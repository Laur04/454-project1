module Verify (Result(..), verify) where

import Language
import AssumeAssert
import Parser.Parser
import Control.Monad.State.Lazy
import System.Process
import Data.List



data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify inputProgram = do
  -- putStrLn (show inputProgram ++ "\n") 
  let parsedProgram = parseProg inputProgram
  -- putStrLn (show parsedProgram ++ "\n") 
  let assumeAssertedProgram = driverAA parsedProgram
  -- putStrLn (show assumeAssertedProgram ++ "\n")
  let weakestPreProgram = driverWP assumeAssertedProgram
  -- putStrLn (show weakestPreProgram ++ "\n")
  let smtString = driverSMTLIB weakestPreProgram 
  putStrLn(smtString)
  out <- readProcess "z3" ["-in"] smtString
  putStrLn(out) 
  return (toReturn (head (lines out)))
  -- return Verified

toReturn :: String -> Result
toReturn "unsat" = Verified
toReturn "sat" = NotVerified
toReturn _ = Unknown "Z3 returned unknown"
--------------------------------------------
-- | BEGIN Parser to AssumeAssert Conversion
--------------------------------------------
driverAA :: Language.Program -> AssumeAssert.GCommand
driverAA ( _, pre, body, post ) = Comb (Comb (assumeInvariants pre) (evalState (blockAA body) 0)) (assertInvariants post)

-- Handle preconditions and invariants
assumeInvariants :: [Language.Assertion] -> AssumeAssert.GCommand
assumeInvariants [] = Assume (ACmp (Eq (Num 0) (Num 0)))
assumeInvariants [x] = Assume x
assumeInvariants (x : xs) = Comb (Assume x) (assumeInvariants xs)

-- Handle postconditions and invariants
assertInvariants :: [Language.Assertion] -> AssumeAssert.GCommand
assertInvariants [] = Assume (ACmp (Eq (Num 0) (Num 0)))
assertInvariants [x] = Assert x
assertInvariants (x : xs) = Comb (Assert x) (assertInvariants xs)

-- Handle program block
blockAA :: Language.Block -> State Int AssumeAssert.GCommand
blockAA (xs) = do 
  gcommds <- (mapM (toGCommand) xs)
  return (foldr (AssumeAssert.Comb) (Assume (ACmp (Eq (Num 0) (Num 0)))) gcommds)
  -- (Statement -> State Int Command) -> [Statement] -> State Int [Command]

-- Monad for tmp variables
tmpGen :: State Int String
tmpGen = do 
  n <- get
  put (n + 1)
  return ("AAtmp_" ++ (show n))

-- Main converter to Guarded Command
toGCommand :: Language.Statement -> State Int AssumeAssert.GCommand
toGCommand (Assign x arithexp) = do
  tmp <- tmpGen
  return (Comb (Comb (Assume (ACmp (Eq (Var tmp) (Var x)))) (Havoc x)) (Assume (ACmp (Eq (Var x) (replace x tmp arithexp)))))
toGCommand (ParAssign x1 x2 arithexp1 arithexp2) = do
  tmp1 <- tmpGen
  tmp2 <- tmpGen
  return (Comb (Comb (Comb (Assume (ACmp (Eq (Var tmp1) (Var x1)))) (Havoc x1)) (Assume (ACmp (Eq (Var x1) (replace x1 tmp1 arithexp1))))) (Comb (Comb (Assume (ACmp (Eq (Var tmp2) (Var x2)))) (Havoc x2)) (Assume (ACmp (Eq (Var x2) (replace x2 tmp2 arithexp2))))))
toGCommand (Write name arithexp_index arithexp_value) = do
  tmp <- tmpGen
  return (writeHelper name tmp arithexp_index arithexp_value)
toGCommand (If boolexp block1 block2) = do
  blk1 <- (blockAA block1)
  blk2 <- (blockAA block2)
  return (Box (Comb (Assume (convertBoolExp boolexp)) (blk1)) (Comb (Assume (convertBoolExp (BNot boolexp))) (blk2)))
toGCommand (While boolexp assns block) = do
  blk <- (blockAA block)
  let eleList = getElements block
  let eleSet = rmdups eleList
  return (Comb (Comb (Comb (assertInvariants assns) (whileHelper eleSet)) (assumeInvariants assns)) (Box (Comb (Comb (Comb (Assume (convertBoolExp boolexp)) (blk)) (assertInvariants assns)) (Assume (ACmp (Eq (Num 0) (Num 1))))) (Assume (convertBoolExp (BNot boolexp)))))

-- | Helper functions for While
getElements :: Language.Block -> [String]
getElements [] = []
getElements (x : xs) = (helperStatement x) ++ getElements xs

helperStatement :: Language.Statement -> [String]
helperStatement (Assign name arithexp) = [name] ++ helperArith arithexp
helperStatement (ParAssign name1 name2 arithexp1 arithexp2) = [name1, name2] ++ (helperArith arithexp1) ++ (helperArith arithexp2)
helperStatement (Write name arithexp1 arithexp2) = [name] ++ (helperArith arithexp1) ++ (helperArith arithexp2)
helperStatement (If boolexp block1 block2) = (helperBool boolexp) ++ (getElements block1) ++ (getElements block2)
helperStatement (While boolexp assns block) = (helperBool boolexp) ++ (helperAssertionList assns) ++ (getElements block)

helperArith :: Language.ArithExp -> [String]
helperArith (Num _) = []
helperArith (Var name) = [name]
helperArith (Read name arithexp) = [name] ++ (helperArith arithexp)
helperArith (AWrite name arithexp1 arithexp2) = [name] ++ (helperArith arithexp1) ++ (helperArith arithexp2)
helperArith (Add arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperArith (Sub arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperArith (Mul arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperArith (Div arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperArith (Mod arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperArith (Parens arithexp) = helperArith arithexp

helperComp :: Language.Comparison -> [String]
helperComp (Eq arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperComp (Neq arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperComp (Le arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperComp (Ge arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperComp (Lt arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)
helperComp (Gt arithexp1 arithexp2) = (helperArith arithexp1) ++ (helperArith arithexp2)

helperBool :: Language.BoolExp -> [String]
helperBool (BCmp comp) = helperComp comp
helperBool (BNot boolexp) = helperBool boolexp
helperBool (BDisj boolexp1 boolexp2) = (helperBool boolexp1) ++ (helperBool boolexp2)
helperBool (BConj boolexp1 boolexp2) = (helperBool boolexp1) ++ (helperBool boolexp2)
helperBool (BParens boolexp) = helperBool boolexp

helperNames :: [String] -> [String]
helperNames [] = []
helperNames (x : xs) = [x] ++ (helperNames xs)

helperAssertionList :: [Language.Assertion] -> [String]
helperAssertionList [] = []
helperAssertionList (x : xs) = (helperAssertion x) ++ (helperAssertionList xs)

helperAssertion :: Language.Assertion -> [String]
helperAssertion (ACmp comp) = helperComp comp
helperAssertion (ANot assn) = helperAssertion assn
helperAssertion (ADisj assn1 assn2) = (helperAssertion assn1) ++ (helperAssertion assn2)
helperAssertion (AConj assn1 assn2) = (helperAssertion assn1) ++ (helperAssertion assn2)
helperAssertion (Implies assn1 assn2) = (helperAssertion assn1) ++ (helperAssertion assn2)
helperAssertion (Forall names assn) = helperNames names ++ (helperAssertion assn)
helperAssertion (Exists names assn) = helperNames names ++ (helperAssertion assn)
helperAssertion (AParens assn) = helperAssertion assn



-- rmdups :: [String] -> [String]
-- rmdups [] = []
-- rmdups (x:xs)   | x `elem` xs   = rmdups xs
                -- | otherwise     = x : rmdups xs

rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort

whileHelper :: [String]-> AssumeAssert.GCommand
whileHelper [] = Assume (ACmp (Eq (Num 0) (Num 0)))
whileHelper [x] = Havoc x
whileHelper (x : xs) = Comb (Havoc x) (whileHelper xs)

-- | Helper functions for Assign, ParAssign
replace :: String -> String -> Language.ArithExp -> Language.ArithExp
replace _ _ (Num i) = Num i
replace x tmp (Var name) = if x == name then Var tmp else Var name
replace x tmp (AWrite name arithexp1 arithexp2) = if x == name then AWrite tmp (replace x tmp arithexp1) (replace x tmp arithexp2) else AWrite name (replace x tmp arithexp1) (replace x tmp arithexp2)
replace x tmp (Read name arithexp) = if x == name then Read tmp (replace x tmp arithexp) else Read name (replace x tmp arithexp)
replace x tmp (Add arithexp1 arithexp2) = Add (replace x tmp arithexp1) (replace x tmp arithexp2)
replace x tmp (Sub arithexp1 arithexp2) = Sub (replace x tmp arithexp1) (replace x tmp arithexp2)
replace x tmp (Mul arithexp1 arithexp2) = Mul (replace x tmp arithexp1) (replace x tmp arithexp2)
replace x tmp (Div arithexp1 arithexp2) = Div (replace x tmp arithexp1) (replace x tmp arithexp2)
replace x tmp (Mod arithexp1 arithexp2) = Mod (replace x tmp arithexp1) (replace x tmp arithexp2)
replace x tmp (Parens arithexp) = Parens (replace x tmp arithexp)

-- | Helper function for Write
writeHelper :: String -> String -> Language.ArithExp -> Language.ArithExp -> AssumeAssert.GCommand
writeHelper x tmp index value = Comb (Comb (Assume (ACmp (Eq (Var tmp) (Var x)))) (Havoc x)) (Assume (ACmp (Eq (Var x) (AWrite tmp index value ))))

-- | Helper functions for If, While
convertBoolExp :: Language.BoolExp -> Language.Assertion
convertBoolExp (BCmp comp) = ACmp comp
convertBoolExp (BNot boolexp) = ANot (convertBoolExp boolexp)
convertBoolExp (BDisj boolexp1 boolexp2) = ADisj (convertBoolExp boolexp1) (convertBoolExp boolexp2)
convertBoolExp (BConj boolexp1 boolexp2) = AConj (convertBoolExp boolexp1) (convertBoolExp boolexp2)
convertBoolExp (BParens boolexp) = AParens (convertBoolExp boolexp)
--------------------------------------------
-- | END Parser to AssumeAssert Conversion
--------------------------------------------


--------------------------------------------
-- | BEGIN AssumeAssert to VC Conversion
--------------------------------------------
driverWP :: AssumeAssert.GCommand -> Language.Assertion
driverWP gc = evalState (toVC gc (ACmp (Eq (Num 0) (Num 0)))) 0

-- Monad for fresh tmp variables
tmpGen2 :: State Int String
tmpGen2 = do 
  n <- get
  put (n + 1)
  return ("VCtmp__" ++ show n)

toVC :: AssumeAssert.GCommand -> Language.Assertion -> State Int Language.Assertion
toVC (Assume b) c = do
  return (Implies b c)
toVC (Assert b) c = do
  return (AConj b c)
toVC (Havoc var) c = do
  tmp <- tmpGen2
  return (fresh var tmp c)
toVC (Comb gc1 gc2) c = do
  blk <- (toVC gc2 c)
  blk2 <- (toVC gc1 blk)
  return (blk2)
toVC (Box gc1 gc2) c = do
  blk1 <- (toVC gc1 c)
  blk2 <- (toVC gc2 c)
  return (AConj (blk1) (blk2))

fresh :: String -> String -> Language.Assertion -> Language.Assertion
fresh x tmp (ACmp comp) = ACmp (freshCompHelper x tmp comp)
fresh x tmp (ANot c) = ANot (fresh x tmp c)
fresh x tmp (ADisj c1 c2) = ADisj (fresh x tmp c1) (fresh x tmp c2)
fresh x tmp (AConj c1 c2) = AConj (fresh x tmp c1) (fresh x tmp c2)
fresh x tmp (Implies c1 c2) = Implies (fresh x tmp c1) (fresh x tmp c2)
fresh x tmp (Forall names c) = Forall (freshNameHelper x tmp names) (fresh x tmp c)
fresh x tmp (Exists names c) = Exists (freshNameHelper x tmp names) (fresh x tmp c)
fresh x tmp (AParens c) = AParens (fresh x tmp c)

freshNameHelper :: String -> String -> [String] -> [String]
freshNameHelper _ _ [] = []
freshNameHelper var tmp [x] = if x == var then [tmp] else [x]
freshNameHelper var tmp (x : xs) = if x == var then [tmp] ++ (freshNameHelper var tmp xs) else [var] ++ (freshNameHelper var tmp xs)

freshCompHelper :: String -> String -> Language.Comparison -> Language.Comparison
freshCompHelper x tmp (Eq arithexp1 arithexp2) = Eq (replace x tmp arithexp1) (replace x tmp arithexp2)
freshCompHelper x tmp (Neq arithexp1 arithexp2) = Neq (replace x tmp arithexp1) (replace x tmp arithexp2)
freshCompHelper x tmp (Le arithexp1 arithexp2) = Le (replace x tmp arithexp1) (replace x tmp arithexp2)
freshCompHelper x tmp (Ge arithexp1 arithexp2) = Ge (replace x tmp arithexp1) (replace x tmp arithexp2)
freshCompHelper x tmp (Lt arithexp1 arithexp2) = Lt (replace x tmp arithexp1) (replace x tmp arithexp2)
freshCompHelper x tmp (Gt arithexp1 arithexp2) = Gt (replace x tmp arithexp1) (replace x tmp arithexp2)
--------------------------------------------
-- | END AssumeAssert to VC Conversion
--------------------------------------------



--------------------------------------------
-- | BEGIN VC to SMT LIB Conversion 
--------------------------------------------
driverSMTLIB :: Language.Assertion -> String
driverSMTLIB vc = setLogic ++ declareFuns (rmdups (getIVarAssertion vc)) ++ declareArrVars (rmdups (getArrVarAssertion vc)) ++ "(assert (not " ++ toSMTLIB vc ++ "))" ++ "\n" ++"(check-sat)"
-- driverSMTLIB vc = setLogic ++ declareFuns (rmdups (helperAssertion vc)) ++ "(assert (not " ++ toSMTLIB vc ++ "))" ++ "\n" ++"(check-sat)"
  
setLogic :: String
setLogic = "(set-logic QF_AUFNIA)" ++ "\n"

-- this needs work for array names and shit
declareFuns :: [String] -> String 
declareFuns [] = []
declareFuns (x:xs) = "(declare-fun " ++ x ++ " () Int)"++ "\n" ++ declareFuns xs

declareArrVars :: [String] -> String 
declareArrVars [] = []
declareArrVars (x:xs) = "(declare-fun " ++ x ++ " () (Array Int Int))"++ "\n" ++ declareArrVars xs

-- NOTE: Helper Assertion returns the var names from a big assertion

toSMTLIB :: Language.Assertion -> String
toSMTLIB (ACmp comp) = toSMTLIBComp comp
toSMTLIB (ANot c) = "(not " ++ toSMTLIB c ++ ")"
toSMTLIB (ADisj c1 c2) = "(or " ++ toSMTLIB c1 ++ " " ++ toSMTLIB c2 ++ ")"
toSMTLIB (AConj c1 c2) = "(and " ++ toSMTLIB c1 ++ " " ++ toSMTLIB c2 ++ ")"
toSMTLIB (Implies c1 c2) = "(=> " ++ toSMTLIB c1 ++ " " ++ toSMTLIB c2 ++ ")"
toSMTLIB (Forall names c) = "(forall (" ++ toSMTLIBNames names ++ ")" ++ toSMTLIB c ++ ")"
toSMTLIB (Exists names c) = "(exists (" ++ toSMTLIBNames names ++ ")" ++ toSMTLIB c ++ ")"
toSMTLIB (AParens c) = toSMTLIB c
-- toSMTLIB (AParens c) = "(TEST " ++ toSMTLIB c ++ ")"

-- assertSMTParens :: Language.Assertion -> String
-- assertSMTParens (ACmp comp) = toSMTLIBComp comp

toSMTLIBNames :: [String] -> String
toSMTLIBNames [] = []
toSMTLIBNames (x:xs) = "(" ++ x ++ " Int) " ++ toSMTLIBNames xs

toSMTLIBComp :: Language.Comparison -> String
toSMTLIBComp (Eq arithexp1 arithexp2) = "(= " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBComp (Neq arithexp1 arithexp2) = "(not (= " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ "))"
toSMTLIBComp (Le arithexp1 arithexp2) = "(<= " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBComp (Ge arithexp1 arithexp2) = "(>= " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBComp (Lt arithexp1 arithexp2) = "(< " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBComp (Gt arithexp1 arithexp2) = "(> " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"

toSMTLIBArith :: Language.ArithExp -> String
toSMTLIBArith (Num n) = show n
toSMTLIBArith (Var x) = x
toSMTLIBArith (Read x arithexp) = "(select " ++ x ++ " " ++ toSMTLIBArith arithexp ++ ")"
toSMTLIBArith (AWrite x arithexp1 arithexp2) = "(store " ++ x ++ " " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBArith (Add arithexp1 arithexp2) = "(+ " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBArith (Sub arithexp1 arithexp2) = "(- " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBArith (Mul arithexp1 arithexp2) = "(* " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBArith (Div arithexp1 arithexp2) = "(div " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBArith (Mod arithexp1 arithexp2) = "(mod " ++ toSMTLIBArith arithexp1 ++ " " ++ toSMTLIBArith arithexp2 ++ ")"
toSMTLIBArith (Parens arithexp) = toSMTLIBArith arithexp
--------------------------------------------


--------------------------------------------
-- | Integer Vars for declaration at top of SMTLIB String
--------------------------------------------

getIVarArith :: Language.ArithExp -> [String]
getIVarArith (Num _) = []
getIVarArith (Var name) = [name]
getIVarArith (Read _ arithexp) = getIVarArith arithexp
getIVarArith (AWrite _ arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarArith (Add arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarArith (Sub arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarArith (Mul arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarArith (Div arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarArith (Mod arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarArith (Parens arithexp) = getIVarArith arithexp

getIVarComp :: Language.Comparison -> [String]
getIVarComp (Eq (AWrite _ _ _) (AWrite _ _ _)) = []
getIVarComp (Eq (Read _ _) (Read _ _)) = []
getIVarComp (Eq (AWrite _ _ _) (Read _ _)) = []
getIVarComp (Eq (Read _ _) (AWrite _ _ _)) = []
getIVarComp (Eq (AWrite _ _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Eq arithexp1 (AWrite _ _ _)) = (getIVarArith arithexp1)
getIVarComp (Eq (Read _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Eq arithexp1 (Read _ _)) = (getIVarArith arithexp1)
getIVarComp (Eq arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarComp (Neq (AWrite _ _ _) (AWrite _ _ _)) = []
getIVarComp (Neq (Read _ _) (Read _ _)) = []
getIVarComp (Neq (AWrite _ _ _) (Read _ _)) = []
getIVarComp (Neq (Read _ _) (AWrite _ _ _)) = []
getIVarComp (Neq (AWrite _ _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Neq arithexp1 (AWrite _ _ _)) = (getIVarArith arithexp1)
getIVarComp (Neq (Read _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Neq arithexp1 (Read _ _)) = (getIVarArith arithexp1)
getIVarComp (Neq arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarComp (Le (AWrite _ _ _) (AWrite _ _ _)) = []
getIVarComp (Le (Read _ _) (Read _ _)) = []
getIVarComp (Le (AWrite _ _ _) (Read _ _)) = []
getIVarComp (Le (Read _ _) (AWrite _ _ _)) = []
getIVarComp (Le (AWrite _ _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Le arithexp1 (AWrite _ _ _)) = (getIVarArith arithexp1)
getIVarComp (Le (Read _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Le arithexp1 (Read _ _)) = (getIVarArith arithexp1)
getIVarComp (Le arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarComp (Ge (AWrite _ _ _) (AWrite _ _ _)) = []
getIVarComp (Ge (Read _ _) (Read _ _)) = []
getIVarComp (Ge (AWrite _ _ _) (Read _ _)) = []
getIVarComp (Ge (Read _ _) (AWrite _ _ _)) = []
getIVarComp (Ge (AWrite _ _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Ge arithexp1 (AWrite _ _ _)) = (getIVarArith arithexp1)
getIVarComp (Ge (Read _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Ge arithexp1 (Read _ _)) = (getIVarArith arithexp1)
getIVarComp (Ge arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarComp (Gt (AWrite _ _ _) (AWrite _ _ _)) = []
getIVarComp (Gt (Read _ _) (Read _ _)) = []
getIVarComp (Gt (AWrite _ _ _) (Read _ _)) = []
getIVarComp (Gt (Read _ _) (AWrite _ _ _)) = []
getIVarComp (Gt (AWrite _ _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Gt arithexp1 (AWrite _ _ _)) = (getIVarArith arithexp1)
getIVarComp (Gt (Read _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Gt arithexp1 (Read _ _)) = (getIVarArith arithexp1)
getIVarComp (Gt arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)
getIVarComp (Lt (AWrite _ _ _) (AWrite _ _ _)) = []
getIVarComp (Lt (Read _ _) (Read _ _)) = []
getIVarComp (Lt (AWrite _ _ _) (Read _ _)) = []
getIVarComp (Lt (Read _ _) (AWrite _ _ _)) = []
getIVarComp (Lt (AWrite _ _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Lt arithexp1 (AWrite _ _ _)) = (getIVarArith arithexp1)
getIVarComp (Lt (Read _ _) arithexp2) = (getIVarArith arithexp2)
getIVarComp (Lt arithexp1 (Read _ _)) = (getIVarArith arithexp1)
getIVarComp (Lt arithexp1 arithexp2) = (getIVarArith arithexp1) ++ (getIVarArith arithexp2)

getIVarNames :: [String] -> [String]
getIVarNames [] = []
getIVarNames (x : xs) = [x] ++ (getIVarNames xs)

getIVarAssertion :: Language.Assertion -> [String]
getIVarAssertion (ACmp comp) = getIVarComp comp
getIVarAssertion (ANot assn) = getIVarAssertion assn
getIVarAssertion (ADisj assn1 assn2) = (getIVarAssertion assn1) ++ (getIVarAssertion assn2)
getIVarAssertion (AConj assn1 assn2) = (getIVarAssertion assn1) ++ (getIVarAssertion assn2)
getIVarAssertion (Implies assn1 assn2) = (getIVarAssertion assn1) ++ (getIVarAssertion assn2)
getIVarAssertion (Forall names assn) = getIVarNames names ++ (getIVarAssertion assn)
getIVarAssertion (Exists names assn) = getIVarNames names ++ (getIVarAssertion assn)
getIVarAssertion (AParens assn) = getIVarAssertion assn

----------------------------------------------------------------------------------------
-- | Array Vars for declaration at top of SMTLIB String
----------------------------------------------------------------------------------------
getArrVarArith :: Language.ArithExp -> [String]
getArrVarArith (Num _) = []
getArrVarArith (Var _) = []
getArrVarArith (Read name arithexp) = [name] ++ (getArrVarArith arithexp)
getArrVarArith (AWrite name arithexp1 arithexp2) = [name] ++ (getArrVarArith arithexp1) ++ (getArrVarArith arithexp2)
getArrVarArith (Add arithexp1 arithexp2) = (getArrVarArith arithexp1) ++ (getArrVarArith arithexp2)
getArrVarArith (Sub arithexp1 arithexp2) = (getArrVarArith arithexp1) ++ (getArrVarArith arithexp2)
getArrVarArith (Mul arithexp1 arithexp2) = (getArrVarArith arithexp1) ++ (getArrVarArith arithexp2)
getArrVarArith (Div arithexp1 arithexp2) = (getArrVarArith arithexp1) ++ (getArrVarArith arithexp2)
getArrVarArith (Mod arithexp1 arithexp2) = (getArrVarArith arithexp1) ++ (getArrVarArith arithexp2)
getArrVarArith (Parens arithexp) = getArrVarArith arithexp

getArrVarComp :: Language.Comparison -> [String]
getArrVarComp (Eq (AWrite a b c) (AWrite d e f)) = (getArrVarArith (AWrite a b c)) ++ (getArrVarArith (AWrite d e f))
getArrVarComp (Eq (Read a b) (Read c d)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (Read c d))
getArrVarComp (Eq (AWrite x y z) (Read c d)) = (getArrVarArith (AWrite x y z)) ++ (getArrVarArith (Read c d))
getArrVarComp (Eq (Read a b) (AWrite x y z)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (AWrite x y z))
getArrVarComp (Eq (AWrite a b c) _) = (getArrVarArith (AWrite a b c))
getArrVarComp (Eq _ (AWrite a b c)) = (getArrVarArith (AWrite a b c))
getArrVarComp (Eq (Read a b) _) = (getArrVarArith (Read a b))
getArrVarComp (Eq _ (Read a b)) = (getArrVarArith (Read a b))
getArrVarComp (Eq _ _) = []
getArrVarComp (Neq (AWrite a b c) (AWrite d e f)) = (getArrVarArith (AWrite a b c)) ++ (getArrVarArith (AWrite d e f))
getArrVarComp (Neq (Read a b) (Read c d)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (Read c d))
getArrVarComp (Neq (AWrite x y z) (Read c d)) = (getArrVarArith (AWrite x y z)) ++ (getArrVarArith (Read c d))
getArrVarComp (Neq (Read a b) (AWrite x y z)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (AWrite x y z))
getArrVarComp (Neq (AWrite a b c) _) = (getArrVarArith (AWrite a b c))
getArrVarComp (Neq _ (AWrite a b c)) = (getArrVarArith (AWrite a b c))
getArrVarComp (Neq (Read a b) _) = (getArrVarArith (Read a b))
getArrVarComp (Neq _ (Read a b)) = (getArrVarArith (Read a b))
getArrVarComp (Neq _ _) = []
getArrVarComp (Lt (AWrite a b c) (AWrite d e f)) = (getArrVarArith (AWrite a b c)) ++ (getArrVarArith (AWrite d e f))
getArrVarComp (Lt (Read a b) (Read c d)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (Read c d))
getArrVarComp (Lt (AWrite x y z) (Read c d)) = (getArrVarArith (AWrite x y z)) ++ (getArrVarArith (Read c d))
getArrVarComp (Lt (Read a b) (AWrite x y z)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (AWrite x y z))
getArrVarComp (Lt (AWrite a b c) _) = (getArrVarArith (AWrite a b c))
getArrVarComp (Lt _ (AWrite a b c)) = (getArrVarArith (AWrite a b c))
getArrVarComp (Lt (Read a b) _) = (getArrVarArith (Read a b))
getArrVarComp (Lt _ (Read a b)) = (getArrVarArith (Read a b))
getArrVarComp (Lt _ _) = []
getArrVarComp (Gt (AWrite a b c) (AWrite d e f)) = (getArrVarArith (AWrite a b c)) ++ (getArrVarArith (AWrite d e f))
getArrVarComp (Gt (Read a b) (Read c d)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (Read c d))
getArrVarComp (Gt (AWrite x y z) (Read c d)) = (getArrVarArith (AWrite x y z)) ++ (getArrVarArith (Read c d))
getArrVarComp (Gt (Read a b) (AWrite x y z)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (AWrite x y z))
getArrVarComp (Gt (AWrite a b c) _) = (getArrVarArith (AWrite a b c))
getArrVarComp (Gt _ (AWrite a b c)) = (getArrVarArith (AWrite a b c))
getArrVarComp (Gt (Read a b) _) = (getArrVarArith (Read a b))
getArrVarComp (Gt _ (Read a b)) = (getArrVarArith (Read a b))
getArrVarComp (Gt _ _) = []
getArrVarComp (Le (AWrite a b c) (AWrite d e f)) = (getArrVarArith (AWrite a b c)) ++ (getArrVarArith (AWrite d e f))
getArrVarComp (Le (Read a b) (Read c d)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (Read c d))
getArrVarComp (Le (AWrite x y z) (Read c d)) = (getArrVarArith (AWrite x y z)) ++ (getArrVarArith (Read c d))
getArrVarComp (Le (Read a b) (AWrite x y z)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (AWrite x y z))
getArrVarComp (Le (AWrite a b c) _) = (getArrVarArith (AWrite a b c))
getArrVarComp (Le _ (AWrite a b c)) = (getArrVarArith (AWrite a b c))
getArrVarComp (Le (Read a b) _) = (getArrVarArith (Read a b))
getArrVarComp (Le _ (Read a b)) = (getArrVarArith (Read a b))
getArrVarComp (Le _ _) = []
getArrVarComp (Ge (AWrite a b c) (AWrite d e f)) = (getArrVarArith (AWrite a b c)) ++ (getArrVarArith (AWrite d e f))
getArrVarComp (Ge (Read a b) (Read c d)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (Read c d))
getArrVarComp (Ge (AWrite x y z) (Read c d)) = (getArrVarArith (AWrite x y z)) ++ (getArrVarArith (Read c d))
getArrVarComp (Ge (Read a b) (AWrite x y z)) = (getArrVarArith (Read a b)) ++ (getArrVarArith (AWrite x y z))
getArrVarComp (Ge (AWrite a b c) _) = (getArrVarArith (AWrite a b c))
getArrVarComp (Ge _ (AWrite a b c)) = (getArrVarArith (AWrite a b c))
getArrVarComp (Ge (Read a b) _) = (getArrVarArith (Read a b))
getArrVarComp (Ge _ (Read a b)) = (getArrVarArith (Read a b))
getArrVarComp (Ge _ _) = []

getArrVarNames :: [String] -> [String]
getArrVarNames [] = []
getArrVarNames (x : xs) = [x] ++ (getArrVarNames xs)

getArrVarAssertion :: Language.Assertion -> [String]
getArrVarAssertion (ACmp comp) = getArrVarComp comp
getArrVarAssertion (ANot assn) = getArrVarAssertion assn
getArrVarAssertion (ADisj assn1 assn2) = (getArrVarAssertion assn1) ++ (getArrVarAssertion assn2)
getArrVarAssertion (AConj assn1 assn2) = (getArrVarAssertion assn1) ++ (getArrVarAssertion assn2)
getArrVarAssertion (Implies assn1 assn2) = (getArrVarAssertion assn1) ++ (getArrVarAssertion assn2)
getArrVarAssertion (Forall names assn) = getArrVarNames names ++ (getArrVarAssertion assn)
getArrVarAssertion (Exists names assn) = getArrVarNames names ++ (getArrVarAssertion assn)
getArrVarAssertion (AParens assn) = getArrVarAssertion assn