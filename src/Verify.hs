module Verify (Result(..), verify) where

import Language
import AssumeAssert
import Parser.Parser
import Control.Monad.State.Lazy
import System.Process


data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify inputProgram = do
  let parsedProgram = parseProg inputProgram
  let assumeAssertedProgram = driverAA parsedProgram
  let weakestPreProgram = driverWP assumeAssertedProgram
  putStrLn (show weakestPreProgram ++ "\n")
  let smtString = driverSMTLIB weakestPreProgram 
  putStrLn (show smtString ++ "\n")
  out <- readProcess ["z3", "file"] smtString
  return Verified

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
  return ("tmp_" ++ (show n))

-- Main converter to Guarded Command
toGCommand :: Language.Statement -> State Int AssumeAssert.GCommand
toGCommand (Assign x arithexp) = do
  tmp <- tmpGen
  return (Comb (Comb (Assume (ACmp (Eq (Var tmp) (Var x)))) (Havoc x)) (Assume (ACmp (Eq (Var x) (replace x tmp arithexp)))))
toGCommand (ParAssign x1 x2 arithexp2 arithexp1) = do
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

helperAssertionList :: [Language.Assertion] -> [String]
helperAssertionList [] = []
helperAssertionList (x : xs) = (helperAssertion x) ++ (helperAssertionList xs)

helperAssertion :: Language.Assertion -> [String]
helperAssertion (ACmp comp) = helperComp comp
helperAssertion (ANot assn) = helperAssertion assn
helperAssertion (ADisj assn1 assn2) = (helperAssertion assn1) ++ (helperAssertion assn2)
helperAssertion (AConj assn1 assn2) = (helperAssertion assn1) ++ (helperAssertion assn2)
helperAssertion (Implies assn1 assn2) = (helperAssertion assn1) ++ (helperAssertion assn2)
helperAssertion (Forall names assn) = names ++ (helperAssertion assn)
helperAssertion (Exists names assn) = names ++ (helperAssertion assn)
helperAssertion (AParens assn) = helperAssertion assn

rmdups :: [String] -> [String]
rmdups [] = []
rmdups (x:xs)   | x `elem` xs   = rmdups xs
                | otherwise     = x : rmdups xs

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
  return (show n ++ "_tmp")

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
driverSMTLIB vc = setLogic ++ declareFuns (helperAssertion vc) ++ "(assert" ++ toSMTLIB vc ++ ")\n(check-sat)\n"
  
setLogic :: String
setLogic = "(set-logic QF_AUFBV)\n"

-- this needs work for array names and shit
declareFuns :: [String] -> String 
declareFuns [] = []
declareFuns (x:xs) = "(declare-fun " ++ x ++ " () Int) \n" ++ declareFuns xs

-- NOTE: Helper Assertion returns the var names from a big assertion

toSMTLIB :: Language.Assertion -> String
toSMTLIB (ACmp comp) = toSMTLIBComp comp
toSMTLIB (ANot c) = "(not " ++ toSMTLIB c ++ ")"
toSMTLIB (ADisj c1 c2) = "(or " ++ toSMTLIB c1 ++ " " ++ toSMTLIB c2 ++ ")"
toSMTLIB (AConj c1 c2) = "(and " ++ toSMTLIB c1 ++ " " ++ toSMTLIB c2 ++ ")"
toSMTLIB (Implies c1 c2) = "(=> " ++ toSMTLIB c1 ++ " " ++ toSMTLIB c2 ++ ")"
toSMTLIB (Forall names c) = "(forall (" ++ toSMTLIBNames names ++ ") " ++ toSMTLIB c ++ ")"
toSMTLIB (Exists names c) = "(exists (" ++ toSMTLIBNames names ++ ") " ++ toSMTLIB c ++ ")"
toSMTLIB (AParens c) = "(" ++ toSMTLIB c ++ ")"

toSMTLIBNames :: [String] -> String
toSMTLIBNames [] = []
toSMTLIBNames (x:xs) = "(" ++ x ++ " Int)" ++ toSMTLIBNames xs

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
toSMTLIBArith (Parens arithexp) = "(" ++ toSMTLIBArith arithexp ++ ")"
--------------------------------------------