module Verify (Result(..), verify) where

import Language
import AssumeAssert
import Parser.Parser
import Control.Monad.State.Lazy

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify inputProgram = do
  let parsedProgram = parseProg inputProgram
  let assumeAssertedProgram = driverAA parsedProgram
  let weakestPreProgram = driverWP assumeAssertedProgram
  putStrLn (show weakestPreProgram)

  -- TODO: verify with SMT solver

  return Verified

-- | BEGIN Parser to AssumeAssert Conversion

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

-- | END Parser to AssumeAssert Conversion


-- | BEGIN AssumeAssert to VC Conversion

driverWP :: AssumeAssert.GCommand -> Language.Assertion
driverWP gc = toVC gc (ACmp (Eq (Num 0) (Num 0)))

toVC :: AssumeAssert.GCommand -> Language.Assertion -> Language.Assertion
toVC (Assume b) B = Implies b B
toVC (Assert b) B = AConj b B
toVC (Havoc var) B = fresh var (execState tmp) B
toVC (Comb gc1 gc2) B = toVC gc1 (toVC gc2 B)
toVC (Box gc1 gc2) assn = AConj (toVC gc1 B) (toVC gc2 B)

fresh :: String -> String -> Language.Assertion -> Language.Assertion
fresh x tmp (ACmp comp) = ACmp (freshCompHelper x tmp comp)
fresh x tmp (ANot B) = ANot (fresh x tmp B)
fresh x tmp (ADisj B1 B2) = ADisj (fresh x tmp B1) (fresh x tmp B2)
fresh x tmp (AConj B1 B2) = AConj (fresh x tmp B1) (fresh x tmp B2)
fresh x tmp (Implies B1 B2) = Implies (fresh x tmp B1) (fresh x tmp B2)
fresh x tmp (Forall names B) = Forall (freshNameHelper x tmp names) (fresh x tmp B)
fresh x tmp (Exists names B) = Exists (freshNameHelper x tmp names) (fresh x tmp B)
fresh x tmp (AParens B) = AParens (fresh x tmp B)

freshNameHelper :: String -> String -> [String] -> [String]
freshNameHelper var tmp [] = []
freshNameHelper var tmp (x : xs) = if x == var then tmp ++ (freshNameHelper var tmp xs) else var ++ (freshNameHelper var tmp xs)

freshCompHelper :: String -> String -> Language.Comparison -> Language.Comparison
freshNameHelper x tmp (Eq arithexp1 arithexp2) = Eq (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper x tmp (Neq arithexp1 arithexp2) = Neq (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper x tmp (Le arithexp1 arithexp2) = Le (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper x tmp (Ge arithexp1 arithexp2) = Ge (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper x tmp (Lt arithexp1 arithexp2) = Lt (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper x tmp (Gt arithexp1 arithexp2) = Gt (replace x tmp arithexp1) (replace x tmp arithexp2)

-- | END AssumeAssert to VC Conversion
