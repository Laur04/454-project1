module Verify (Result(..), verify) where

import Language
import AssumeAssert
import Parser.Parser

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify inputProgram = do
  let parsedProgram = parseProg inputProgram
  let assumeAssertedProgram = driverAA parsedProgram
  let weakestPreProgram = driverWP assumeAssertedProgram

  -- TODO: verify with SMT solver

  return Verified

-- | BEGIN Parser to AssumeAssert Conversion

driverAA :: Language.Program -> AssumeAssert.GCommand
driverAA ( name, pre, body, post ) = Comb (Comb (assumeInvariants pre) (blockAA body)) (assertInvariants post)

-- Handle preconditions and invariants
assumeInvariants :: [Language.Assertion] -> AssumeAssert.GCommand
assumeInvariants (x) = Assume x
assumeInvariants (x : xs) = Comb (Assume x) (assumeInvariants xs)

-- Handle postconditions and invariants
assertInvariants :: [Language.Assertion] -> AssumeAssert.GCommand
assertInvariants (x) = Assert x
assertInvariants (x : xs) = Comb (Assert x) (assertInvariants xs)

-- Handle program block
blockAA :: Language.Block -> AssumeAssert.GCommand
blockAA [] = Assume (ACmp (Eq (Int 0) (Int 0))) -- assume true
blockAA (x) = toGCommand x
blockAA (x : xs) = Comb (toGCommand x) (blockAA xs)

-- Monad for tmp variables
tmp :: State Int String
tmp = do n <- get
        put (n + 1)
        return "tmp_" ++ (show n)

-- Main converter to Guarded Command
toGCommand :: Language.Statement -> AssumeAssert.GCommand
toGCommand ( Assign name arithexp ) = assignHelper name (execState tmp) arithexp
blockAAHelper ( ParAssign name1 name2 arithexp2 arithexp1 ) = Comb (assignHelper name1 (execState tmp) arithexp1) (assignHelper name2 (execState tmp) arithexp2)
blockAAHelper ( Write name arithexp_index arithexp_value ) = writeHelper name (execState tmp) arithexp_index arithexp_value
blockAAHelper ( If boolexp block1 block2 ) = Box (Comb (Assume (convertBoolExp boolexp)) (blockAA block1)) (Comb (Assume (convertBoolExp (BNot boolexp))) (blockAA block2))
blockAAHelper ( While boolexp assns block ) = Comb (Comb (Comb (assertInvariants assns) (DO HAVOC HERE)) (assumeInvariants assns)) (Box (Comb (Comb (Comb (Assume (convertBoolExp boolexp)) (blockAA block)) (assertInvariants assns)) (Assume (ACmp (Eq (Num 0) (Num 1))))) (Assume (convertBoolExp (BNot boolexp))))

-- | Helper functions for Assign, ParAssign
assignHelper :: String -> String -> Language.ArithExp -> AssumeAssert.GCommand
assignHelper (x tmp arithexp) = Comb (Comb (Assume (ACmp (Eq (Var tmp) (Var x)))) (Havoc x)) (Assume (ACmp (Eq (Var x) (replace x tmp arithexp))))

replace :: String -> String -> Language.ArithExp -> Language.ArithExp
replace (x tmp (Num i)) = Num i
replace (x tmp (Var name)) = if x == name then Var tmp else Var name
replace (x tmp (Read name arithexp)) = if x == name then Read tmp (replace x tmp arithexp) else Read name (replace x tmp arithexp)
replace (x tmp (Add arithexp1 arithexp2)) = Add (replace x tmp arithexp1) (replace x tmp arithexp2)
replace (x tmp (Sub arithexp1 arithexp2)) = Sub (replace x tmp arithexp1) (replace x tmp arithexp2)
replace (x tmp (Mul arithexp1 arithexp2)) = Mul (replace x tmp arithexp1) (replace x tmp arithexp2)
replace (x tmp (Div arithexp1 arithexp2)) = Div (replace x tmp arithexp1) (replace x tmp arithexp2)
replace (x tmp (Mod arithexp1 arithexp2)) = Mod (replace x tmp arithexp1) (replace x tmp arithexp2)
replace (x tmp (Parens arithexp)) = Parens (replace x tmp arithexp)

-- | Helper function for Write
writeHelper :: String -> String -> Language.ArithExp -> Language.ArithExp -> AssumeAssert.GCommand
writeHelper (x tmp index value) = Comb (Comb (Assume (ACmp (Eq (Var tmp) (Var x)))) (Havoc x)) (Assume (ACmp (Eq (Var x) (Write tmp index value ))))

-- | Helper functions for If, While
convertBoolExp :: Language.BoolExp -> Language.Assertion
convertBoolExp (BCmp comp) = ACmp comp
convertBoolExp (BNot boolexp) = ANot (convertBoolExp boolexp)
convertBoolExp (BDisj boolexp) = BDisj (convertBoolExp boolexp)
convertBoolExp (BConj boolexp) = BConj (convertBoolExp boolexp)
convertBoolExp (BParens boolexp) = BParens (convertBoolExp boolexp)

-- | END Parser to AssumeAssert Conversion


-- | BEGIN AssumeAssert to VC Conversion

driverWP :: AssumeAssert.GCommand -> Language.Assertion
driverWP gc = toVC gc (ACmp (Eq (Int 0) (Int 0)))

toVC :: AssumeAssert.GCommand -> Language.Assertion -> Language.Assertion
toVC ((Assume b) B) = Implies b B
toVC ((Assert b) B) = AConj b B
toVC ((Havoc var) B) = fresh var (execState tmp) B
toVC ((Comb gc1 gc2) B) = toVC gc1 (toVC gc2 B)
toVC ((Box gc1 gc2) assn) = AConj (toVC gc1 B) (toVC gc2 B)

fresh :: String -> String -> Language.Assertion -> Language.Assertion
fresh (x tmp (ACmp comp)) = ACmp (freshCompHelper x tmp comp)
fresh (x tmp (ANot B)) = ANot (fresh x tmp B)
fresh (x tmp (ADisj B1 B2)) = ADisj (fresh x tmp B1) (fresh x tmp B2)
fresh (x tmp (AConj B1 B2)) = AConj (fresh x tmp B1) (fresh x tmp B2)
fresh (x tmp (Implies B1 B2)) = Implies (fresh x tmp B1) (fresh x tmp B2)
fresh (x tmp (Forall names B)) = Forall (freshNameHelper x tmp names) (fresh x tmp B)
fresh (x tmp (Exists names B)) = Exists (freshNameHelper x tmp names) (fresh x tmp B)
fresh (x tmp (AParens B)) = AParens (fresh x tmp B)

freshNameHelper :: String -> String -> [String] -> [String]
freshNameHelper var tmp [] = []
freshNameHelper var tmp (x : xs) = if x == var then tmp ++ (freshNameHelper var tmp xs) else var ++ (freshNameHelper var tmp xs)

freshCompHelper :: String -> String -> Language.Comparison -> Language.Comparison
freshNameHelper (x tmp (Eq arithexp1 arithexp2)) = Eq (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper (x tmp (Neq arithexp1 arithexp2)) = Neq (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper (x tmp (Le arithexp1 arithexp2)) = Le (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper (x tmp (Ge arithexp1 arithexp2)) = Ge (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper (x tmp (Lt arithexp1 arithexp2)) = Lt (replace x tmp arithexp1) (replace x tmp arithexp2)
freshNameHelper (x tmp (Gt arithexp1 arithexp2)) = Gt (replace x tmp arithexp1) (replace x tmp arithexp2)

-- | END AssumeAssert to VC Conversion
