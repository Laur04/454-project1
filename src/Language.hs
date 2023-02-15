module Language (Name, ArithExp(..), Comparison(..), BoolExp(..), Statement(..), Block, Program) where

type Name = String

-- | Arithmetic expressions
data ArithExp = Num Int
              | Var Name
              | Read Name ArithExp
              | Add ArithExp ArithExp
              | Sub ArithExp ArithExp
              | Mul ArithExp ArithExp
              | Div ArithExp ArithExp
              | Mod ArithExp ArithExp
              | Parens ArithExp
              deriving (Show)

-- | Comparisons of arithmetic expressions
data Comparison = Eq ArithExp ArithExp
                | Neq ArithExp ArithExp
                | Le ArithExp ArithExp
                | Ge ArithExp ArithExp
                | Lt ArithExp ArithExp
                | Gt ArithExp ArithExp
                deriving (Show)

-- | Boolean expressions 
data BoolExp = BCmp Comparison
             | BNot BoolExp
             | BDisj BoolExp BoolExp
             | BConj BoolExp BoolExp
             | BParens BoolExp
             deriving (Show)

data Assertion = ACmp Comparison
               | ANot Assertion
               | ADisj Assertion Assertion
               | AConj Assertion Assertion
               | Implies Assertion Assertion
               | Forall [Name] Assertion
               | Exists [Name] Assertion
               | AParens Assertion
               deriving (Show)

data Statement = Assign Name ArithExp
               | ParAssign Name Name ArithExp ArithExp
               | Write Name ArithExp ArithExp
               | If BoolExp Block Block
               | While BoolExp [Assertion] Block
               deriving (Show)

type Block = [Statement]

type PreCond = [Assertion]

type PostCond = [Assertion]

type Program = (Name, PreCond, PostCond, Block)

-- data: some information I want to store, has a certain type
-- example type: ArithExp
-- example info to store: a number Num, which takes in an integer Int
-- later, could say let a = Num 2 in ... 
-- then a would have the type ArithExp (a :: ArithExp)
-- these are called algebraic datatypes, because they are a sum of products
-- example: ArithExp could be constructed using the constructor Num which passes in a type Int,
-- or it could be constructed using the constructor Var which passes in a type string
-- so ArithExp = Num Int + Var String + Add ArithExp ArithExp ... 
-- how to deconstruct this information?
-- consider function extract :: ArithExp --> Int
-- extract aexp = ...
-- could also pattern match in the function definition
-- extract (Num i) = i
-- extract (Plus exp1 exp2) = (extract exp1) + (extract exp2)