module AssumeAssert (Program) where

import Language(Assertion)

type Var = String

data Formula = Exp Assertion
             | Assign Var Formula

data Statement = Assume Formula
               | Assert Formula
               | Havoc Var
               | Parens Block
               deriving (Show)

type Block = [Statement]

type Program = Block
