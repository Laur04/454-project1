module AssumeAssert (Program) where

import Language(Assertion)

type Var = String

data Statement = Assume Assertion
               | Assert Assertion
               | Havoc Var
               deriving (Show)

type Block = [Statement]

type Program = Block
