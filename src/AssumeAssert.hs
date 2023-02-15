module AssumeAssert (Assume(..), Assert(..), Havoc(..)) where

import Language

type Var = String

data Formula = Exp Assertion
             | Assign Var Formula


data AssumeAssertStatement = Assume Formula
                            | Assert Formula
                            | Havoc Var
                            deriving (Show)

type AssumeAssertBlock = [AssumeAssertStatement]

type AssumeAssertProgram = (Name, AssumeAssertBlock)
