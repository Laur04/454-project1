module AssumeAssert (Assume(..), Assert(..), Havoc(..)) where

import Language

type Name = String

type Var = String

data AssumeAssertStatement = Assume BoolExp
                            | Assert BoolExp
                            | Havoc Var
                            deriving (Show)

type AssumeAssertBlock = [AssumeAssertStatement]

type AssumeAssertProgram = (Name, AssumeAssertBlock)
