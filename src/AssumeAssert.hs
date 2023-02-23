module AssumeAssert (GCommand(..)) where

import Language(Assertion)

data GCommand = Assume Assertion
               | Assert Assertion
               | Havoc String
               | Comb GCommand GCommand
               | Box GCommand GCommand
               deriving (Show)
