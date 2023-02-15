module Verify (Result(..), verify) where

import Language(Program)
import AssumeAssert(Program)
import Parser.Parser

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify inputProgram = do
  let parsedProgram = parseProg inputProgram

  let assumeAssertedProgram = convertToAssumeAssert parsedProgram

  let weakestPreProgram = computeWeakestPrecondition assumeAssertedProgram

  -- TODO: verify with SMT solver

  return Verified

covertToAssumeAssert :: Language.Program -> AssumeAssert.Program
convertToAssumeAssert inputProgram =

computeWeakestPrecondition :: AssumeAssert.Program -> ?
computeWeakestPrecondition inputProgram =
