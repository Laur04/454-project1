module Verify (Result(..), verify) where

import Parser.Parser

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify prog = do
  let parsedProgram = parseProg prog
  print parsedProgram[0]
  let assumeAssertProgram = convertToAssumeAssert parsedProgram[1]
  let verificationCondition = computeWeakestPrecondition assumeAssertProgram

  return Verified

covertToAssumeAssert :: Language.Program -> Language.Program.Block
convertToAssumeAssert prog =

convertHelper :: Language.Program.Statement


computeWeakestPrecondition :: String -> String
