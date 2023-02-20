module Verify (Result(..), verify) where

import Language
import AssumeAssert
import Parser.Parser

data Result = Verified | NotVerified | Unknown String
  deriving (Eq, Show)

verify :: String -> IO Result
verify inputProgram = do
  let parsedProgram = parseProg inputProgram
  putStrLn (show parsedProgram)

  -- let assumeAssertedProgram = convertToAssumeAssertDriver parsedProgram

  -- let weakestPreProgram = computeWeakestPrecondition assumeAssertedProgram

  -- TODO: verify with SMT solver

  return Verified

-- convertToAssumeAssertDriver :: Language.Program -> AssumeAssert.Program
-- convertToAssumeAssertDriver inputProgram =
--   -- for each Assertion in the preconditions, make a Statement
--   -- end with list of statements
--   let preconditions = AssumeAssert.Statement Assume inputProgram[1]

--   -- | Handle program body
--   -- let programBody = []

--   -- for each Assertion in the postconditions, make a Statement
--   -- end with list of statements
--   -- let postconditions = AssumeAssert.Statement inputProgram[3]

--   return AssumeAssert.Program preconditions


-- computeWeakestPrecondition :: AssumeAssert.Program -> ?
-- computeWeakestPrecondition inputProgram =
