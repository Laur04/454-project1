import Verify

import Data.List (findIndices)
import System.Directory
import System.Exit

main :: IO ()
main = do
  let benchmarksPath = "./benchmarks/"
  testSet NotVerified (benchmarksPath ++ "invalid/")
  testSet Verified (benchmarksPath ++ "valid/")

testSet :: Result -> String -> IO ()
testSet desiredOutput path = do
  files <- listDirectory path
  output <- mapM (\file -> readFile file >>= verify) (map (path ++) files)
  let failures = findIndices (desiredOutput /=) output
  if length failures > 0
    then
      let failedFiles = unwords (map (files !!) failures) in
      die $ show desiredOutput ++ " set failed on files: " ++ failedFiles
  else putStrLn (show desiredOutput ++ " set succeeded")
  
