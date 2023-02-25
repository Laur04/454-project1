module Main (main) where

import Verify

import System.Environment

main :: IO ()
main = do
    as <- getArgs
    prog <- readFile (head as)
    result <- verify prog
    -- putStrLn ""
    case result of
      Verified -> putStrLn "Verified"
      NotVerified -> putStrLn "Not verified"
      Unknown msg -> putStrLn ("Verifier returned unknown: " ++ msg)
