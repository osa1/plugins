module Main where

import Control.Monad (forM_)

-- We need these undefined definitions because GHC first type checks and then
-- runs plugins.

addOne :: Int -> Int
addOne = undefined

factorial :: Int -> Int
factorial = undefined

printHelp :: IO ()
printHelp = putStrLn helpMsg
  where
    helpMsg = unlines ["This is a help",
                       "message that takes",
                       "couple of lines."]

main :: IO ()
main = do
    printHelp
    forM_ [1..10] $ print . addOne
    forM_ [1..10] $ print . factorial
