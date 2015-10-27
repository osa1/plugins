module Main where

import Control.Monad (forM_)

-- We need these undefined definitions because GHC first type checks and then
-- runs plugins.

addOne :: Int -> Int
addOne = undefined

factorial :: Int -> Int
factorial = undefined

main :: IO ()
main = do
    forM_ [1..10] $ print . addOne
    forM_ [1..10] $ print . factorial
