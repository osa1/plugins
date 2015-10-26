module Main where

import Control.Monad (forM_)

addOne :: Int -> Int
addOne = undefined

factorial :: Int -> Int
factorial = undefined

haskellFactorial :: Int -> Int
haskellFactorial 0 = 1
haskellFactorial n = n * haskellFactorial (n - 1)

main :: IO ()
main = do
    forM_ [1..10] $ print . addOne
    forM_ [1..10] $ print . haskellFactorial
    forM_ [1..10] $ print . factorial
