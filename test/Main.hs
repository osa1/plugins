module Main where

import Control.Monad (forM_)

--------------------------------------------------------------------------------
-- Even with this piece of code, GHC is simply unable to evaluate this in
-- compile time.

-- import Prelude hiding (unlines)
--
-- unlines :: [String] -> String
-- unlines [] = []
-- unlines (l:ls) = l ++ '\n' : unlines ls
{- # INLINE unlines #-}
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------

data Either1 a b = Left1 a | Right1 b

instance Functor (Either1 a) where
  fmap _ (Left1 a)  = Left1 a
  fmap f (Right1 a) = Right1 (f a)

data Maybe1 a = Nothing1 | Just1 a

instance Functor Maybe1 where
  fmap _ Nothing1  = Nothing1
  fmap f (Just1 a) = Just1 (f a)

--------------------------------------------------------------------------------

main :: IO ()
main = do
    printHelp
    forM_ [1..10] $ print . addOne
    forM_ [1..10] $ print . factorial
