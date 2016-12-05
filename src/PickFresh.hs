{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module PickFresh where

class PickFresh a where
  pickFresh :: [a] -> a

freshStream :: PickFresh a => [a] -> [a]
freshStream l = let x = pickFresh l in x : freshStream (x : l)

instance PickFresh String where
  pickFresh strings = tryString strings 0
    where
      tryString :: [String] -> Int -> String
      tryString strings i = let x = "x" ++ show i in
        if x `notElem` strings
          then x
          else tryString strings (i + 1)
