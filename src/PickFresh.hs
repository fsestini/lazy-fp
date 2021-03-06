{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module PickFresh where

import qualified Stream as S

class PickFresh a where
  pickFresh :: [a] -> a

freshStream :: PickFresh a => [a] -> S.Stream a
freshStream used = let x = pickFresh used in S.Cons x (freshStream (x : used))

pickNTh :: PickFresh a => Int -> a
pickNTh n = pickFresh $ S.take n (freshStream [])

instance PickFresh String where
  pickFresh strings = tryString strings 0
    where
      tryString :: [String] -> Int -> String
      tryString strings i = let x = "x" ++ show i in
        if x `notElem` strings
          then x
          else tryString strings (i + 1)
