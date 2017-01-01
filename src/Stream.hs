{-# LANGUAGE DeriveFunctor #-}

module Stream where

import Prelude hiding (take)
data Stream a = Cons a (Stream a) deriving (Eq, Show, Ord, Functor)

take :: Int -> Stream a -> [a]
take 0 _ = []
take n (Cons x xs) = x : take (n-1) xs
