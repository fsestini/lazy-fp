module Pair where

class Pair p where
  pFst :: p a b -> a
  pSnd :: p a b -> b
  fromPair :: (a,b) -> p a b
  toPair :: p a b -> (a,b)
  toPair p = (pFst p, pSnd p)

instance Pair (,) where
  pFst = fst
  pSnd = snd
  fromPair = id
