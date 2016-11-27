module AssocList(
  Assoc,
  aLookup,
  aUpdate
) where

import Data.List
import Data.Maybe

type Assoc a b = [(a,b)]

aLookup :: Eq a => Assoc a b -> a -> b -> b
aLookup list key v = fromMaybe v $ lookup key list

aUpdate :: Eq a => [(a,b)] -> (a,b) -> [(a,b)]
aUpdate alist (key, val) = (key,val) : filter ((key /=) . fst) alist
