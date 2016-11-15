module Heap(
  hInitial,
  hAlloc,
  hUpdate,
  hFree,
  hLookup,
  hAddresses,
  hSize,
  hNull,
  hIsNull,
  Heap,
  Addr,
  HeapState
) where

import Data.List
import Data.Maybe
import Control.Monad.State

remove :: Eq k => [(k,v)] -> k -> [(k,v)]
remove []     _ = error "remove failed"
remove ((k,v):xs) key | k == key = xs
                      | otherwise = (k,v) : remove xs key

-- number of objects in the heap, list of unused addresses, association list
type Addr = Int
type Heap a = (Int, [Addr], [(Addr, a)])

type HeapState a b = State (Heap a) b

hInitial :: Heap a
hInitial = (0, [1..], [])

-- Modification functions
hAlloc :: a -> HeapState a Addr
hAlloc node = do
  (size, next : free, cts) <- get
  put (size+1, free, (next,node):cts)
  return next

hUpdate :: Addr -> a -> HeapState a ()
hUpdate addr node = do
  (size, free, cts) <- get
  put (size, free, (addr, node) : remove cts addr)
  return ()

hFree :: Addr -> HeapState a ()
hFree addr = do
  (size, free, cts) <- get
  put (size - 1, addr : free, remove cts addr)
  return ()

-- Querying functions
hLookup :: Heap a -> Addr -> a
hLookup (_, _, cts) addr = fromMaybe err $ lookup addr cts
  where
    err = error $ "can't find node " ++ show addr ++ " in the heap"

hAddresses :: Heap a -> [Addr]
hAddresses (_, _, cts) = map fst cts

hSize :: Heap a -> Int
hSize (size, _, _) = size

hNull :: Addr
hNull = 0

hIsNull :: Addr -> Bool
hIsNull = (== 0)
