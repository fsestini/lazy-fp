{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}

module Heap(
  hInitial,
  hAlloc,
  hUpdate,
  hUpdate',
  hFree,
  hLookup,
  hLookup',
  hAddresses,
  hAddresses',
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
data Heap a = Heap { count :: Int,
                     freeAddrs :: [Addr],
                     assocList :: [(Addr,a)] }
              deriving (Eq, Show)

type HeapState a b = State (Heap a) b

mapSnd f (x,y) = (x,f y)

instance Functor Heap where
  fmap f (Heap count unused assocList) =
    Heap count unused (map (mapSnd f) assocList)

hInitial :: Heap a
hInitial = Heap 0 [1..] []

-- Modification functions
hAlloc :: a -> HeapState a Addr
hAlloc node = get >>= \case
  Heap size (next : free) cts -> do
    put (Heap (size+1) free ((next,node) : cts))
    return next

hUpdate :: Addr -> a -> HeapState a ()
hUpdate addr node = do
  Heap size free cts <- get
  put (Heap size free ((addr, node) : remove cts addr))
  return ()

hUpdate' :: Addr -> a -> Heap a -> Heap a
hUpdate' addr x = execState (hUpdate addr x)

hFree :: Addr -> HeapState a ()
hFree addr = do
  Heap size free cts <- get
  put (Heap (size - 1) (addr : free) (remove cts addr))
  return ()

hLookup' :: Addr -> HeapState a a
hLookup' addr = do
  (Heap _ _ cts) <- get
  return $ fromMaybe err (lookup addr cts)
  where
    err = error $ "can't find node " ++ show addr ++ " in the heap"

-- Querying functions
hLookup :: Heap a -> Addr -> a
hLookup (Heap _ _ cts) addr = fromMaybe err $ lookup addr cts
  where
    err = error $ "can't find node " ++ show addr ++ " in the heap"

hAddresses :: Heap a -> [Addr]
hAddresses (Heap _ _ cts) = map fst cts

hAddresses' :: HeapState a [Addr]
hAddresses' = do
  heap <- get
  return $ hAddresses heap

hSize :: Heap a -> Int
hSize (Heap size _ _) = size

hNull :: Addr
hNull = 0

hIsNull :: Addr -> Bool
hIsNull = (== 0)
