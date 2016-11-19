module TemplateInstantiation.Structures where

import Data.Tuple
import Syntax
import Heap
import Data.List
import Data.Maybe

-- type of the spine of the stack
type TiStack = [Addr]

-- type of the dump
type TiDump = [TiStack]
initialTiDump = []

data Node = NAp Addr Addr
          | NSuperComb Name {- Name is for doc and debugging -} [Name] CoreExpr
          | NNum Int
          | NInd Addr -- Indirection node
          | NPrim Name Primitive {- Name again for doc and debugging -}
          deriving (Show, Eq)

data Primitive = PAdd | PSub | PMul | PDiv deriving (Eq, Show)

type TiHeap = Heap Node

type Assoc a b = [(a,b)]
-- associates each supercombinator name with the address of a heap node
-- containing its definition
type TiGlobals = Assoc Name Addr

-- statistics
type TiStats = Int
tiStatInitial = 0
tiStatIncSteps s = s + 1
tiStatGetSteps s = s

applyToStats :: (TiStats -> TiStats) -> TiState  -> TiState
applyToStats f (s, d, h, e, stats) = (s, d, h, e, f stats)

-- type of the state of the template instantiation machine
type TiState = (TiStack, TiDump, TiHeap, TiGlobals, TiStats)

stack   (s,_,_,_,_) = s
dump    (_,d,_,_,_) = d
heap    (_,_,h,_,_) = h
globals (_,_,_,g,_) = g
stats   (_,_,_,_,s) = s

liftHeapFunc f (s,d,h,g,w) = (s,d,f h,g,w)

type TiHeapState a = HeapState Node a
