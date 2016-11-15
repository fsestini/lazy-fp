module Compiler where

import Syntax
import Heap
import Data.List
import Data.Maybe
import Control.Monad.State

{-
unwinding a single application node onto the stack:
    a : s        d    h[a : NAp a1 a2]   f
==> a1 : a : s   d    h                  f

perform a supercombinator reduction:
     a0 : a1 : ... : an : s    d    h[a0 : NSuperComb [x1,...,xn] body]   f
==>                  ar : s    d    h'                                    f
where (h', ar) = instantiate body h f[x1 |-> a1, ..., xn |-> an ]

-}

-- type of the spine of the stack
type TiStack = [Addr]

-- type of the dump
data TiDump = DummyTiDump
initialTiDump = DummyTiDump

data Node = NAp Addr Addr
          | NSuperComb Name {- Name is for doc and debugging -} [Name] CoreExpr
          | NNum Int
          deriving (Show, Eq)

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

type TiHeapState a = HeapState Node a

--------------------------------------------------------------------------------
-- Compilation

compile :: CoreProgram -> TiState
compile program = (initialStack, initialTiDump, initialHeap, globals, tiStatInitial)
  where
    scDefs = program ++ preludeDefs -- ++ extraPreludeDefs
    (initialHeap, globals) = buildInitialHeap scDefs
    initialStack = [addressOfMain]
    addressOfMain = aLookup globals "main" (error "main is not defined")

-- Build initial heap from the set of supercombinators that make up the program.
buildInitialHeap :: [CoreScDefn] -> (TiHeap, TiGlobals)
buildInitialHeap = (\(x,y) -> (y,x)) . flip runState hInitial . mapM allocateSc

-- Allocate a node for a supercombinator in the heap.
-- Return the pair (name, address) of the superc.
allocateSc :: CoreScDefn -> TiHeapState (Name, Addr)
allocateSc (name, args, body) =
  (,) <$> pure name <*> hAlloc (NSuperComb name args body)

aLookup :: TiGlobals -> Name -> Addr -> Addr
aLookup alist k v = fromMaybe v $ lookup k alist

--------------------------------------------------------------------------------
-- Evaluator

step :: TiState -> TiState
step state = dispatch (hLookup heap (head stack))
  where
    (stack,_,heap,_,_) = state

    dispatch :: Node -> TiState
    dispatch (NNum _) = error "number applied as a function" -- numStep state n
    dispatch (NAp a1 a2) = apStep state a1 a2
    dispatch (NSuperComb sc args body) = scStep state sc args body

apStep :: TiState -> Addr -> Addr -> TiState
apStep (stack,dump,heap,globals,stats) a1 a2 =
  (a1 : stack, dump, heap, globals, stats)

scStep :: TiState -> Name -> [Name] -> CoreExpr -> TiState
scStep (stack,dump,heap,globals,stats) scName argNames body =
  (newStack, dump, newHeap, globals, stats)
  where
    argBindings = zip argNames (getArgs heap stack)
    env = argBindings ++ globals
    (newHeap, resultAddr) = instantiate body heap env
    newStack = resultAddr : drop (length argNames + 1) stack

instantiate' :: CoreExpr -> Assoc Name Addr -> TiHeapState Addr
instantiate' (ENum n) env = hAlloc (NNum n)
instantiate' (EAp e1 e2) env = do
  addr1 <- instantiate' e1 env
  addr2 <- instantiate' e2 env
  hAlloc $ NAp addr1 addr2
instantiate' (EVar x) env =
  return $ aLookup env x (error $ "undefined name: " ++ show x)
instantiate' (EBinOp e1 e2 e3) env = error "binary operators not supported"
instantiate' (ECtor expr1 expr2) env = instantiateConstr
instantiate' (ELet Recursive binds body) env = instantiateLetRec binds body env
instantiate' (ELet NonRecursive binds body) env = instantiateLet binds body env
instantiate' (ECase expr1 expr2) env = error "case expressions not supported"
instantiate' (ELam expr1 expr2) env = error "lambda expressions not supported"

instantiateConstr = undefined

instantiateLet :: Assoc Name CoreExpr
               -> CoreExpr
               -> Assoc Name Addr
               -> TiHeapState Addr
instantiateLet binds body env = do
  addresses <- mapM (`instantiate'` env) (rhssOf binds)
  let newEnv = env ++ zip (map fst binds) addresses
  instantiate' body newEnv

instantiateLetRec :: Assoc Name CoreExpr -> CoreExpr -> Assoc Name Addr -> TiHeapState Addr
instantiateLetRec binds body env = do
  heap <- get
  let (heappp, addr) = aux heap binds body env
  put heappp
  return addr
  where
    aux heap binds body env = instantiate body heap' newEnv
      where (addresses, heap') =
                runState (mapM (`instantiate'` newEnv) (rhssOf binds)) heap
            newEnv = env ++ zip (map fst binds) addresses

instantiate :: CoreExpr -> TiHeap -> Assoc Name Addr -> (TiHeap, Addr)
instantiate expr heap env = swap $ runState (instantiate' expr env) heap
  where swap (x,y) = (y,x)

-- Takes a stack with a sc node on top of application nodes, and return a list
-- formed from the argument of each of the application nodes on the stack.
getArgs :: TiHeap -> TiStack -> [Addr]
getArgs heap (sc:stack) = map getArg stack
  where
    getArg addr = arg
      where
        (NAp fun arg) = hLookup heap addr

eval :: TiState -> [TiState]
eval state = state : restStates
  where
    restStates | tiFinal state = []
               | otherwise = eval nextState
    nextState = doAdmin (step state)

doAdmin :: TiState -> TiState
doAdmin = applyToStats tiStatIncSteps

-- Tests for final state
tiFinal :: TiState -> Bool
tiFinal ([soleAddr], _, heap, _, _) =
  isDataNode (hLookup heap soleAddr)
tiFinal ([],_,_,_,_) = error "empty stack"
tiFinal _ = False

isDataNode :: Node -> Bool
isDataNode (NNum n) = True
isDataNode _ = False
