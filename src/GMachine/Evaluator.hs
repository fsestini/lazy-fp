module GMachine.Evaluator(
  GMStateMonad,
  eval
) where

import GMachine.Structures
import Control.Monad.State.Lazy
import Syntax
import Heap
import Data.Maybe

--------------------------------------------------------------------------------
-- Evaluation monad and related utility functions

type GMStateMonad a = State GMState a

fromStTrans :: (GMState -> GMState) -> GMStateMonad ()
fromStTrans f = do
  s <- get
  put $ f s

getStack = fmap stack get

getGlobals :: GMStateMonad GMGlobals
getGlobals = fmap globals get

getHeap :: GMStateMonad GMHeap
getHeap = fmap heap get

setCode :: GMCode -> GMStateMonad ()
setCode c = get >>= \s -> put $ s { code = c }

setStack :: GMStack -> GMStateMonad ()
setStack st = get >>= \s -> put $ s { stack = st }

pushOnStack :: Addr -> GMStateMonad ()
pushOnStack addr = fromStTrans $ \s -> s { stack = addr : stack s }

popStack :: GMStateMonad Addr
popStack = do
  (a : as) <- fmap stack get
  setStack as
  return a

peekStack :: Int -> GMStateMonad Addr
peekStack n = do
  s <- fmap stack get
  return $ s !! n

popInstruction :: GMStateMonad Instruction
popInstruction = do
  (c : cs) <- fmap code get
  fromStTrans $ \s -> s { code = cs }
  return c

putGlobals :: (Name, Addr) -> GMStateMonad ()
putGlobals p = fromStTrans $ \s -> s { globals = p : globals s }

changeHeap :: HeapState Node a -> GMStateMonad a
changeHeap hs = do
  h <- getHeap
  let (x, h') = runState hs h
  fromStTrans $ \s -> s { heap = h' }
  return x

--------------------------------------------------------------------------------
-- Evaluation

eval :: GMStateMonad [GMState]
eval = do
  s <- get
  restStates <- if gmFinal s
    then return []
    else step >> doAdmin >> eval
  return $ s : restStates

step :: GMStateMonad ()
step = popInstruction >>= dispatch

doAdmin :: GMStateMonad ()
doAdmin = fromStTrans (\s -> s { stats = statIncSteps (stats s) })

-- The G-Machine has finished when the code sequence that it is executing is
-- empty.
gmFinal :: GMState -> Bool
gmFinal = null . code

--------------------------------------------------------------------------------
-- Execution of single instructions

dispatch :: Instruction -> GMStateMonad ()
dispatch (PushGlobal f) = pushGlobal f
dispatch Unwind = unwind
dispatch (PushInt n) = pushInt n
dispatch (Push n) = push n
dispatch Mkap = mkap
dispatch (Update n) = update n
dispatch (Pop n) = pop n

update :: Int -> GMStateMonad ()
update n = do
  a <- popStack
  an <- peekStack n
  changeHeap $ hUpdate an (NInd a)

pop :: Int -> GMStateMonad ()
pop n = replicateM_ n popStack

pushGlobal :: Name -> GMStateMonad ()
pushGlobal f = do
  globs <- getGlobals
  let a = fromMaybe (error $ err f) $ lookup f globs
  pushOnStack a
  where
    err g = "Undeclared global: " ++ g

pushInt :: Int -> GMStateMonad ()
pushInt i = do
  globs <- getGlobals
  case lookup (show i) globs of
    Just a -> pushOnStack a
    Nothing -> do
      a <- changeHeap (hAlloc (NNum i))
      putGlobals (show i, a)
      pushOnStack a

mkap :: GMStateMonad ()
mkap = do
  a1 <- popStack
  a2 <- popStack
  addr <- changeHeap (hAlloc (NAp a1 a2))
  pushOnStack addr

push :: Int -> GMStateMonad ()
push n = do
  addr <- peekStack $ n + 1
  (NAp a1 a2) <- changeHeap $ hLookup' addr
  pushOnStack a2

slide :: Int -> GMStateMonad ()
slide n = do
  (a : st) <- getStack
  setStack $ a : drop n st

unwind :: GMStateMonad ()
unwind = do
  a <- peekStack 0
  node <- changeHeap $ hLookup' a
  case node of
    (NNum node) -> return ()
    (NAp a1 a2) -> pushOnStack a1 >> setCode [Unwind]
    (NInd addr) -> popStack >> pushOnStack addr >> setCode [Unwind]
    (NGlobal arity c) -> do
      st <- getStack
      if length st < arity
        then error "unwinding too few arguments"
        else setCode c
