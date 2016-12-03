module GMachine.Evaluator(
  GMStateMonad,
  eval
) where

import GMachine.Structures
import Control.Monad.State.Lazy
import GMachine.Syntax hiding (Div)
import Heap
import Data.Maybe
import AssocList

--------------------------------------------------------------------------------
-- Evaluation monad and related utility functions

type GMStateMonad a = State GMState a

fromStTrans :: (GMState -> GMState) -> GMStateMonad ()
fromStTrans f = do
  s <- get
  put $ f s

getStack :: GMStateMonad GMStack
getStack = fmap stack get

getDump :: GMStateMonad GMDump
getDump  = fmap dump  get

getCode :: GMStateMonad GMCode
getCode  = fmap code  get

appendOutput :: String -> GMStateMonad ()
appendOutput o = fromStTrans $ \s -> s { output = output s ++ o }

getGlobals :: GMStateMonad GMGlobals
getGlobals = fmap globals get

getHeap :: GMStateMonad GMHeap
getHeap = fmap heap get

setCode :: GMCode -> GMStateMonad ()
setCode c = get >>= \s -> put $ s { code = c }

prependCode :: GMCode -> GMStateMonad ()
prependCode c = fromStTrans $ \s -> s { code = c ++ code s }

setStack :: GMStack -> GMStateMonad ()
setStack st = get >>= \s -> put $ s { stack = st }

setDump :: GMDump -> GMStateMonad ()
setDump d = get >>= \s -> put $ s { dump = d }

pushOnStack :: Addr -> GMStateMonad ()
pushOnStack addr = fromStTrans $ \s -> s { stack = addr : stack s }

pushOnDump :: GMDumpItem -> GMStateMonad ()
pushOnDump di = fromStTrans $ \s -> s { dump = di : dump s }

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
dispatch (Alloc n) = alloc n
dispatch (Slide n) = slide n
dispatch Eval = eval'
dispatch Add = arithmetic2 (+)
dispatch Sub = arithmetic2 (-)
dispatch Mul = arithmetic2 (*)
dispatch Div = arithmetic2 div
dispatch Comp = boolean2 (==)
dispatch Print = evalPrint
dispatch (Split n) = split n
dispatch (Pack tag arity) = pack tag arity
dispatch (CaseJump alternatives) = casejump alternatives

casejump :: Assoc Int GMCode -> GMStateMonad ()
casejump alterns = do
  (NConstr tag _) <- peekStack 0 >>= changeHeap . hLookup'
  let branch = aLookup alterns tag (error "casejump failed")
  prependCode branch

pack :: CtorTag -> CtorArity -> GMStateMonad ()
pack tag arity = do
  addrs <- replicateM arity popStack
  changeHeap (hAlloc (NConstr tag addrs)) >>= pushOnStack

split :: Int -> GMStateMonad ()
split _ = do
  (NConstr _ addrs) <- popStack >>= changeHeap . hLookup'
  forM_ (reverse addrs) pushOnStack

evalPrint :: GMStateMonad ()
evalPrint = do
  node <- popStack >>= changeHeap . hLookup'
  case node of
    (NNum x)            -> appendOutput $ show x
    (NConstr _ addrs) -> prependCode (concatMap (const [Eval, Print]) addrs)
                           >> forM_ (reverse addrs) pushOnStack
    _                   -> error "evalPrint failed"

eval' :: GMStateMonad ()
eval' = do
  (a : s) <- getStack
  i       <- getCode
  pushOnDump (i,s)
  setStack [a]
  setCode [Unwind]

alloc :: Int -> GMStateMonad ()
alloc n = replicateM_ n $ changeHeap (hAlloc $ NInd hNull) >>= pushOnStack

update :: Int -> GMStateMonad ()
update n = do
  a <- popStack
  an <- peekStack n
  changeHeap $ hUpdate an (NInd a)

pop :: Int -> GMStateMonad ()
pop n = replicateM_ n popStack

pushGlobal :: GlobalName -> GMStateMonad ()
pushGlobal (Left f) = do
  globs <- getGlobals
  let a = fromMaybe (error $ err f) $ lookup f globs
  pushOnStack a
  where
    err g = "Undeclared global: " ++ g
pushGlobal (Right (tag, arity)) = do
  globs <- getGlobals
  let name = "Pack{" ++ show tag ++ "," ++ show arity ++ "}"
  let a = lookup name globs
  case a of
    (Just addr) -> pushOnStack addr
    Nothing -> do
      adr <- changeHeap $ hAlloc (NGlobal arity
        [Pack tag arity, Update 0, Unwind])
      putGlobals (name, adr)
      pushOnStack adr

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
  addr <- peekStack n
  pushOnStack addr

slide :: Int -> GMStateMonad ()
slide n = do
  (a : st) <- getStack
  setStack $ a : drop n st

unwind :: GMStateMonad ()
unwind = do
  a <- peekStack 0
  node <- changeHeap $ hLookup' a
  case node of
    (NNum _)      -> maybePopDump a
    (NConstr _ _) -> maybePopDump a
    (NAp a1 _) -> pushOnStack a1 >> setCode [Unwind]
    (NInd addr) -> popStack >> pushOnStack addr >> setCode [Unwind]
    (NGlobal arity c) -> do
      st <- getStack
      if (length st - 1) < arity
        then maybePopDump (last st)
        else rearrange arity >> setCode c
  where
    maybePopDump a = do
      d <- getDump
      case listToMaybe d of
        Just (co, st) -> setCode co >> setStack (a : st) >> setDump (tail d)
        Nothing -> return ()

rearrange :: Int -> GMStateMonad ()
rearrange n = do
  h  <- getHeap
  as <- getStack
  let as' = map (getArg . hLookup h) (tail as)
  setStack $ take n as' ++ drop n as

getArg :: Node -> Addr
getArg (NAp _ a) = a
getArg _ = error "not an Ap node in getArg"

--------------------------------------------------------------------------------
-- Generic primitive operations

type Boxing   a = a    -> GMStateMonad ()
type Unboxing a = Addr -> GMStateMonad a

primitive1 :: Boxing b -> Unboxing a -> (a -> b) -> GMStateMonad ()
primitive1 box unbox op = op <$> (popStack >>= unbox) >>= box

primitive2 :: Boxing b -> Unboxing a -> (a -> a -> b) -> GMStateMonad ()
primitive2 box unbox op =
  op <$> (popStack >>= unbox) <*> (popStack >>= unbox) >>= box

--------------------------------------------------------------------------------
-- Arithmetic instructions

arithmetic2 :: (Int -> Int -> Int) -> GMStateMonad ()
arithmetic2 = primitive2 boxInteger unboxInteger

boxInteger :: Int -> GMStateMonad ()
boxInteger n = do
  a <- changeHeap $ hAlloc (NNum n)
  pushOnStack a

unboxInteger :: Addr -> GMStateMonad Int
unboxInteger addr = do
  (NNum i) <- changeHeap $ hLookup' addr
  return i

--------------------------------------------------------------------------------
-- Boolean operations

boxBoolean :: Bool -> GMStateMonad ()
boxBoolean b = do
  a <- changeHeap $ hAlloc (NConstr bRepr [])
  pushOnStack a
  where
    bRepr | b = 2         -- <2> is true
          | otherwise = 1 -- <1> is false

boolean2 :: (Int -> Int -> Bool) -> GMStateMonad ()
boolean2 = primitive2 boxBoolean unboxInteger
