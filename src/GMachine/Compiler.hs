module GMachine.Compiler where

import Control.Monad.State.Lazy (runState)
import Data.Tuple (swap)
import Data.Maybe (fromMaybe)
import Control.Arrow (second)
import Control.Monad (forM)
import Control.Monad.Reader

import GMachine.Structures
import Syntax
import Heap
import AssocList

--------------------------------------------------------------------------------
-- Compilation data structures

type GMHeapState a = HeapState Node a
type GMCompiledSc = (Name, Int, GMCode)
type CEnv = Assoc Name Int
data CMode = Strict | NonStrict
data CState = CState { mode :: CMode,
                       env  :: CEnv }
type CMonad a = Reader CState a

askMode :: CMonad CMode
askMode = fmap mode ask

askEnv :: CMonad CEnv
askEnv = fmap env ask

inEnv :: CMonad a -> CEnv -> CMonad a
inEnv m e = local (\s -> s { env = e }) m

inShiftedEnv :: CMonad a -> Int -> CMonad a
inShiftedEnv m n = local (\s -> s { env = shiftEnv n (env s) }) m

inMode :: CMonad a -> CMode -> CMonad a
inMode m md = local (\s -> s { mode = md }) m

branchMode :: CMonad a -> CMonad a -> CMonad a
branchMode strict nonstrict = do
  m <- askMode
  case m of
    Strict -> strict
    NonStrict -> nonstrict

transformEnv :: CMonad a -> (CEnv -> CEnv) -> CMonad a
transformEnv m t = local (\s -> s { env = t . env $ s }) m

--------------------------------------------------------------------------------

-- Turns a program into an initial state for the G-Machine. The initial code
-- sequence finds the global main and then evaluates it. The heap is initialized
-- so that it contains a node for each global declared.
compile :: CoreProgram -> GMState
compile program = GMState initialCode [] [] heap globals statInitial
  where
    (heap, globals) = buildInitialHeap program

buildInitialHeap :: CoreProgram -> (GMHeap, GMGlobals)
buildInitialHeap program = swap $ runState (forM compiled allocateSc) hInitial
  where
    compiled :: [GMCompiledSc]
    compiled = map compileSc (preludeDefs ++ program) ++ compiledPrimitives

compiledPrimitives :: [GMCompiledSc]
compiledPrimitives = [
    ("+", 2, [Push 1, Eval, Push 1, Eval, Add, Update 2, Pop 2, Unwind]),
    ("-", 2, [Push 1, Eval, Push 1, Eval, Sub, Update 2, Pop 2, Unwind]),
    ("*", 2, [Push 1, Eval, Push 1, Eval, Mul, Update 2, Pop 2, Unwind]),
    ("/", 2, [Push 1, Eval, Push 1, Eval, GMachine.Structures.Div, Update 2, Pop 2, Unwind])
  ]

-- Allocates a new global node for its compiled supercombinator argument
allocateSc :: GMCompiledSc -> GMHeapState (Name, Addr)
allocateSc (name, arity, code) = (,) name <$> hAlloc (NGlobal arity code)

initialCode :: GMCode
initialCode = [PushGlobal "main", Unwind]

--------------------------------------------------------------------------------
-- Main compilation functions

compileSc :: CoreScDefn -> GMCompiledSc
compileSc (name, args, body) =
  (name, length args, compileR body (zip args [0..]))

-- Generates code which instantiates the body e of a supercombinator, and then
-- proceeds to unwind the resulting stack.
compileR :: CoreExpr -> [(Name, Int)] -> GMCode
compileR e env = body ++ [Update n, Pop n, Unwind]
  where
    body = runReader (compilee e) (CState Strict env)
    n = length env

compilee :: CoreExpr -> CMonad GMCode
compilee (ENum n) = return [PushInt n]
compilee (ELet NonRecursive defs e) = compileLet defs e
compilee (ELet Recursive defs e) = compileLetRec defs e
compilee (EBinOp binop e1 e2) = compileBinOp binop e1 e2
compilee (EVar x) = strictWrap $ flip inMode NonStrict $ do
  env <- askEnv
  if x `elem` map fst env
    then return [Push $ lkup env x]
    else return [PushGlobal x]
compilee (EAp e0 e1) = strictWrap $ flip inMode NonStrict $
  compilee e1 <++> compilee e0 `inShiftedEnv` 1 <++> pure [Mkap]
compilee (ECtor e1 e2) = undefined
compilee (ECase e1 e2) = undefined
compilee (ELam e1 e2) = undefined

strictWrap :: CMonad GMCode -> CMonad GMCode
strictWrap m = branchMode (fmap (++ [Eval]) m) m

--------------------------------------------------------------------------------
-- Binary operation compilation

compileBinOp :: BinOp -> CoreExpr -> CoreExpr -> CMonad GMCode
compileBinOp binop e1 e2 =
  compilee e2 <++> compilee e1 `inShiftedEnv` 1 <++> case binop of
    Plus       -> branchMode (return [Add])
                             (return [PushGlobal "+", Mkap, Mkap])
    Minus      -> branchMode (return [Sub])
                             (return [PushGlobal "-", Mkap, Mkap])
    Mult       -> branchMode (return [Mul])
                             (return [PushGlobal "*", Mkap, Mkap])
    Syntax.Div -> branchMode (return [GMachine.Structures.Div])
                             (return [PushGlobal "/", Mkap, Mkap])

--------------------------------------------------------------------------------
-- Let and Letrec compilationo

compileLet :: CoreBinders -> CoreExpr -> CMonad GMCode
compileLet = compileGenericLet (const []) compBinder
  where compBinder _ _ (e, i) = compilee e `inMode` NonStrict `inShiftedEnv` i

compileLetRec :: CoreBinders -> CoreExpr -> CMonad GMCode
compileLetRec = compileGenericLet (return . Alloc) compBinder
  where compBinder n newEnv (e,i) =
          transformEnv (compilee e `inMode` NonStrict) newEnv
          <++> pure [Update $ n - 1 - i]

type BinderCompiler =  Int -> (CEnv -> CEnv)
                    -> (CoreExpr, Int) -> CMonad GMCode

compileGenericLet :: (Int -> GMCode)
                  -> BinderCompiler
                  -> CoreBinders
                  -> CoreExpr
                  -> CMonad GMCode
compileGenericLet before compBinder defs e = pure (before n)
  <++> join <$> forM (zip (rhssOf defs) [0..]) (compBinder n newEnv)
  <++> transformEnv (compilee e) newEnv
  <++> pure [Slide n]
  where
    n = length defs
    newEnv env = applyAll (map (flip aUpdate)
                          (zip (bindersOf defs) [n - 1..0]))
                          (shiftEnv n env)

--------------------------------------------------------------------------------
-- Utilities

shiftEnv :: Int -> [(Name, Int)] -> [(Name, Int)]
shiftEnv n = fmap (second (+ n))

applyAll :: [a -> a] -> a -> a
applyAll fs x = foldl (\ x f -> f x) x fs

lkup :: [(Name, Int)] -> Name -> Int
lkup rho x = fromMaybe (error err) $ lookup x rho
  where err = "cannot lookup " ++ show x ++ " in the compiler"

infixl 3 <++>
(<++>) :: CMonad GMCode -> CMonad GMCode -> CMonad GMCode
m1 <++> m2 = (++) <$> m1 <*> m2
