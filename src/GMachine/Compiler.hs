{-# LANGUAGE DataKinds, KindSignatures, GADTs, RankNTypes #-}

module GMachine.Compiler where

import qualified Data.List.NonEmpty as NE
import Control.Monad.State.Lazy (runState)
import Data.Tuple (swap)
import Data.Maybe (fromMaybe)
import Control.Arrow (second)
import Control.Monad (forM)
import Control.Monad.Reader

import GMachine.Structures
import GMachine.Syntax
import Heap
import AssocList

--------------------------------------------------------------------------------
-- Compilation data structures

type GMHeapState a = HeapState Node a
type GMCompiledSc = (Name, Int, GMCode)
data CMode = Strict | NonStrict
type CEnv = Assoc Name Int
data CState (m :: CMode) :: * where
  StrictEnv :: CEnv ->  CState Strict
  NonStrictEnv :: CEnv -> CState NonStrict

-- Compilation monad indexed by the evaluation mode (strict vs. non-strict)
type CMonad m a = Reader (CState m) a

env :: CState m -> CEnv
env (StrictEnv e) = e
env (NonStrictEnv e) = e

envToStateTransformer :: (CEnv -> CEnv) -> CState m -> CState m
envToStateTransformer envT (StrictEnv e) = StrictEnv $ envT e
envToStateTransformer envT (NonStrictEnv e) = NonStrictEnv $ envT e

transformEnv :: CMonad m a -> (CEnv -> CEnv) -> CMonad m a
transformEnv m t = local (envToStateTransformer t) m

askEnv :: CMonad m CEnv
askEnv = fmap env ask

inEnv :: CMonad m a -> CEnv -> CMonad m a
inEnv m e = local (transformState e) m
  where
    transformState :: CEnv -> CState m -> CState m
    transformState env (StrictEnv _) = StrictEnv env
    transformState env (NonStrictEnv _) = NonStrictEnv env

inShiftedEnv :: CMonad m a -> Int -> CMonad m a
inShiftedEnv m n = local (envToStateTransformer $ shiftEnv n) m

inStrictMode :: CMonad Strict a -> CMonad m a
inStrictMode = withReader transformStrict
  where
    transformStrict :: CState m -> CState Strict
    transformStrict (StrictEnv env) = StrictEnv env
    transformStrict (NonStrictEnv env) = StrictEnv env

inNonStrictMode :: CMonad NonStrict a -> CMonad m a
inNonStrictMode = withReader transformNonStrict
  where
    transformNonStrict :: CState m -> CState NonStrict
    transformNonStrict (StrictEnv env) = NonStrictEnv env
    transformNonStrict (NonStrictEnv env) = NonStrictEnv env

branchMode :: CMonad Strict a -> CMonad NonStrict a -> CMonad m a
branchMode strict nonstrict = do
  e <- ask
  case e of
    (StrictEnv _) -> strict
    (NonStrictEnv _) -> nonstrict

--------------------------------------------------------------------------------

-- Turns a program into an initial state for the G-Machine. The initial code
-- sequence finds the global main and then evaluates it. The heap is initialized
-- so that it contains a node for each global declared.
compile :: GProgramN -> GMState
compile program = GMState [] initialCode [] [] heap globals statInitial
  where
    (heap, globals) = buildInitialHeap program

buildInitialHeap :: GProgramN -> (GMHeap, GMGlobals)
buildInitialHeap program = swap $ runState (forM compiled allocateSc) hInitial
  where
    compiled :: [GMCompiledSc]
    compiled = map compileSc (preludeDefs ++ program) ++ compiledPrimitives

compiledPrimitives :: [GMCompiledSc]
compiledPrimitives = [
    ("+", 2, [Push 1, Eval, Push 1, Eval, IAdd, Update 2, Pop 2, Unwind]),
    ("-", 2, [Push 1, Eval, Push 1, Eval, ISub, Update 2, Pop 2, Unwind]),
    ("*", 2, [Push 1, Eval, Push 1, Eval, IMul, Update 2, Pop 2, Unwind]),
    ("/", 2, [Push 1, Eval, Push 1, Eval, IDiv, Update 2, Pop 2, Unwind]),
    ("primComp", 2, [Push 1, Eval, Push 1, Eval, IComp, Update 2, Pop 2, Unwind])
  ]

-- Allocates a new global node for its compiled supercombinator argument
allocateSc :: GMCompiledSc -> GMHeapState (Name, Addr)
allocateSc (name, arity, code) = (,) name <$> hAlloc (NGlobal arity code)

initialCode :: GMCode
initialCode = [PushGlobal $ Left "main", Unwind]

--------------------------------------------------------------------------------
-- Main compilation functions

compileSc :: GScDefnN -> GMCompiledSc
compileSc (name, args, body) =
  (name, length args, compileR body (zip args [0..]))

-- Generates code which instantiates the body e of a supercombinator, and then
-- proceeds to unwind the resulting stack.
compileR :: GExprN -> [(Name, Int)] -> GMCode
compileR e env = body ++ [Update n, Pop n, Unwind]
  where
    body = runReader (compilee e) (StrictEnv env)
    n = length env

compilee :: GExprN -> CMonad m GMCode
compilee (GLit (LInt n)) = return [PushInt n]
compilee (GLet NonRecursive defs e) = compileLet defs e
compilee (GLet Recursive defs e) = compileLetRec defs e
-- TODO: compilee (GBinOp binop e1 e2) = compileBinOp binop e1 e2
compilee (GVar x) = strictWrap $ inNonStrictMode $ do
 env <- askEnv
 if x `elem` map fst env
   then return [Push $ lkup env x]
   else return [PushGlobal $ Left x]
compilee e@(GApp e0 e1) = case isFullyAppliedCtor e of
  Just (t,a,exprs) -> compileFullyAppliedCtor t a exprs
  Nothing          -> case isFullyAppliedPrimitiveComparison e of
    Just (a1, a2)  -> compilePrimComp a1 a2
    Nothing        -> applicationCompilation e0 e1
-- compilee (GCase e alts) =
--   branchMode (compileCase e alts) (error "compiling case in non-strict scheme")
compilee (GPack t a) = if a == 0
  then compileFullyAppliedCtor t a []
  else return [PushGlobal $ Right (t,a)]
compilee (GPrim Eql) = strictWrap $ return [PushGlobal $ Left "primComp"]

strictWrap :: (forall m . CMonad m GMCode) -> CMonad n GMCode
strictWrap m = branchMode (fmap (++ [Eval]) m) m

applicationCompilation :: GExprN -> GExprN -> CMonad m GMCode
applicationCompilation e0 e1 = strictWrap $ inNonStrictMode $
  compilee e1 <++> compilee e0 `inShiftedEnv` 1 <++> pure [Mkap]

--------------------------------------------------------------------------------
-- Primitive integer comparison compilation

isFullyAppliedPrimitiveComparison :: GExprN -> Maybe (GExprN, GExprN)
isFullyAppliedPrimitiveComparison (GApp (GApp (GPrim Eql) a1) a2) = Just (a1,a2)
isFullyAppliedPrimitiveComparison _ = Nothing

compilePrimComp :: GExprN -> GExprN -> CMonad n GMCode
compilePrimComp a1 a2 = compilee a2 <++> compilee a1 `inShiftedEnv` 1 <++>
  branchMode (return [IComp]) (return [PushGlobal $ Left "primComp", Mkap, Mkap])

--------------------------------------------------------------------------------
-- Case expression and constructors compilation

isFullyAppliedCtor :: GExprN -> Maybe (CtorTag, CtorArity, [GExprN])
isFullyAppliedCtor e = case isPartiallyAppliedCtor e of
  res@(Just (t, a, exprs)) -> if a == length exprs then res else Nothing
  Nothing                  -> Nothing
  where
    isPartiallyAppliedCtor :: GExprN -> Maybe (CtorTag, CtorArity, [GExprN])
    isPartiallyAppliedCtor (GApp (GPack t a) e) = Just (t, a, [e])
    isPartiallyAppliedCtor (GApp e1 e2) = case isPartiallyAppliedCtor e1 of
      Just (t,a,args) -> Just (t, a, args ++ [e2])
      Nothing         -> Nothing
    isPartiallyAppliedCtor _ = Nothing

compileFullyAppliedCtor :: CtorTag -> CtorArity -> [GExprN] -> CMonad m GMCode
compileFullyAppliedCtor t a exprs =
  join <$> forM (zip (reverse exprs) [0..]) aux <++> pure [Pack t a]
  where aux (e,i) = inNonStrictMode (compilee e) `inShiftedEnv` i

-- This will always be called in strict mode
compileCase :: GExprN -> [GAlterN] -> CMonad Strict GMCode
compileCase e alts =
  compilee e <++> fmap (pure . CaseJump) (compileAlts compileAlternative alts)

compileAlts :: (GAlterN -> CMonad m (CtorTag, GMCode))
            -> [GAlterN]
            -> CMonad m [(CtorTag, GMCode)]
compileAlts comp alts = do
  env <- askEnv
  forM alts comp

compileAlternative :: GAlterN -> CMonad m (CtorTag, GMCode)
compileAlternative (GAlterB t names body) = (,) <$> pure t <*>
  (pure [Split n] <++> transformEnv (compilee body) newEnv <++> pure [Slide n])
  where
    n = length names
    newEnv env = applyAll (map (flip aUpdate)
                               (zip names [0..]))
                          (shiftEnv n env)

--------------------------------------------------------------------------------
-- Binary operation compilation

-- compileBinOp :: BinOp -> GExprN -> GExprN -> CMonad m GMCode
-- compileBinOp binop e1 e2 =
--   compilee e2 <++> compilee e1 `inShiftedEnv` 1 <++> case binop of
--     Plus       -> branchMode (return [Add])
--                              (return [PushGlobal $ Left "+", Mkap, Mkap])
--     Minus      -> branchMode (return [Sub])
--                              (return [PushGlobal $ Left "-", Mkap, Mkap])
--     Mult       -> branchMode (return [Mul])
--                              (return [PushGlobal $ Left "*", Mkap, Mkap])
--     GMachine.Syntax.Div -> branchMode (return [GMachine.Structures.Div])
--                              (return [PushGlobal $ Left "/", Mkap, Mkap])

--------------------------------------------------------------------------------
-- Let and Letrec compilationo

compileLet :: GBindersN -> GExprN -> CMonad m GMCode
compileLet = compileGenericLet (const []) compBinder
  where compBinder _ _ (e, i) = inNonStrictMode (compilee e) `inShiftedEnv` i

compileLetRec :: GBindersN -> GExprN -> CMonad m GMCode
compileLetRec = compileGenericLet (return . Alloc) compBinder
  where compBinder n newEnv (e,i) =
          transformEnv (inNonStrictMode $ compilee e) newEnv
          <++> pure [Update $ n - 1 - i]

type BinderCompiler =  forall m . Int -> (CEnv -> CEnv)
                    -> (GExprN, Int) -> CMonad m GMCode

compileGenericLet :: (Int -> GMCode)
                  -> BinderCompiler
                  -> GBindersN
                  -> GExprN
                  -> CMonad m GMCode
compileGenericLet before compBinder deffs e = undefined
-- compileGenericLet before compBinder defs e = pure (before n)
--   <++> join <$> forM (NE.zip (rhssOf defs) (0 NE.:| [1..])) (compBinder n newEnv)
--   <++> transformEnv (compilee e) newEnv
--   <++> pure [Slide n]
--   where
--     n = length defs
--     newEnv env = applyAll (map (flip aUpdate)
--                           (NE.zip (bindersOf defs) (n-1 NE.:| [n - 2..0])))
--                           (shiftEnv n env)

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
(<++>) :: CMonad m GMCode -> CMonad m GMCode -> CMonad m GMCode
m1 <++> m2 = (++) <$> m1 <*> m2
