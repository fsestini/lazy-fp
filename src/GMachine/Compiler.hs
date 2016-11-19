module GMachine.Compiler where

import Control.Monad.State.Lazy (runState)
import Data.Tuple (swap)
import Data.Maybe (fromMaybe)
import Control.Arrow (second)
import Control.Monad (forM)

import GMachine.Structures
import Syntax
import Heap
import AssocList

type GMHeapState a = HeapState Node a
type GMCompiledSc = (Name, Int, GMCode)

-- Turns a program into an initial state for the G-Machine. The initial code
-- sequence finds the global main and then evaluates it. The heap is initialized
-- so that it contains a node for each global declared.
compile :: CoreProgram -> GMState
compile program = GMState initialCode [] heap globals statInitial
  where
    (heap, globals) = buildInitialHeap program

buildInitialHeap :: CoreProgram -> (GMHeap, GMGlobals)
buildInitialHeap program = swap $ runState (forM compiled allocateSc) hInitial
  where
    compiled :: [GMCompiledSc]
    compiled = map compileSc (preludeDefs ++ program) ++ compiledPrimitives

compiledPrimitives :: [GMCompiledSc]
compiledPrimitives = []

-- Allocates a new global node for its compiled supercombinator argument
allocateSc :: GMCompiledSc -> GMHeapState (Name, Addr)
allocateSc (name, arity, code) = (,) name <$> hAlloc (NGlobal arity code)

initialCode :: GMCode
initialCode = [PushGlobal "main", Unwind]

compileSc :: CoreScDefn -> GMCompiledSc
compileSc (name, args, body) =
  (name, length args, compileR body (zip args [0..]))

compileR :: CoreExpr -> [(Name, Int)] -> GMCode
compileR e env = compileC e env ++ [Update n, Pop n, Unwind]
  where n = length env

lkup :: [(Name, Int)] -> Name -> Int
lkup rho x = fromMaybe (error err) $ lookup x rho
  where err = "cannot lookup " ++ show x ++ " in the compiler"

compileC :: CoreExpr -> [(Name, Int)] -> GMCode
compileC (EVar x) env | x `elem` map fst env = [Push $ lkup env x]
                      | otherwise            = [PushGlobal x]
compileC (ENum n) env = [PushInt n]
compileC (EAp e0 e1) env =
  compileC e1 env ++ compileC e0 (shiftEnv 1 env) ++ [Mkap]
compileC (ELet NonRecursive defs e) env = compileLet    defs e env
compileC (ELet Recursive defs e) env    = compileLetRec defs e env
compileC (EBinOp e1 e2 e3) env = undefined
compileC (ECtor e1 e2) env = undefined
compileC (ECase e1 e2) env = undefined
compileC (ELam e1 e2) env = undefined

compileLet :: [(Name, CoreExpr)] -> CoreExpr -> [(Name, Int)] -> GMCode
compileLet defs e env =
  concatMap aux (zip exprs [0..]) ++ compileC e newEnv ++ [Slide n]
  where
    binders = map fst defs
    exprs = map snd defs
    n = length exprs
    aux (e, i) = compileC e (shiftEnv i env)
    newEnv = applyAll (map (flip aUpdate) (zip binders [n-1..0]))
                      (shiftEnv n env)

compileLetRec :: [(Name, CoreExpr)] -> CoreExpr -> [(Name, Int)] -> GMCode
compileLetRec defs e env = [Alloc n] ++
  concatMap aux (zip exprs [n-1..0]) ++ compileC e newEnv ++ [Slide n]
  where
    binders = map fst defs
    exprs = map snd defs
    n = length exprs
    aux (e, i) = compileC e newEnv ++ [Update i]
    newEnv = applyAll (map (flip aUpdate) (zip binders [n-1..0]))
                      (shiftEnv n env)

shiftEnv :: Int -> [(Name, Int)] -> [(Name, Int)]
shiftEnv n = fmap (second (+ n))

applyAll :: [a -> a] -> a -> a
applyAll fs x = foldl (\ x f -> f x) x fs
