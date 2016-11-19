module GMachine.Compiler where

import Control.Monad.State.Lazy (runState)
import Data.Tuple (swap)
import Data.Maybe (fromMaybe)
import Control.Arrow (second)
import Control.Monad (forM)

import GMachine.Structures
import Syntax
import Heap

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
compileR e env = compileC e env ++ [Slide (length env + 1), Unwind]

lkup :: [(Name, Int)] -> Name -> Int
lkup rho x = fromMaybe (error err) $ lookup x rho
  where err = "cannot lookup " ++ show x ++ " in the compiler"

compileC :: CoreExpr -> [(Name, Int)] -> GMCode
compileC (EVar x) env | x `elem` map fst env = [Push $ lkup env x]
                      | otherwise            = [PushGlobal x]
compileC (ENum n) env = [PushInt n]
compileC (EAp e0 e1) env =
  compileC e1 env ++ compileC e0 (shiftEnv 1 env) ++ [Mkap]
compileC (EBinOp e1 e2 e3) env = undefined
compileC (ECtor e1 e2) env = undefined
compileC (ELet e1 e2 e3) env = undefined
compileC (ECase e1 e2) env = undefined
compileC (ELam e1 e2) env = undefined

shiftEnv :: Int -> [(Name, Int)] -> [(Name, Int)]
shiftEnv n = fmap (second (+ n))
