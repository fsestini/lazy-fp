module GMachine.Structures where

import Heap
import Syntax

type GlobalName = Either Name (CtorTag, CtorArity)

data Instruction = Unwind
                 | PushGlobal GlobalName
                 | PushInt Int
                 | Push Int
                 | Mkap
                 | Update Int
                 | Pop Int
                 | Alloc Int
                 | Slide Int
                 | Eval
                 | Add | Sub | Mul | Div
                 | Pack CtorTag CtorArity
                 | CaseJump [(Int, GMCode)]
                 | Split Int
                 | Print
                 deriving (Eq,Show)

data Node = NNum Int
          | NAp Addr Addr
          | NGlobal Int GMCode  -- Number of arguments + code to execute
                                -- This replaces the supercombinator nodes,
                                -- which instead held a template of the superc.
          | NInd Addr
          | NConstr CtorTag [Addr]
          deriving (Eq, Show)

type GMStats = Int
statInitial = 0 :: Int
statIncSteps s = s + 1
statGetSteps s = s

type GMCode    = [Instruction]
type GMStack   = [Addr]
type GMHeap    = Heap Node
type GMGlobals = [(Name, Addr)]
type GMDump    = [GMDumpItem]
type GMOutput  = String

type GMDumpItem = (GMCode, GMStack)

-- State of the G-Machine
data GMState = GMState {
  output  :: GMOutput,
  code    :: GMCode,
  stack   :: GMStack,
  dump    :: GMDump,
  heap    :: GMHeap,
  globals :: GMGlobals,
  stats   :: GMStats
}
