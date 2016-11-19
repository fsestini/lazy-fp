module GMachine.Structures where

import Heap
import Syntax

data Instruction = Unwind
                 | PushGlobal Name
                 | PushInt Int
                 | Push Int
                 | Mkap
                 | Update Int
                 | Pop Int
                 | Alloc Int
                 | Slide Int
                 deriving (Eq,Show)

data Node = NNum Int
          | NAp Addr Addr
          | NGlobal Int GMCode  -- Number of arguments + code to execute
                                -- This replaces the supercombinator nodes,
                                -- which instead held a template of the superc.
          | NInd Addr
          deriving (Eq, Show)

type GMStats = Int
statInitial = 0 :: Int
statIncSteps s = s + 1
statGetSteps s = s

type GMCode = [Instruction]
type GMStack = [Addr]
type GMHeap = Heap Node
type GMGlobals = [(Name, Addr)]

-- State of the G-Machine
data GMState = GMState {
  code :: GMCode,
  stack :: GMStack,
  heap :: GMHeap,
  globals :: GMGlobals,
  stats :: GMStats
}
