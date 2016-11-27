module GMachine.Main where

import Syntax
import GMachine.Compiler
import GMachine.Evaluator
import GMachine.Structures
import LexerParser
import GMachine.Pretty
import Heap

import Control.Monad.State.Lazy
import Text.PrettyPrint

runShow :: String -> String
runShow programText = render $ pResults states
  where
    parsed = parseString parseProgram programText
    initialState = compile parsed
    states = evalState eval initialState

run :: String -> Int
run programText = n
  where
    parsed = parseString parseProgram programText
    initialState = compile parsed
    states = evalState eval initialState
    final = last states
    (NNum n) = hLookup (heap final) (head $ stack final)

compileString :: String -> GMCode
compileString = code . compile . parseString parseProgram
