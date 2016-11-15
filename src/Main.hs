{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ImpredicativeTypes #-}

module Main where

import Heap
import SystemF
import Lexer
import Parser
import Compiler

main :: IO ()
main = putStrLn "Hello, Haskell!"

{-
Nat = forall X . X -> (X -> X) -> X

zero = /\ X . \ z f . z
succ : Nat -> Nat
succ = \n : Nat . /\ X . \ z f . f (n X z f)

-}

tail' :: [a] -> [a]
tail' = foldr (const id) []

data PNat = PZero | PSucc PNat deriving Show

type Nat = forall x . x -> (x -> x) -> x
type NatD = forall x . x -> (Nat -> x) -> x

toPrintable :: Nat -> PNat
toPrintable n = n PZero PSucc

fromPrintable :: PNat -> Nat
fromPrintable PZero = zero'
fromPrintable (PSucc n) = succ' (fromPrintable n)

zero' :: Nat
zero' = const

succ' :: Nat -> Nat
succ' n z s = s (n z s)

destructor :: Nat -> NatD
destructor n = n g1' g2'

g1' :: NatD
g1' = const

g2' :: NatD -> NatD
g2' n z s = s (n zero' succ')

pred' :: Nat -> Nat
pred' n = destructor n zero' id

qweqwe :: String -> Node
qweqwe str = hLookup heap (head stack)
  where
    (Right lexed) = lexer str
    parsed = syntax lexed
    compiled = compile parsed
    evald = Compiler.eval compiled
    (stack,_,heap,_,_) = last evald

test =
  "pair x y f = f x y ;\nfst p = p K ;\nsnd p = p K1 ;\n" ++
  "f x y = letrec a = pair x b ; b = pair y a in fst (snd (snd (snd a))) ;\n" ++
  "main = f 3 4"
