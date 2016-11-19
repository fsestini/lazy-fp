module GMachine.Pretty where

--- import Text.PrettyPrint.HughesPJClass
import Text.PrettyPrint

import Syntax
import Heap
import GMachine.Structures

data Tree a = Leaf a | Node (Tree a) (Tree a) deriving Show

-- instance (Pretty a) => Pretty (Tree a) where
--   pPrint (Leaf a) = text "Leaf: " <> pPrint a
--   pPrint (Node tree1 tree2) = vcat [ text "Node:"
--                                    , nest 2 (pPrint tree1)
--                                    , nest 2 (pPrint tree2)]
--

--------------------------------------------------------------------------------
-- Instructions

pInstruction :: Instruction -> Doc
pInstruction Unwind = text "Unwind"
pInstruction (PushGlobal i) = text $ "PushGlobal " ++ i
pInstruction (PushInt i) = text $ "PushInt " ++ show i
pInstruction (Push i) = text $ "Push " ++ show i
pInstruction Mkap = text "Mkap"
pInstruction (Slide i) = text $ "Slide " ++ show i

pInstructions :: GMCode -> Doc
pInstructions = hsep . punctuate semi . fmap pInstruction

--------------------------------------------------------------------------------
-- Stack

pAddress :: Addr -> Doc
pAddress a = text $ "#" ++ show a

pStack :: GMState -> Doc
pStack s = vcat $ text "Stack:[" :
                  map (nest 2 . showStackItem s) (reverse (stack s)) ++
                  [text "]"]

showStackItem :: GMState -> Addr -> Doc
showStackItem s a = cat [pAddress a, text ": ", pNode s a (hLookup (heap s) a)]

pNode :: GMState -> Addr -> Node -> Doc
pNode s a (NNum n) = int n
pNode s a (NGlobal n g) = cat [text "Global ", text v]
  where v = head [n | (n,b) <- globals s, a == b]
pNode s a (NAp a1 a2) = hsep [text "Ap", pAddress a1, pAddress a2]

--------------------------------------------------------------------------------
-- State

pState :: GMState -> Doc
pState s = vcat [pStack s, pInstructions (code s)]

--------------------------------------------------------------------------------
-- Supercombinators

pSC :: GMState -> (Name, Addr) -> Doc
pSC s (name, addr) = vcat [
    text $ "Code for " ++ name,
    pInstructions instr
  ]
  where
    (NGlobal _ instr) = hLookup (heap s) addr

--------------------------------------------------------------------------------
-- Stats

pStats :: GMState -> Doc
pStats s = hsep [text "Steps taken =", int $ statGetSteps (stats s)]

--------------------------------------------------------------------------------
-- Results

pResults :: [GMState] -> Doc
pResults states@(s : ss) =
  vcat $  text "Superc. definitions" : map (nest 2 . pSC s) (globals s)
      ++  text "State transitions"   : map (nest 2 . asd) (zip [1..] states)
      ++ [text "Stats: "            <> pStats (last states)]
  where
    asd :: (Int, GMState) -> Doc
    asd (n,s) = vcat [text $ "State " ++ show n, nest 2 . pState $ s]
