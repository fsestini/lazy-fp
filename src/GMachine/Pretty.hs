module GMachine.Pretty where

--- import Text.PrettyPrint.HughesPJClass
import Text.PrettyPrint

import Syntax hiding (Div)
import Heap
import GMachine.Structures

--------------------------------------------------------------------------------
-- Instructions

pInstruction :: Instruction -> Doc
pInstruction Unwind = text "Unwind"
pInstruction (PushGlobal (Left i)) = text $ "PushGlobal " ++ i
pInstruction (PushGlobal (Right (t,a))) =
  text $ "PushGlobal Pack{" ++ show t ++ "," ++ show a ++ "}"
pInstruction (PushInt i) = text $ "PushInt " ++ show i
pInstruction (Push i) = text $ "Push " ++ show i
pInstruction Mkap = text "Mkap"
pInstruction (Update i) = text $ "Update " ++ show i
pInstruction (Pop i) = text $ "Pop " ++ show i
pInstruction (Alloc i) = text $ "Alloc " ++ show i
pInstruction (Slide i) = text $ "Slide " ++ show i
pInstruction Eval = text "Eval"
pInstruction Add  = text "Add"
pInstruction Sub  = text "Sub"
pInstruction Mul  = text "Mul"
pInstruction Div  = text "Div"
pInstruction (Pack t a) = hsep [text "Pack", int t, int a]
pInstruction (CaseJump _) = text "CaseJump"
pInstruction (Split n) = text $ "Split " ++ show n
pInstruction Print = text "Print"
pInstruction Comp = text "Comp"

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
pNode s a (NGlobal n g) = hsep [text "Global", text v, parens (int n)]
  where v = head [n | (n,b) <- globals s, a == b]
pNode s a (NAp a1 a2) = hsep [text "Ap", pAddress a1, pAddress a2]
pNode s a (NInd addr) = hsep [text "Ind", pAddress addr]
pNode s a (NConstr tag addrs) =
  hsep $ [text "Ctor", int tag]
  ++ [brackets (hsep $ punctuate comma (map pAddress addrs))]

--------------------------------------------------------------------------------
-- State

pState :: GMState -> Doc
pState s = vcat [pOutput s, pStack s, pDump s, pInstructions (code s)]

--------------------------------------------------------------------------------
-- Output

pOutput :: GMState -> Doc
pOutput s = text "Output: \"" <> text (output s) <> text "\""

--------------------------------------------------------------------------------
-- Dump

pDump :: GMState -> Doc
pDump s = vcat $ text "Dump:[" : map (nest 2 . pDumpItem) (reverse . dump $ s)
             ++ [text "]"]

pDumpItem :: GMDumpItem -> Doc
pDumpItem (code, stack) = hsep [
    text "<",
    braces $ shortP 3 semi $ map pInstruction code,
    brackets $ shortP 3 comma $ map pAddress stack,
    text ">"
  ]

shortP :: Int -> Doc -> [Doc] -> Doc
shortP n separator list = hsep $ punctuate separator items
  where
    items | length list > n = take n list ++ [text "..."]
          | otherwise       = list

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
    asd (n,s) = vcat [text $ "State " ++ show n, nest 2 . pState $ s, text ""]
