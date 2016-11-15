{-# LANGUAGE GADTs #-}

module PrettyPrint.ISeq(
  ISeq,
  iStr,
  iAppend,
  iNewLine,
  iIndent,
  iDisplay,
  iConcat,
  iInterleave) where

data ISeq where
  INil :: ISeq
  IStr :: String -> ISeq
  IAppend :: ISeq -> ISeq -> ISeq
  IIndent :: ISeq -> ISeq
  INewLine :: ISeq

iNil :: ISeq
iNil = INil

iStr :: String -> ISeq
iStr = IStr

iAppend :: ISeq -> ISeq -> ISeq
iAppend = IAppend

-- new line with indentation
iNewLine :: ISeq
iNewLine = INewLine

-- indent an ISeq
iIndent :: ISeq -> ISeq
iIndent = IIndent

iConcat :: [ISeq] -> ISeq
iConcat = foldr iAppend INil

iInterleave :: ISeq -> [ISeq] -> ISeq
iInterleave iseq = iConcat . foldr interleaver []
  where
    interleaver x xs = if null xs then x : xs else x : iseq : xs

-- flatten :: [ISeq] -> String
-- flatten [] = ""
-- flatten (INil : seqs) = flatten seqs
-- flatten (IStr str : seqs) = str ++ flatten seqs
-- flatten (IAppend seq1 seq2 : seqs) = flatten $ seq1 : seq2 : seqs

-- iDisplay :: ISeq -> String
-- iDisplay seqq = flatten [seqq]

flatten :: Int -> [(ISeq, Int)] -> String
flatten _ [] = ""
flatten col ((INil, _) : seqs) = flatten col seqs
flatten col ((IStr str, indent) : seqs) = str ++ flatten col seqs
flatten col ((IAppend seq1 seq2, indent) : seqs) =
  flatten col ((seq1, col) : (seq2, col) : seqs)
flatten col ((INewLine, indent) : seqs) =
  '\n' : spaces indent ++ flatten indent seqs
  where
    spaces = flip take $ repeat ' '
flatten col ((IIndent seqq, _) : seqs) =
  flatten col ((seqq, col) : seqs)

iDisplay :: ISeq -> String
iDisplay seqq = flatten 0 [(seqq,0)]
