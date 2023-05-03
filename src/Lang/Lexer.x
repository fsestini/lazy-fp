{
module Lang.Lexer (
  Token(..),
  scanTokens
) where

import Lang.Syntax
import AST
import Control.Monad.Except
}

%wrapper "basic"

$digit = 0-9
$upper = [A-Z]
$lower = [a-z]
$alpha = [a-zA-Z]
$lf = \n  -- line feed
$cr = \r  -- carriage return
$eol_char = [$lf $cr] -- any end of line character
$not_eol_char = ~$eol_char -- anything but an end of line character
$white_char   = [\ \n\r\f\v\t]
$white_no_nl = $white_char # $eol_char

tokens :-

  $eol_char $white_no_nl*       { \s -> TokenIndent . indentation $ s }

  -- Whitespace insensitive
  $white_no_nl+                       ;

  -- Comments
  "#".*                         ;

  -- Syntax
  let                           { \s -> TokenLet }
  letrec                        { \s -> TokenLetRec }
  case                          { \s -> TokenCase }
  data                          { \s -> TokenData }
  where                         { \s -> TokenWhere }
  in                            { \s -> TokenIn }
  of                            { \s -> TokenOf }
  primAdd                       { \s -> TokenPrimOp Add }
  primSub                       { \s -> TokenPrimOp Sub }
  primMul                       { \s -> TokenPrimOp Mul }
  primEql                       { \s -> TokenPrimOp Eql }
  $digit+                       { \s -> TokenNum (read s) }
  "->"                          { \s -> TokenArrow }
  ty                            { \s -> TokenType }
  \=                            { \s -> TokenEq }
  \\                            { \s -> TokenLambda }
  \;                            { \s -> TokenSemi }
  \:                            { \s -> TokenColon }
  \%                            { \s -> TokenPercent }
  [\+]                          { \s -> TokenAdd }
  [\-]                          { \s -> TokenSub }
  [\*]                          { \s -> TokenMul }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  \{                            { \s -> TokenLCurly }
  \}                            { \s -> TokenRCurly }
  $lower [$alpha $digit \_ \']* { \s -> TokenSym s }
  $upper [$alpha $digit \_ \']* { \s -> TokenCtor s }

{

data Token
  = TokenLet
  | TokenLetRec
  | TokenCase
  | TokenIn
  | TokenOf
  | TokenSemi
  | TokenLambda
  | TokenPercent
  | TokenNum Int
  | TokenSym String
  | TokenPrimOp PrimOp
  | TokenCtor String
  | TokenType
  | TokenArrow
  | TokenEq
  | TokenAdd
  | TokenSub
  | TokenMul
  | TokenLParen
  | TokenRParen
  | TokenLCurly
  | TokenRCurly
  | TokenData
  | TokenColon
  | TokenWhere
  | TokenIndent Int
  | TokenCurlyIndent Int
  | TokenAngleIndent Int
  | TokenEOF
  deriving (Eq,Show)

indentation :: String -> Int
indentation str = 1 + (length str `div` 2)

scanTokens :: String -> [Token]
scanTokens = removeSurroundingSemi . flip funcL []
             . tokenTranslate . removeEmptyIndent . alexScanTokens

startsWithCurly :: [Token] -> Bool
startsWithCurly (TokenIndent _ : ts) = startsWithCurly ts
startsWithCurly (TokenLCurly : ts) = True
startsWithCurly _ = False

indent :: [Token] -> (Int, [Token])
indent (TokenIndent i : ts) = (i, ts)
indent ts = (1, ts)

removeEmptyIndent :: [Token] -> [Token]
removeEmptyIndent [] = []
removeEmptyIndent (TokenIndent _ : TokenIndent n : ts) =
  removeEmptyIndent (TokenIndent n : ts)
removeEmptyIndent (t : ts) = t : removeEmptyIndent ts

removeSurroundingSemi :: [Token] -> [Token]
removeSurroundingSemi ts = if head ts == TokenSemi then f (tail ts) else f ts
  where f ts = if last ts == TokenSemi then init ts else ts

tokenTranslate :: [Token] -> [Token]
tokenTranslate [] = []
tokenTranslate (TokenLet : ts) = if not (startsWithCurly ts)
  then let (i, ts') = indent ts in
    TokenLet : TokenCurlyIndent i : tokenTranslate ts'
  else tokenTranslate ts
tokenTranslate (TokenOf : ts) = if not (startsWithCurly ts)
  then let (i, ts') = indent ts in
    TokenOf : TokenCurlyIndent i : tokenTranslate ts'
  else tokenTranslate ts
tokenTranslate (TokenWhere : ts) = if not (startsWithCurly ts)
  then let (i, ts') = indent ts in
    TokenWhere : TokenCurlyIndent i : tokenTranslate ts'
  else tokenTranslate ts
tokenTranslate (TokenIndent i : ts) = TokenAngleIndent i : tokenTranslate ts
tokenTranslate (t : ts) = t : tokenTranslate ts

funcL :: [Token] -> [Int] -> [Token]
funcL tk@(TokenAngleIndent n : ts) (m : ms)
  | m == n = TokenSemi : funcL ts (m : ms)
  | n < m  = TokenRCurly : funcL tk ms
funcL (TokenAngleIndent 1 : ts) [] = TokenSemi : funcL ts []
funcL (TokenAngleIndent n : ts) ms = funcL ts ms
funcL (TokenCurlyIndent n : ts) (m : ms)
  | n > m = TokenLCurly : funcL ts (n : m : ms)
funcL (TokenCurlyIndent n : ts) []
  | n > 0 = TokenLCurly : funcL ts [n]
funcL (TokenCurlyIndent n : ts) ms = funcL (TokenAngleIndent n : ts) ms
funcL (TokenRCurly : ts) (0 : ms) = TokenRCurly : funcL ts ms
funcL (TokenRCurly : ts) ms = error "funcL"
funcL (TokenLCurly : ts) ms = TokenLCurly : funcL ts (0 : ms)
funcL (t:ts) ms = t : funcL ts ms
funcL [] [] = []
funcL [] (m:ms) | m /= 0 = TokenRCurly : funcL [] ms
funcL _ _ = error "funcL"

}
