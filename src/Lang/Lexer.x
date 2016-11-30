{
module Lang.Lexer (
  Token(..),
  scanTokens
) where

import Lang.Syntax
import Control.Monad.Except
}

%wrapper "basic"

$digit = 0-9
$upper = [A-Z]
$lower = [a-z]
$alpha = [a-zA-Z]
$eol   = [\n]

tokens :-

  -- Whitespace insensitive
  $eol                          ;
  $white+                       ;

  -- Comments
  "#".*                         ;

  -- Syntax
  let                           { \s -> TokenLet }
  letrec                        { \s -> TokenLetRec }
  case                          { \s -> TokenCase }
  data                          { \s -> TokenData }
  where                         { \s -> TokenWhere }
  in                            { \s -> TokenIn }
  primAdd                       { \s -> TokenPrimOp Add }
  primSub                       { \s -> TokenPrimOp Sub }
  primMul                       { \s -> TokenPrimOp Mul }
  primEql                       { \s -> TokenPrimOp Eql }
  $digit+                       { \s -> TokenNum (read s) }
  "->"                          { \s -> TokenArrow }
  \=                            { \s -> TokenEq }
  \\                            { \s -> TokenLambda }
  \;                            { \s -> TokenSemi }
  \:                            { \s -> TokenColon }
  [\+]                          { \s -> TokenAdd }
  [\-]                          { \s -> TokenSub }
  [\*]                          { \s -> TokenMul }
  \(                            { \s -> TokenLParen }
  \)                            { \s -> TokenRParen }
  $lower [$alpha $digit \_ \']* { \s -> TokenSym s }
  $upper [$alpha $digit \_ \']* { \s -> TokenCtor s }

{

data Token
  = TokenLet
  | TokenLetRec
  | TokenCase
  | TokenIn
  | TokenSemi
  | TokenLambda
  | TokenNum Int
  | TokenSym String
  | TokenPrimOp PrimOp
  | TokenCtor String
  | TokenArrow
  | TokenEq
  | TokenAdd
  | TokenSub
  | TokenMul
  | TokenLParen
  | TokenRParen
  | TokenData
  | TokenColon
  | TokenWhere
  | TokenEOF
  deriving (Eq,Show)

scanTokens :: String -> [Token]
scanTokens = alexScanTokens

}
