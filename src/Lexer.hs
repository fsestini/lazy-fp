module Lexer where -- (ParseError, lexer, LangToken(..), Keyword(..), Symbol(..)) where

import System.IO
import Control.Monad
import Text.Parsec.Char
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

data LangToken = Keyword Keyword
               | Id String
               | Symbol Symbol
               | Number Int
               deriving (Show, Eq)

data Keyword = LET | LETREC | CASE | OF | IN | PACK deriving (Show, Eq)
data Symbol = PLUS | MINUS | TIMES | DIV | EQUALS | LAMBDA | ARROW
            | LEFTANGLE | RIGHTANGLE | LEFTPAREN | RIGHTPAREN
            | SEMICOLON | DOT | CURLYLEFT | CURLYRIGHT | COMMA
            deriving (Show, Eq)

lexer :: String -> Either ParseError [LangToken]
lexer = parseString $ whiteSpace >> many1 langToken

languageDef =
  emptyDef {  Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "case"
                                      , "of"
                                      , "let"
                                      , "letrec"
                                      , "in"
                                      , "Pack"
                                      ]
            , Token.reservedOpNames = ["+", "-", "*", "/", "="
                                      , "<", ">", "\\", "->", ".", "{", "}", ","
                                      ]
            }

generatedLexer = Token.makeTokenParser languageDef

parseString :: Parser a -> String -> Either ParseError a
parseString p = parse p ""

identifier :: Parser LangToken
identifier = Id <$> ((:) <$> letter <*> many alphaNum <* whiteSpace)

keyword :: Parser LangToken
keyword = Keyword <$>
  (caseTok <|> ofTok <|> letTok <|> letrecTok <|> inTok <|> packTok)
  where
    caseTok   = Token.reserved generatedLexer "case"         >> return CASE
    ofTok     = Token.reserved generatedLexer "of"           >> return OF
    letTok    = try (Token.reserved generatedLexer "let")    >> return LET
    letrecTok = try (Token.reserved generatedLexer "letrec") >> return LETREC
    inTok     = Token.reserved generatedLexer "in"           >> return IN
    packTok   = Token.reserved generatedLexer "Pack"         >> return PACK

reservedOp :: Parser LangToken
reservedOp = Symbol <$> ((Token.reservedOp generatedLexer "+" >> return PLUS)
                    <|> (Token.reservedOp generatedLexer "-"  >> return MINUS)
                    <|> (Token.reservedOp generatedLexer "*"  >> return TIMES)
                    <|> (Token.reservedOp generatedLexer "/"  >> return DIV)
                    <|> (Token.reservedOp generatedLexer "="  >> return EQUALS)
                    <|> (Token.reservedOp generatedLexer "\\" >> return LAMBDA)
                    <|> (Token.reservedOp generatedLexer "->" >> return ARROW)
                    <|> (Token.reservedOp generatedLexer "."  >> return DOT)
                    <|> (Token.reservedOp generatedLexer ","  >> return COMMA)
                    <|> (Token.semi generatedLexer            >> return SEMICOLON)
                    <|> (char '('                             >> return LEFTPAREN)
                    <|> (char ')'                             >> return RIGHTPAREN)
                    <|> (char '{'                             >> return CURLYLEFT)
                    <|> (char '}'                             >> return CURLYRIGHT)
                    <|> (Token.reservedOp generatedLexer "<"  >> return LEFTANGLE)
                    <|> (Token.reservedOp generatedLexer ">"  >> return RIGHTANGLE))

integer :: Parser LangToken
integer = (Number . fromInteger) <$> Token.integer generatedLexer

whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace generatedLexer

langToken :: Parser LangToken
langToken =  try identifier
         <|> keyword
         <|> reservedOp
         <|> integer
