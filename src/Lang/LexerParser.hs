module Lang.LexerParser where

import Lang.Syntax

import Data.Either
import Data.List
import Data.List.Split hiding (chunk)
import System.IO
import Control.Monad
import Text.Parsec.Char
import Text.ParserCombinators.Parsec hiding (token)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Data.Char (isUpper, isSpace)

chunk :: String -> [String]
chunk = map (intercalate "\n")
  . filter (not . null)
  . splitOn [""]
  . map (\s -> if isWhiteString s then "" else s)
  . splitOn "\n"
  where isWhiteString = not . any (not . isSpace)

languageDef =
  emptyDef {  Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "case"
                                      , "of"
                                      , "let"
                                      , "letrec"
                                      , "in"
                                      , "data"
                                      , "where"
                                      , "comp"
                                      , "plus"
                                      , "sub"
                                      , "mult"
                                      , "div"
                                      ]
            , Token.reservedOpNames = ["=", "^", "->", ".", ",", ":"
                                      ]
            }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
curly      = Token.braces     lexer
angle      = Token.angles     lexer
integer    = fromInteger <$> Token.integer lexer
dot        = Token.dot        lexer
semicolon  = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer
commaSep   = Token.commaSep   lexer
semiSep    = Token.semiSep    lexer
semiSep1   = Token.semiSep1   lexer
comma      = Token.comma      lexer

-- Symbols
equalsSym = reservedOp "="

parseString :: Parser a -> String -> a
parseString p str = case parse p "" str of
                  Left err -> error (show err)
                  Right x  -> x

parseAdtOrSc :: Parser (Either AdtDecl LangScDefn)
parseAdtOrSc = (Left <$> parseAdtDecl) <|> (Right <$> parseSuperCombinator)

parseProgram :: String -> LangProgram
parseProgram = partitionEithers . map aux . chunk
  where
    aux :: String -> Either AdtDecl LangScDefn
    aux = parseString parseAdtOrSc

parseSuperCombinator :: Parser LangScDefn
parseSuperCombinator = (,,)
                    <$> identifier
                    <*> many identifier
                    <*  equalsSym
                    <*> parseExpression

parseAdtDecl :: Parser AdtDecl
parseAdtDecl = do
  reserved "data"
  name <- identifier
  reserved "where"
  ctors <- parseAdtCtors
  return (name, ctors)

parseAdtCtors :: Parser [AdtCtor]
parseAdtCtors =  semiSep1 parseAdtCtor

parseCtorName :: Parser CtorName
parseCtorName = do
  ident <- identifier
  if isUpper (head ident)
    then return ident
    else fail "ctor not uppercase"

parseAdtCtor :: Parser AdtCtor
parseAdtCtor = do
  name <- parseCtorName
  reservedOp ":"
  types <- sepBy1 parseCtorName (reservedOp "->")
  return (name, types)

parseLet :: Parser LangExpr
parseLet =  ELet NonRecursive
        <$  reserved "let"
        <*> parseDefinitions
        <*  reserved "in"
        <*> parseExpression

parseLetRec :: Parser LangExpr
parseLetRec =  ELet Recursive
           <$  reserved "letrec"
           <*> parseDefinitions
           <*  reserved "in"
           <*> parseExpression

parseExpression :: Parser LangExpr
parseExpression =  parseLet
               <|> parseLetRec
               <|> parseCase
               <|> parseLambda
               <|> foldl1 EAp <$> many1 (try parseAExp)

parseCase :: Parser LangExpr
parseCase =  ECase
         <$  reserved "case"
         <*> parseExpression
         <*  reserved "of"
         <*> parseAlternatives

parseLambda :: Parser LangExpr
parseLambda =  ELam
           <$  reservedOp "^"
           <*> many1 identifier
           <*  dot
           <*> parseExpression

parseAlternatives :: Parser [LangAlter]
parseAlternatives = semiSep parseAlternative

parseAlternative :: Parser LangAlter
parseAlternative =  (,,)
                <$> parseCtorName
                <*> many identifier
                <*  reservedOp "->"
                <*> parseExpression

parsePrimitive :: Parser LangExpr
parsePrimitive =  (reserved "comp" >> return (EPrimitive PrimComp))
              <|> (reserved "plus" >> return (EPrimitive PrimSum))
              <|> (reserved "sub"  >> return (EPrimitive PrimSub))
              <|> (reserved "mult" >> return (EPrimitive PrimMul))
              <|> (reserved "div"  >> return (EPrimitive PrimDiv))

parseAExp :: Parser LangExpr
parseAExp =  (EVar <$> identifier)
         <|> (ENum <$> integer)
         <|> parsePrimitive
         <|> parseCtor
         <|> parens parseExpression
  where
    parseCtor = ECtor <$> parseCtorName

parseDefinitions :: Parser [(Name, LangExpr)]
parseDefinitions = semiSep parseDefinition

parseDefinition :: Parser (Name, LangExpr)
parseDefinition = (,) <$> identifier <* equalsSym <*> parseExpression
