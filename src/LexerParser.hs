module LexerParser where

import System.IO
import Control.Monad
import Text.Parsec.Char
import Text.ParserCombinators.Parsec hiding (token)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Syntax

languageDef =
  emptyDef {  Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "case"
                                      , "of"
                                      , "let"
                                      , "letrec"
                                      , "in"
                                      , "Pack"
                                      , "primComp"
                                      ]
            , Token.reservedOpNames = ["+", "-", "*", "/", "="
                                      , "\\", "->", ".", ","
                                      ]
            }

lexer = Token.makeTokenParser languageDef

identifier = Token.identifier lexer
reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
parens     = Token.parens     lexer
curly      = Token.braces     lexer
angle      = Token.angles     lexer
integer    = (read :: String -> Int) <$> (many1 digit <* whiteSpace)
dot        = Token.dot        lexer
semicolon  = Token.semi       lexer
whiteSpace = Token.whiteSpace lexer
commaSep   = Token.commaSep   lexer
semiSep    = Token.semiSep    lexer
comma      = Token.comma      lexer

-- Symbols
equalsSym = reservedOp "="

parseString :: Parser a -> String -> a
parseString p str = case parse p "" str of
                  Left err -> error (show err)
                  Right x  -> x

parseProgram :: Parser CoreProgram
parseProgram = semiSep parseSuperCombinator

parseSuperCombinator :: Parser CoreScDefn
parseSuperCombinator = (,,)
                    <$> identifier
                    <*> many identifier
                    <*  equalsSym
                    <*> parseExpression

parseLet :: Parser CoreExpr
parseLet =  ELet NonRecursive
        <$  reserved "let"
        <*> parseDefinitions
        <*  reserved "in"
        <*> parseExpression

parseLetRec :: Parser CoreExpr
parseLetRec =  ELet Recursive
           <$  reserved "letrec"
           <*> parseDefinitions
           <*  reserved "in"
           <*> parseExpression

parseExpression :: Parser CoreExpr
parseExpression =  parseLet
               <|> parseLetRec
               <|> parseCase
               <|> parseLambda
               <|> parseExpr1
               -- <|> parsePrimComp

-- parsePrimComp :: Parser CoreExpr
-- parsePrimComp = string "primComp" >> return EPrimComp

parseCase :: Parser CoreExpr
parseCase =  ECase
         <$  reserved "case"
         <*> parseExpression
         <*  reserved "of"
         <*> parseAlternatives

parseLambda :: Parser CoreExpr
parseLambda =  ELam
           <$  reservedOp "\\"
           <*> many1 identifier
           <*  dot
           <*> parseExpression

-- type Alter a = (CtorTag, [a], Expr a)
-- type CoreAlt = Alter Name

parseAlternatives :: Parser [CoreAlt]
parseAlternatives = semiSep parseAlternative

parseAlternative :: Parser CoreAlt
parseAlternative =  (,,)
                <$> angle integer
                <*> many identifier
                <*  reservedOp "->"
                <*> parseExpression

parseAExp :: Parser CoreExpr
parseAExp =  (EVar <$> identifier)
         <|> (ENum <$> integer)
         <|> (reserved "primComp" >> return EPrimComp)
         <|> parseCtor
         <|> parens parseExpression
  where
    parseCtor =  uncurry ECtor
             <$  reserved "Pack"
             <*> curly ((,) <$> integer <* comma <*> integer)

parseDefinitions :: Parser [(Name, CoreExpr)]
parseDefinitions = semiSep parseDefinition

parseDefinition :: Parser (Name, CoreExpr)
parseDefinition = (,) <$> identifier <* equalsSym <*> parseExpression

-- parseBinOp :: Parser CoreExpr
-- parseBinOp = buildExpressionParser aOperators parseExpression
--
-- aOperators = [ [Infix (reservedOp "*" >> return (EBinOp Mult))  AssocLeft,
--                 Infix (reservedOp "/" >> return (EBinOp Div))   AssocLeft]
--              , [Infix (reservedOp "+" >> return (EBinOp Plus))  AssocLeft,
--                 Infix (reservedOp "-" >> return (EBinOp Minus)) AssocLeft]
--              ]

-- {-
-- expr --> expr1
--
-- expr1  --> expr2 expr1c
-- expr1c --> + expr1
--         |  - expr1
--         |  epsilon
-- expr2  --> expr3 expr2c
-- expr2c --> * expr2
--         |  / expr2
--         |  epsilon
-- expr3  --> aexpr1 ... aexprn
-- -}
--
parseExpr1 :: Parser CoreExpr
parseExpr1 = parseExpr2 >>= parseExpr1c
  where
    parseExpr1c :: CoreExpr -> Parser CoreExpr
    parseExpr1c expr2 = binPlus <|> binMinus <|> return expr2
      where
        binPlus  = EBinOp Plus  expr2 <$ (char '+' >> whiteSpace) <*> parseExpr1
        binMinus = EBinOp Minus expr2 <$ (char '-' >> whiteSpace) <*> parseExpr1

parseExpr2 :: Parser CoreExpr
parseExpr2 = parseExpr3 >>= parseExpr2c
  where
    parseExpr2c :: CoreExpr -> Parser CoreExpr
    parseExpr2c expr3 = binMult <|> binDiv <|> return expr3
      where
        binMult = EBinOp Mult expr3 <$ (char '*' >> whiteSpace) <*> parseExpr2
        binDiv  = EBinOp Div  expr3 <$ (char '/' >> whiteSpace) <*> parseExpr2

parseExpr3 :: Parser CoreExpr
parseExpr3 = foldl1 EAp <$> many1 (try parseAExp)
