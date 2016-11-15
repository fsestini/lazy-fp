module Parser(syntax) where

import Control.Monad (void)

import Syntax
import Lexer
import Text.Parsec
import Text.Parsec.Prim
import Text.Parsec.Combinator

type Parser a = Parsec [LangToken] () a

satisfy :: (LangToken -> Bool) -> Parser LangToken
satisfy f = tokenPrim show (\x y z -> x) (\c -> if f c then Just c else Nothing)

tok :: LangToken -> Parser LangToken
tok t = Parser.satisfy (== t) <?> show t

syntax :: [LangToken] -> CoreProgram
syntax tokens = case parse parseProgram "" tokens of
  Right program -> program
  Left err -> error $ show err

semicolon :: Parser ()
semicolon = void $ tok (Symbol SEMICOLON)

parseProgram :: Parser CoreProgram
parseProgram = parseSuperCombinator `sepBy1` semicolon

parseId :: Parser Name
parseId = do
  (Id name) <- Parser.satisfy isId
  return name
  where
    isId :: LangToken -> Bool
    isId (Id _) = True
    isId _ = False

parseInt :: Parser Int
parseInt = do
  (Number n) <- Parser.satisfy isNum
  return n
  where
    isNum (Number _) = True
    isNum _ = False

parseSuperCombinator :: Parser CoreScDefn
parseSuperCombinator = (,,)
                    <$> parseId
                    <*> many parseId
                    <*  tok (Symbol EQUALS)
                    <*> parseExpression

parseExpression :: Parser CoreExpr
parseExpression =  parseLet
               <|> parseLetRec
               <|> parseCase
               <|> parseLambda
               <|> parseExpr1

parseLet :: Parser CoreExpr
parseLet =  try $ ELet NonRecursive
        <$  tok (Keyword LET)
        <*> parseDefinitions
        <*  tok (Keyword IN)
        <*> parseExpression

parseLetRec :: Parser CoreExpr
parseLetRec =  try $ ELet Recursive
           <$  tok (Keyword LET)
           <*> parseDefinitions
           <*  tok (Keyword IN)
           <*> parseExpression

parseCase :: Parser CoreExpr
parseCase = ECase
         <$  tok (Keyword CASE)
         <*> parseExpression
         <*  tok (Keyword OF)
         <*> parseAlternatives

parseLambda :: Parser CoreExpr
parseLambda =  ELam
           <$  tok (Symbol LAMBDA)
           <*> many1 parseId
           <*  tok (Symbol DOT)
           <*> parseExpression

-- type Alter a = (CtorTag, [a], Expr a)
-- type CoreAlt = Alter Name

parseAlternatives :: Parser [CoreAlt]
parseAlternatives = parseAlternative `sepBy1` semicolon

parseAlternative :: Parser CoreAlt
parseAlternative =  (,,)
                <$  tok (Symbol LEFTANGLE)
                <*> parseInt
                <*  tok (Symbol RIGHTANGLE)
                <*> many parseId
                <*  tok (Symbol ARROW)
                <*> parseExpression

parseAExp :: Parser CoreExpr
parseAExp =  (EVar <$> parseId)
         <|> (ENum <$> parseInt)
         <|> parseCtor
         <|> between (tok (Symbol LEFTPAREN))
                     (tok (Symbol RIGHTPAREN))
                     parseExpression
  where
    parseCtor =  ECtor
             <$  tok (Keyword PACK)
             <*  tok (Symbol CURLYLEFT)
             <*> parseInt
             <*  tok (Symbol COMMA)
             <*> parseInt
             <*  tok (Symbol CURLYRIGHT)

parseDefinitions :: Parser [(Name, CoreExpr)]
parseDefinitions = parseDefinition `sepBy1` semicolon

parseDefinition :: Parser (Name, CoreExpr)
parseDefinition = (,) <$> parseId <* tok (Symbol EQUALS) <*> parseExpression

{-
expr --> expr1

expr1  --> expr2 expr1c
expr1c --> + expr1
        |  - expr1
        |  epsilon
expr2  --> expr3 expr2c
expr2c --> * expr2
        |  / expr2
        |  epsilon
expr3  --> aexpr1 ... aexprn
-}

parseExpr1 :: Parser CoreExpr
parseExpr1 = parseExpr2 >>= parseExpr1c
  where
    parseExpr1c :: CoreExpr -> Parser CoreExpr
    parseExpr1c expr2 = binPlus <|> binMinus <|> return expr2
      where
        binPlus  = EBinOp Plus  expr2 <$ tok (Symbol PLUS)  <*> parseExpr1
        binMinus = EBinOp Minus expr2 <$ tok (Symbol MINUS) <*> parseExpr1

parseExpr2 :: Parser CoreExpr
parseExpr2 = parseExpr3 >>= parseExpr2c
  where
    parseExpr2c :: CoreExpr -> Parser CoreExpr
    parseExpr2c expr3 = binMult <|> binDiv <|> return expr3
      where
        binMult = EBinOp Mult expr3 <$ tok (Symbol TIMES) <*> parseExpr2
        binDiv  = EBinOp Div  expr3 <$ tok (Symbol DIV)   <*> parseExpr2

parseExpr3 :: Parser CoreExpr
parseExpr3 = foldl1 EAp <$> many1 parseAExp

-- parseProgram :: Parser CoreProgram
-- parseProgram
