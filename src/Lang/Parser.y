{

module Lang.Parser where

import Control.Monad.Except
import Data.List.NonEmpty
import Lang.Lexer (Token(..))
import Lang.Syntax
import AST
import qualified Data.Set as S
import Types.Schemes
import Types.DataDecl

import Control.Monad.Except

}

%tokentype { Token }

%token
    let      { TokenLet }
    letrec   { TokenLetRec }
    in       { TokenIn }
    of       { TokenOf }
    data     { TokenData }
    where    { TokenWhere }
    NUM      { TokenNum $$ }
    VAR      { TokenSym $$ }
    CTOR     { TokenCtor $$ }
    semi     { TokenSemi }
    colon    { TokenColon }
    case     { TokenCase }
    prim     { TokenPrimOp $$ }
    '\\'     { TokenLambda }
    '->'     { TokenArrow }
    ty       { TokenType }
    '='      { TokenEq }
    '+'      { TokenAdd }
    '-'      { TokenSub }
    '*'      { TokenMul }
    '('      { TokenLParen }
    ')'      { TokenRParen }
    '{'      { TokenLCurly }
    '}'      { TokenRCurly }

%name parseProgram
%error { parseError }

%left '+' '-'
%left '*'
%right '->'
%right in
%%

Prog : sepBy(ProgElement, semi)  { toList $1 }

ProgElement : DataDecl { Left $1 }
            | Sc       { Right $1 }

DataDecl : data CTOR colon Kind where '{' sepBy(CtorDecl,semi) '}'
                                     { ($2,$4,$7) }
CtorDecl : CTOR colon Type           { ($1, generalize S.empty $3) }

Sc   : VAR list(Pat) '=' Expr                { ($1, $2, $4) }

Kind : ty                              { KStar1 }
     | ty '->' Kind                    { KArrow1 $3 }

Type  : AType '->' Type                      { ArrowTy $1 $3 }
      | AType                                { $1 }

AType : VAR                                  { MFree $1 }
      | CTOR list(VAR)                       { MCtor $1 (fmap MFree $2) }
      | '(' Type ')'                         { $2 }

Expr : let '{' sepBy(Bind,semi) '}' in Expr  { LLet NonRecursive $3 $6 }
     | letrec '{' sepBy(Bind,semi) '}' in Expr  { LLet Recursive $3 $6 }
     | '\\' list(VAR) '->' Expr              { foldr LLam $4 $2 }
     | case Expr of '{' sepBy(Alter,semi) '}'   { LCase $2 $5 }
     | Form                                  { $1 }

Pat : VAR                                    { PVar $1 }
    | NUM                                    { PInt $1 }
    | CTOR                                   { PCtor $1 [] }
    | '(' CTOR list1(Pat) ')'                { PCtor $2 (toList $3) }

Bind : Pat '=' Expr                          { PBinderB $1 $3 }

Alter : CTOR list(VAR) '->' Expr              { AlterB $1 $2 $4 }

Form : Form '+' Form                         { LApp (LApp (LPrim Add) $1) $3 }
     | Form '-' Form                         { LApp (LApp (LPrim Sub) $1) $3 }
     | Form '*' Form                         { LApp (LApp (LPrim Mul) $1) $3 }
     | Fact                                  { $1 }

Fact : Fact Atom                             { LApp $1 $2 }
     | Atom                                  { $1 }

Atom : '(' Expr ')'                          { $2 }
     | NUM                                   { LLit (LInt $1) }
     | VAR                                   { LVar $1 }
     | CTOR                                  { LCtor $1 }
     | prim                                  { LPrim $1 }

list(p) : p list(p)                          { $1 : $2 }
        |                                    { [] }

list1(p) : p                                 { $1 :| [] }
         | p list(p)                         { $1 :| $2 }

sepBy(p,q)  : p                              { $1 :| [] }
            | p q sepBy(p,q)                 { $1 :| (toList $3) }

{

parseError :: [Token] -> a
parseError [] = error "unexpected end of input"
parseError (l:ls) = error $ show l

-- parseSupercombinators :: [String] -> [ScDefn Name]
-- parseSupercombinators = fmap $ parseSc . scanTokens

}
