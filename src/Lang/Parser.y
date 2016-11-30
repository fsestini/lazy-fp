{

module Lang.Parser where

import Data.List.NonEmpty
import Lang.Lexer
import Lang.Syntax

import Control.Monad.Except

}

%tokentype { Token }

%token
    let      { TokenLet }
    letrec   { TokenLetRec }
    in       { TokenIn }
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
    '='      { TokenEq }
    '+'      { TokenAdd }
    '-'      { TokenSub }
    '*'      { TokenMul }
    '('      { TokenLParen }
    ')'      { TokenRParen }

%name parseProgram
%error { parseError }

%left '+' '-'
%left '*'
%%

Prog : list(ProgElement)  { $1 }

ProgElement : DataDecl { Left $1 }
            | Sc       { Right $1 }

DataDecl : data CTOR where sepBy(CtorDecl,semi)  { ($2,$4) }
CtorDecl : CTOR colon sepBy(CTOR,'->')           { ($1, $3) }

Sc   : VAR list(Pat) '=' Expr                { ($1, $2, $4) }

Expr : let Bind list(SemiBind) in Expr       { Let NonRecursive ($2 :| $3) $5 }
     | letrec Bind list(SemiBind) in Expr    { Let Recursive ($2 :| $3) $5 }
     | '\\' list(VAR) '->' Expr              { Lam $2 $4 }
     | case Expr in Alter list(SemiAlter)    { Case $2 ($4 :| $5) }
     | Form                                  { $1 }

Pat : VAR                                    { PVar $1 }
    | NUM                                    { PInt $1 }
    | CTOR                                   { PCtor $1 [] }
    | '(' CTOR list1(Pat) ')'                { PCtor $2 (toList $3) }

Bind : VAR '=' Expr                          { ($1, $3) }
SemiBind : semi Bind                         { $2 }

Alter : VAR list(VAR) '->' Expr              { ($1, $2, $4) }
SemiAlter : semi Alter                       { $2 }

Form : Form '+' Form                         { App (App (PrimOp Add) $1) $3 }
     | Form '-' Form                         { App (App (PrimOp Sub) $1) $3 }
     | Form '*' Form                         { App (App (PrimOp Mul) $1) $3 }
     | Fact                                  { $1 }

Fact : Fact Atom                             { App $1 $2 }
     | Atom                                  { $1 }

Atom : '(' Expr ')'                          { $2 }
     | NUM                                   { Lit (LInt $1) }
     | VAR                                   { Var $1 }
     | CTOR                                  { Ctor $1 }
     | prim                                  { PrimOp $1 }

list(p) : p list(p)                          { $1 : $2 }
        |                                    { [] }

list1(p) : p                                 { $1 :| [] }
         | p list(p)                         { $1 :| $2 }

sepBy(p,q)  : p                              { $1 :| [] }
            | p q sepBy(p,q)                 { $1 :| (toList $3) }

{

parseError :: [Token] -> a
parseError _ = error "Parse error"

-- parseSupercombinators :: [String] -> [ScDefn Name]
-- parseSupercombinators = map $ parseSc . scanTokens

}
