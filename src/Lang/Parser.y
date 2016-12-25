{

module Lang.Parser where

import Data.List.NonEmpty
import Lang.Lexer
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
    data     { TokenData }
    where    { TokenWhere }
    NUM      { TokenNum $$ }
    VAR      { TokenSym $$ }
    CTOR     { TokenCtor $$ }
    semi     { TokenSemi }
    colon    { TokenColon }
    percent  { TokenPercent }
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

Prog : sepBy(ProgElement, percent)  { toList $1 }

ProgElement : DataDecl { Left $1 }
            | Sc       { Right $1 }

DataDecl : data CTOR colon Kind where sepBy(CtorDecl,semi)  { ($2,$4,$6) }
CtorDecl : CTOR colon Type           { ($1, generalize S.empty $3) }

Sc   : VAR list(Pat) '=' Expr                { ($1, $2, $4) }

Kind : '*'                              { KStar1 }
     | '*' '->' Kind                    { KArrow1 $3 }

Type  : AType '->' Type                      { ArrowTy $1 $3 }
      | AType                                { $1 }

AType : VAR                                  { MFree $1 }
      | CTOR list(VAR)                       { MCtor $1 (fmap MFree $2) }
      | '(' Type ')'                         { $2 }

Expr : let Bind list(SemiBind) in Expr       { LLet NonRecursive ($2 :| $3) $5 }
     | letrec Bind list(SemiBind) in Expr    { LLet Recursive ($2 :| $3) $5 }
     | '\\' list(VAR) '->' Expr              { foldr LLam $4 $2 }
     | case Expr in sepBy(Alter,semi)        { LCase $2 $4 }
     | Form                                  { $1 }

Pat : VAR                                    { PVar $1 }
    | NUM                                    { PInt $1 }
    | CTOR                                   { PCtor $1 [] }
    | '(' CTOR list1(Pat) ')'                { PCtor $2 (toList $3) }

Bind : Pat '=' Expr                          { PBinderB $1 $3 }
SemiBind : semi Bind                         { $2 }

Alter : VAR list(VAR) '->' Expr              { AlterB $1 $2 $4 }
SemiAlter : semi Alter                       { $2 }

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
parseError _ = error "parse error"
-- parseError [] = error "unexpected end of input"
-- parseError (l:ls) = show l

-- parseSupercombinators :: [String] -> [ScDefn Name]
-- parseSupercombinators = fmap $ parseSc . scanTokens

}
