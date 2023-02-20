{
module Parser.Parser (parseProg) where

import Language
import Parser.Lexer
}

%name parse1
%tokentype { Token }
%error { parseError }

%token
    int         { TokenInt $$ }
    name        { TokenName $$ }
    '['         { TokenSymb "[" }
    ']'         { TokenSymb "]" }
    '+'         { TokenSymb "+" }
    '-'         { TokenSymb "-" }
    '*'         { TokenSymb "*" }
    '/'         { TokenSymb "/" }
    '%'         { TokenSymb "%" }
    '('         { TokenSymb "(" }
    ')'         { TokenSymb ")" }
    
    '='         { TokenSymb "=" }
    "!="        { TokenSymb "!=" }
    "<="        { TokenSymb "<=" }
    ">="        { TokenSymb ">=" }
    '<'         { TokenSymb "<" }
    '>'         { TokenSymb ">" }
    '!'         { TokenSymb "!" }
    
    "||"        { TokenSymb "||" }
    "&&"        { TokenSymb "&&" }
    "==>"       { TokenSymb "==>" }

    ":="        { TokenSymb ":=" }
    ','         { TokenSymb "," }
    ';'         { TokenSymb ";" }
    "if"        { TIf }
    "then"      { TThen }
    "else"      { TElse }
    "end"       { TEnd }
    "while"     { TWhile }
    "do"        { TDo }
    "inv"       { TInv }
    "forall"    { TForall }
    "exists"    { TExists }
    "pre"       { TPre }
    "post"      { TPost }
    "program"   { TProgram }
    "is"        { TIs }

%left '+' '-'
%left '*' '/' '%'

%left "exists"
%left "forall"
%left "==>"
%left "||"
%left "&&"
%left '!'
%left '(' ')'

%%

prog :: { Program }
    : "program" name "pre" assn "post" assn "is" block "end" { ($2, [$4], $8, [$6]) }

arithExp :: { ArithExp }
    : int { Num $1 }
    | name { Var $1 }
    | '-' arithExp { Sub (Num 0) $2 }
    | name '[' arithExp ']' { Read $1 $3 }
    | arithExp '+' arithExp { Add $1 $3 }
    | arithExp '-' arithExp { Sub $1 $3 }
    | arithExp '*' arithExp { Mul $1 $3 }
    | arithExp '/' arithExp { Div $1 $3 }
    | arithExp '%' arithExp { Mod $1 $3 }
    | '(' arithExp ')'      { Parens $2 }

comp :: { Comparison }
    : arithExp '=' arithExp { Eq $1 $3 }
    | arithExp "!=" arithExp { Neq $1 $3 }
    | arithExp "<=" arithExp { Le $1 $3 }
    | arithExp ">=" arithExp { Ge $1 $3 }
    | arithExp '<' arithExp { Lt $1 $3 }
    | arithExp '>' arithExp { Gt $1 $3 }

assn :: { Assertion }
    : comp { ACmp $1 } 
    | '!' assn { ANot $2 }
    | assn "||" assn { ADisj $1 $3 }
    | assn "&&" assn { AConj $1 $3 }
    | assn "==>" assn { Implies $1 $3 }
    | "forall" name ',' assn { Forall [$2] $4 }
    | "exists" name ',' assn { Exists [$2] $4 }  
    | '(' assn ')' { AParens $2 }

boolExp :: { BoolExp }
    : comp { BCmp $1 }
    | '!' boolExp { BNot $2 }
    | boolExp "||" boolExp { BDisj $1 $3 }
    | boolExp "&&" boolExp { BConj $1 $3 }
    | '(' boolExp ')' { BParens $2 }

stmt :: { Statement }
    : name ":=" arithExp ';' { Assign $1 $3 }
    | name ',' name ":=" arithExp ',' arithExp ';' { ParAssign $1 $3 $5 $7 }
    | name '[' arithExp ']' ":=" arithExp ';' { Write $1 $3 $6 }
    | "if" boolExp "then" block "else" block "end" { If $2 $4 $6 }
    | "if" boolExp "then" block "end" { If $2 $4 [] }
    | "while" boolExp "inv" assn "do" block "end" { While $2 [$4] $6 }

block :: { Block }
    : block_rev { reverse $1 }

block_rev :: { Block }
    : stmt { [$1] }
    | block_rev stmt { $2:$1 }

pre :: { [Assertion] }
    : assn { [$1] }

post :: { [Assertion] }
    : assn { [$1] }

{

parseProg = parse1 . lexProg

parseError :: [Token] -> a
parseError _ = error "Parse error"

} 