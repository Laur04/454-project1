{
module Parser.Lexer ( Token (..)        -- exporting token data type with all its constructors
                    , lexProg ) where   -- exporting lexProg function (lexes stream of characters --> list of tokens)
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]
$symb = [\_]

tokens:-
    $white+                             ;

    "if"                                { const TIf }
    "then"                              { const TThen }
    "else"                              { const TElse }
    "end"                               { const TEnd }
    "while"                             { const TWhile }
    "inv"                               { const TInv }
    "forall"                            { const TForall }
    "exists"                            { const TExists }
    "do"                                { const TDo }
    "pre"                               { const TPre }
    "post"                              { const TPost }
    "program"                           { const TProgram }
    "is"                                { const TIs }

    $digit+                             { TokenInt . read }
    $alpha [$alpha $digit $symb ]*      { TokenName }
    [\[ \] \+ \- \* \/ \% ]             { TokenSymb }
    [\( \) ]                            { TokenSymb }
    
    [\= \< \>]                          { TokenSymb }
    \!\=                                { TokenSymb }
    \>\=                                { TokenSymb }
    \<\=                                { TokenSymb }
    \!                                  { TokenSymb }
    
    \|\|                                { TokenSymb }
    \&\&                                { TokenSymb }
    \=\=\>                              { TokenSymb }

    \:\=                                { TokenSymb }
    \,                                  { TokenSymb }
    \;                                  { TokenSymb }

{
data Token = TokenInt Int
           | TokenName String
           | TokenSymb String
           | TIf
           | TThen
           | TElse
           | TEnd
           | TWhile
           | TInv
           | TForall
           | TExists
           | TDo
           | TPre
           | TPost
           | TProgram
           | TIs
           deriving (Eq, Show)

-- haskell has typed classes: take data type such as Token and have it derive an instance of a typed class
-- in the above, Token derives an instance of Eq and Show (equality and printing)

lexProg :: String -> [Token]
lexProg = alexScanTokens

}