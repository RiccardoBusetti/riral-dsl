%option noyywrap
%{
#include <stdlib.h>
#include <string.h>
%}

DIGIT [0-9]
NUM {DIGIT}+(\.{DIGIT}+)?
ID [a-zA-Z]+

%%

[ \t\n] { /* skip useless chars */ }

fun { return FUN; }

"(" { return '('; }

")" { return ')'; }

"{" { return '{'; }

"}" { return '}'; }

"+" { return '+'; }

";" { return ';'; }

{NUM} {
       yylval.value = atof(yytext);
       return NUM;
      }

{ID} {
      yylval.lexeme = strdup(yytext);
      return ID;
     }

%%
