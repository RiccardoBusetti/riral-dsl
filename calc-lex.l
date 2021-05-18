%option noyywrap
%{
#include <stdlib.h>
#include <string.h>
%}

DIGIT [0-9]
INT_NUM {DIGIT}+
REAL_NUM {DIGIT}+\.({DIGIT}+)?
ID [a-zA-Z]+

%%

[ \t\n] { /* skip useless chars */ }

"(" { return '('; }

")" { return ')'; }

"{" { return '{'; }

"}" { return '}'; }

"+" { return '+'; }

"-" { return '-'; }

"*" { return '*'; }

"/" { return '/'; }

"^" { return '^'; }

"!" { return '!'; }

"ln" { return LN; }

"log" { return LOG; }

"log10" { return LOG10;}

"sqrt" { return SQRT;}

"sin" { return SIN;}

"cos" { return COS;}

"tan" { return TAN;}

"," { return ','; }

":" { return ':'; }

";" { return ';'; }

"=" { return '='; }

"block" { return BLOCK; }

"print" { return PRINT; }

"int" { return INT; }

"real" { return REAL; }

{INT_NUM} {
            yylval.int_value = atoi(yytext);
            return INT_NUM;
          }

{REAL_NUM} {
            yylval.real_value = atof(yytext);
            return REAL_NUM;
           }

{ID} {
      yylval.lexeme = strdup(yytext);
      return ID;
     }

. { }

%%
