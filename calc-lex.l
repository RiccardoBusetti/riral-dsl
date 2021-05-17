%option noyywrap
%{
#include <stdlib.h>
#include <string.h>
%}

DIGIT [0-9]
INT_NUM {DIGIT}+
REAL_NUM {DIGIT}+\.({DIGIT}+)?
ID [a-zA-Z]+
STRING_CONTENT \"[a-zA-Z0-9.]+\"

%%

[ \t\n] { /* skip useless chars */ }

"(" { return '('; }

")" { return ')'; }

"{" { return '{'; }

"}" { return '}'; }

"+" { return '+'; }

":" { return ':'; }

";" { return ';'; }

"=" { return '='; }

"\"" { return '"'; }

"int" { return INT; }

"real" { return REAL; }

"string" { return STRING; }

"print" { return PRINT; }

"block" { return BLOCK; }

"return" { return RETURN; }

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
     
{STRING_CONTENT} { 
		yylval.string_value = strdup(yytext);
		return STRING_CONTENT;
		}

. { printf("The symbol %s is unknown.\n", yytext); exit(0); }

%%
