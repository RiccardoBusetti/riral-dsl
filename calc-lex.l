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

"|" { return '|'; }

"," { return ','; }

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
     
{STRING_CONTENT} { 
                  char *string = yytext;
                  string++[strlen(yytext) - 1] = 0;
		              yylval.string_value = strdup(string);
		              return STRING_CONTENT;
		             }

{ID} {
      yylval.lexeme = strdup(yytext);
      return ID;
     }

. { printf("The symbol %s is unknown.\n", yytext); exit(0); }

%%
