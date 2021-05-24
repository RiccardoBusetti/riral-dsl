%option noyywrap
%{
#include <stdlib.h>
#include <string.h>
%}

DIGIT [0-9]
ID [a-zA-Z]+
TEXT [a-zA-Z0-9.\-\!\#\$\%\&\'\*\+\/\{\}\[\]\(\)\?\<\>\^ ]
BOOLEAN_VAL true|false
STRING_VAL \"{TEXT}+\"
INT_VAL {DIGIT}+
REAL_VAL {DIGIT}+\.({DIGIT}+)?
COMMENT	\/\*({TEXT}|\t|\n)*\*\/

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

"log10" { return LOG10; }

"sqrt" { return SQRT; }

"sin" { return SIN; }

"cos" { return COS; }

"tan" { return TAN; }

"|" { return '|'; }

"." { return '.'; }

"," { return ','; }

":" { return ':'; }

";" { return ';'; }

"=" { return '='; }

">" { return GT; }

"<" { return LT; }

">=" { return GE; }

"<=" { return LE; }

"==" { return EQ; }

"!=" { return NE; }

"\"" { return '"'; }

"int" { return INT; }

"real" { return REAL; }

"string" { return STRING; }

"boolean" { return BOOLEAN; }

"print" { return PRINT; }

"block" { return BLOCK; }

"return" { return RETURN; }

{INT_VAL} {
            yylval.int_value = atoi(yytext);
            return INT_VAL;
          }

{REAL_VAL} {
             yylval.real_value = atof(yytext);
             return REAL_VAL;
           }
           
{BOOLEAN_VAL} {
			    char *bool = strdup(yytext);
			    if(strcmp(bool, "true") == 0) {
			         yylval.boolean_value = 1;
			    } else {
				     yylval.boolean_value = 0;
		        }

		        return BOOLEAN_VAL;
		      }
		   	
{STRING_VAL} {
			   char *string = yytext;
               string++[strlen(yytext) - 1] = 0;
		       yylval.string_value = strdup(string);
		       return STRING_VAL;
		     }

{ID} {
       yylval.lexeme = strdup(yytext);
       return ID;
     }

{COMMENT} { /* skip comments */ }

. { printf("The symbol %s is unknown.\n", yytext); exit(0); }

%%
