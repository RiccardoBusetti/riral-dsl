%{
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>

typedef struct {
      char *name;
      double value;
} FunReturn;

int yylex();
void yyerror(const char *s);

FunReturn *computeFunReturn(char* name, double value);
void showFunReturn(FunReturn *funReturn);
%}

%union {
        double value;
        char *lexeme;
        FunReturn *funReturn;
       }

%token <value> NUM
%token <lexeme> ID
%token FUN

%type <funReturn> function
%type <value> expr

%left '+'

%start scope

%%

scope : function { showFunReturn($1); exit(0); }
      ;

function : FUN ID '{' expr ';' '}' { $$ = computeFunReturn($2, $4); }
         ;

expr : '(' expr ')' { $$ = $2; }
     | expr '+' expr { $$ = $1 + $3; }
     | NUM { $$ = $1; }
     ;

%%

#include "lex.yy.c"

FunReturn *computeFunReturn(char* name, double value) {
      FunReturn *funReturn = malloc(sizeof(FunReturn));
      funReturn->name = name;
      funReturn->value = value;

      return funReturn;
}

void showFunReturn(FunReturn *funReturn) {
      printf("%s returned %f\n", funReturn->name, funReturn->value);
}