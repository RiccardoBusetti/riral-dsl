%{
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>

typedef enum {
      SUM
} ExprOperation;

typedef enum {
      INT,
      REAL,
      VOID
} ExprResultType;

typedef union {
      int int_value;
      double real_value;
} ExprResultData;

typedef struct {
  ExprResultType type;
  ExprResultData data;
} ExprResult;

int yylex();
void yyerror(const char *s);

ExprResult *build_expr_result(ExprResultType type, ExprResultData data);
ExprResult *operation(ExprResult *left, ExprResult *right, ExprOperation operation);
ExprResult *sum(ExprResult *left, ExprResult *right);

void print_expr_result(ExprResult *expr_result);
%}

%union {
        int int_value;
        double real_value;
        char *lexeme;
        ExprResult *expr_result;
       }

%token <int_value> INT_NUM
%token <real_value> REAL_NUM
%token <lexeme> ID
%token PRINT

%type <expr_result> expr

%left '+'

%start scope

%%

scope : statements { exit(0); }

statements : statement ';' statements
           | statement ';'
           ;

statement : expr
          | PRINT '(' expr ')' { print_expr_result($3); }
          ;       

expr : '(' expr ')' { $$ = $2; }
     | expr '+' expr { $$ = operation($1, $3, SUM); }
     | INT_NUM { ExprResultData data; data.int_value = $1; $$ = build_expr_result(INT, data); }
     | REAL_NUM { ExprResultData data; data.real_value = $1; $$ = build_expr_result(REAL, data); }
     ;

%%

#include "lex.yy.c"

ExprResult *build_expr_result(ExprResultType type, ExprResultData data) {
      ExprResult *expr_result = malloc(sizeof(ExprResult));
      expr_result->type = type;
      expr_result->data = data;
      
      return expr_result;
}

ExprResult *operation(ExprResult *left, ExprResult *right, ExprOperation operation) {
      ExprResult *new_result;

      switch (operation) {
            case SUM: 
                  return sum(left, right);
            default:
                  return left;
      }
}

ExprResult *sum(ExprResult *left, ExprResult *right) {
      ExprResult *sum = malloc(sizeof(ExprResult));

      if (left->type == INT && right->type == INT) {
            sum->type = INT;
            sum->data.int_value = left->data.int_value + right->data.int_value;
      } else if (left->type == INT && right->type == REAL) {
            sum->type = REAL;
            sum->data.real_value = left->data.int_value + right->data.real_value;
      } else if (left->type == REAL && right->type == INT) {
            sum->type = REAL;
            sum->data.real_value = left->data.real_value + right->data.int_value;
      } else if (left->type == REAL && right->type == REAL) {
            sum->type = REAL;
            sum->data.real_value = left->data.real_value + right->data.real_value;
      }

      return sum;
}

void print_expr_result(ExprResult *expr_result) {
      switch (expr_result->type) {
            case INT:
                  printf("Integer with value %i\n", expr_result->data.int_value);
                  break;
            case REAL:
                  printf("Real with value %f\n", expr_result->data.real_value);
                  break;
            default:
                  printf("Void\n");   
                  break;   
      }
}