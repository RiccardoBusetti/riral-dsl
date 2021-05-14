%{
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>

typedef enum {
      SUM_OP
} Operation;

typedef enum {
      INT_TYPE,
      REAL_TYPE
} Type;

typedef union {
      int int_value;
      double real_value;
} TypeData;

typedef struct {
      char* name;
      Type type;
      TypeData data;
} SymbolTableEntry;

typedef struct sm_node {
      SymbolTableEntry *entry;
      struct sm_node *next;
} SymbolTableNode;

typedef struct {
      SymbolTableNode *head;
      SymbolTableNode *tail;
} SymbolTable;

typedef struct {
      Type type;
      TypeData data;
} ExprResult;

int yylex();
void yyerror(const char *s);

void check_types_eq(Type type1, Type type2);

SymbolTable *init_symbol_table();
void insert(SymbolTable *symbol_table, char *name, Type type, TypeData data);
SymbolTableEntry *lookup(SymbolTable *symbol_table, char *name);
void delete(SymbolTable *symbol_table, char *name);
void print_symbol_table(SymbolTable *symbol_table);

ExprResult *build_expr_result(Type type, TypeData data);
ExprResult *operation(ExprResult *left, ExprResult *right, Operation operation);
ExprResult *sum(ExprResult *left, ExprResult *right);

void print_expr_result(ExprResult *expr_result);

SymbolTable *SYMBOL_TABLE = NULL;
%}

%union {
        int int_value;
        double real_value;
        char *lexeme;
        Type type;
        ExprResult *expr_result;
       }

%token <int_value> INT_NUM
%token <real_value> REAL_NUM
%token <lexeme> ID
%token INT REAL PRINT

%type <type> type
%type <expr_result> expr

%left '+'

%start scope

%%

scope : statements { exit(0); }

statements : statement ';' statements
           | statement ';'
           ;

statement : expr
          | ID ':' type '=' expr { check_types_eq($3, $5->type); insert(SYMBOL_TABLE, $1, $3, $5->data); }
          | PRINT '(' expr ')' { print_expr_result($3); }
          ;

type : INT { $$ = INT_TYPE; }
     | REAL { $$ = REAL_TYPE; }
     ;           

expr : '(' expr ')' { $$ = $2; }
     | expr '+' expr { $$ = operation($1, $3, SUM_OP); }
     | INT_NUM { TypeData data; data.int_value = $1; $$ = build_expr_result(INT_TYPE, data); }
     | REAL_NUM { TypeData data; data.real_value = $1; $$ = build_expr_result(REAL_TYPE, data); }
     | ID { SymbolTableEntry *entry = lookup(SYMBOL_TABLE, $1); $$ = build_expr_result(entry->type, entry->data); }
     ;

%%

#include "lex.yy.c"

void check_types_eq(Type type1, Type type2) {
      if (type1 != type2)
            yyerror("incompatible types");
}

SymbolTable *init_symbol_table(SymbolTable *symbol_table) {
      if (SYMBOL_TABLE == NULL) {
            symbol_table = malloc(sizeof(symbol_table));
            SYMBOL_TABLE = symbol_table;
      }

      return symbol_table;
}

void insert(SymbolTable *symbol_table, char *name, Type type, TypeData data) {
      symbol_table = init_symbol_table(symbol_table);

      // TODO: check if type of expression and declared type are equal.
      SymbolTableEntry *entry = malloc(sizeof(SymbolTableEntry));
      entry->name = name;
      entry->type = type;
      entry->data = data;

      SymbolTableNode *node = malloc(sizeof(SymbolTableNode));
      node->entry = entry;

      if (symbol_table->head == NULL) {
            // The symbol table is empty, initialize it.
            symbol_table->head = node;
            symbol_table->tail = node;
      } else {
            // The symbol table is non empty, append the value to it. 
            SymbolTableNode *current = symbol_table->head;
            while (current != NULL) {
                  if (strcmp(current->entry->name, entry->name) == 0) 
                        yyerror("variable is already declared in this scope");

                  current = current->next;
            }
            
            symbol_table->tail->next = node;
            symbol_table->tail = node;
      }
}

SymbolTableEntry *lookup(SymbolTable *symbol_table, char *name) {
      symbol_table = init_symbol_table(symbol_table);

      SymbolTableNode *current = symbol_table->head;

      while (current != NULL) {
            if (strcmp(current->entry->name, name) == 0) 
                  return current->entry;

            current = current->next;
      }

      yyerror("the variable is not in this scope");
      return NULL;
}

void delete(SymbolTable *symbol_table, char *name) {
      symbol_table = init_symbol_table(symbol_table);
      // TODO: implement deletion, needed only in case of scoping.
}

void print_symbol_table(SymbolTable *symbol_table) {
      SymbolTableNode *current = symbol_table->head;

      while (current != NULL) {
            printf("Variable: %s\n", current->entry->name);
            current = current->next;
      }
}


ExprResult *build_expr_result(Type type, TypeData data) {
      ExprResult *expr_result = malloc(sizeof(ExprResult));
      expr_result->type = type;
      expr_result->data = data;
      
      return expr_result;
}

ExprResult *operation(ExprResult *left, ExprResult *right, Operation operation) {
      ExprResult *new_result;

      switch (operation) {
            case SUM_OP: 
                  return sum(left, right);
            default:
                  return left;
      }
}

ExprResult *sum(ExprResult *left, ExprResult *right) {
      ExprResult *sum = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            sum->type = INT_TYPE;
            sum->data.int_value = left->data.int_value + right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            sum->type = REAL_TYPE;
            sum->data.real_value = left->data.int_value + right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            sum->type = REAL_TYPE;
            sum->data.real_value = left->data.real_value + right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            sum->type = REAL_TYPE;
            sum->data.real_value = left->data.real_value + right->data.real_value;
      } else {
            yyerror("invalid type/s for expression +");
      }

      return sum;
}

void print_expr_result(ExprResult *expr_result) {
      switch (expr_result->type) {
            case INT_TYPE:
                  printf("Integer with value %i\n", expr_result->data.int_value);
                  break;
            case REAL_TYPE:
                  printf("Real with value %f\n", expr_result->data.real_value);
                  break;
            default:
                  printf("Unknown type\n");   
                  break;   
      }
}

void yyerror(const char *s) {
    fprintf(stderr, "Error at %d: %s\n", yylineno, s);
    exit(0);
}

// main() { 
//   extern int yydebug;
//   yydebug = 1;
//   return yyparse();
// }