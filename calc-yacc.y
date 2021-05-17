%{
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>
#include <math.h>

/* OPERATORS */
typedef enum {
      SUM_OP,
      DIF_OP,
      MOL_OP,
      DIV_OP,
      EXP_OP,
      LN_OP,
      LOG_OP,
      LOG10_OP,
      SQRT_OP
} Operation;


/* TYPES */
typedef enum {
      INT_TYPE,
      REAL_TYPE
} Type;

typedef union {
      int int_value;
      double real_value;
} TypeData;


/* SYMBOL TABLES */
typedef struct {
      char* name;
      Type type;
      TypeData data;
} SymbolTableEntry;

typedef struct symbol_table_node {
      SymbolTableEntry *entry;
      struct symbol_table_node *next;
} SymbolTableNode;

typedef struct {
      SymbolTableNode *head;
      SymbolTableNode *tail;
} SymbolTable;


/* SCOPING */
typedef struct scope {
      SymbolTable *symbol_table;
      struct scope *outer;
} Scope;

typedef struct {
      Scope *current;
} Program;


/* EXPRESSIONS */
typedef struct {
      Type type;
      TypeData data;
} ExprResult;


/* FUNCTION PROTOTYPES */
int yylex();
void yyerror(const char *s);

char *interpolate(char *string, ...);

void check_types_eq(Type type1, Type type2);

Program *get_program();

void destroy_scope();
void new_scope();

SymbolTable *init_symbol_table();
SymbolTable *get_symbol_table(int scope_index);
void insert(char *name, Type type, TypeData data);
SymbolTableEntry *search(char *name);
SymbolTableEntry *lookup(char *name);
void delete(char *name);
void print_symbol_table(SymbolTable *symbol_table);

void initial_assignment(char *variable_name, Type variable_type, ExprResult *expr_result);

ExprResult *build_expr_result(Type type, TypeData data);

ExprResult *operation(ExprResult *left, ExprResult *right, Operation operation);
ExprResult *sum(ExprResult *left, ExprResult *right);
ExprResult *dif(ExprResult *left, ExprResult *right);
ExprResult *mol(ExprResult *left, ExprResult *right);
ExprResult *div_op(ExprResult *left, ExprResult *right);
ExprResult *exp_op(ExprResult *left, ExprResult *right);
ExprResult *log_op(ExprResult *left, ExprResult *right);

ExprResult *single_operation(ExprResult *left, Operation operation);
ExprResult *ln_op(ExprResult *left);
ExprResult *log10_op(ExprResult *left);
ExprResult *sqrt_op(ExprResult *left);

void print_expr_result(ExprResult *expr_result);

Program *MAIN = NULL;
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
%token INT REAL PRINT BLOCK 
%token LN LOG LOG10 SQRT

%type <type> type
%type <expr_result> expr

%left '-' '+'
%left '*' '/'
%left '^' 
%left LOG LN LOG10 SQRT

%start scope

%%

scope : statements { exit(0); }

statements : statement ';' statements
           | statement ';'
           ;

statement : expr
          | ID ':' type '=' expr { initial_assignment($1, $3, $5); }
          | PRINT '(' expr ')' { print_expr_result($3); }
          | BLOCK '{' { new_scope(); } statements { destroy_scope(); } '}'
          ;

type : INT { $$ = INT_TYPE; }
     | REAL { $$ = REAL_TYPE; }
     ;           

expr : '(' expr ')' { $$ = $2; }
     | expr '+' expr { $$ = operation($1, $3, SUM_OP); }
     | expr '-' expr { $$ = operation($1, $3, DIF_OP); }
     | expr '*' expr { $$ = operation($1, $3, MOL_OP); }
     | expr '/' expr { $$ = operation($1, $3, DIV_OP); }
     | expr '^' expr { $$ = operation($1, $3, EXP_OP); }
     | LOG '(' expr ',' expr ')' { $$ = operation($3, $5, LOG_OP); }
     | LN '(' expr ')' { $$ = single_operation($3,  LN_OP); }
     | LOG10 '(' expr ')' { $$ = single_operation($3, LOG10_OP); }
     | SQRT '(' expr ')' { $$ = single_operation($3,  SQRT_OP); }
     | INT_NUM { TypeData data; data.int_value = $1; $$ = build_expr_result(INT_TYPE, data); }
     | REAL_NUM { TypeData data; data.real_value = $1; $$ = build_expr_result(REAL_TYPE, data); }
     | ID { SymbolTableEntry *entry = lookup($1); $$ = build_expr_result(entry->type, entry->data); }
     ;

%%

#include "lex.yy.c"

void check_types_eq(Type type1, Type type2) {
      if (type1 != type2)
            yyerror("incompatible types");
}

Program *get_program() {
      if (MAIN == NULL) MAIN = malloc(sizeof(Program));
      return MAIN;
}

void destroy_scope() {
      Program *program = get_program();

      if (program->current != NULL) {
            program->current = program->current->outer;
      }
}

void new_scope() {
      Program *program = get_program();

      Scope *scope = malloc(sizeof(Scope));
      scope->symbol_table = init_symbol_table();

      if (program->current == NULL) {
            // We do not have any active scope, create the main scope.
            scope->outer = NULL;
            program->current = scope;
      } else {
            // We already have one scope, we need to update this scope as the current.
            scope->outer = program->current;
            program->current = scope;
      }
}

SymbolTable *init_symbol_table() {
      SymbolTable *symbol_table = malloc(sizeof(SymbolTable));
      return symbol_table;
}

SymbolTable *get_symbol_table(int scope_index) {
      if (MAIN == NULL) new_scope();

      int index = 0;
      Scope *current = MAIN->current;
      while (current != NULL && index < scope_index) {
            current = current->outer;
            index++;
      }

      return current == NULL ? NULL : current->symbol_table;
}

void insert(char *name, Type type, TypeData data) {
      SymbolTable *symbol_table = get_symbol_table(0);

      SymbolTableEntry *entry = malloc(sizeof(SymbolTableEntry));
      entry->name = name;
      entry->type = type;
      entry->data = data;

      SymbolTableNode *node = malloc(sizeof(SymbolTableNode));
      node->entry = entry;

      if (search(name) != NULL) {
            char *message;
            sprintf(message, "variable %s is already declared in this scope", name);
            yyerror(message);
      }
            

      if (symbol_table->head == NULL) {
            // The symbol table is empty, initialize it.
            symbol_table->head = node;
            symbol_table->tail = node;
      } else {
            // The symbol table is non empty, append the value to it. 
            symbol_table->tail->next = node;
            symbol_table->tail = node;
      }
}

SymbolTableEntry *search(char *name) {
      int scope_index = 0;
      SymbolTable *symbol_table = NULL;

      do {
            symbol_table = get_symbol_table(scope_index);

            if (symbol_table != NULL) {
                  SymbolTableNode *current = symbol_table->head;

                  while (current != NULL) {
                        if (strcmp(current->entry->name, name) == 0) 
                              return current->entry;

                        current = current->next;
                  }

                  scope_index++;
            }
      } while (symbol_table != NULL);

      return NULL;
}

SymbolTableEntry *lookup(char *name) {
      SymbolTableEntry *found_entry = search(name);
      if (found_entry == NULL) {
            char *message;
            sprintf(message, "the variable %s is not in this scope", name);
            yyerror(message);
      }

      return found_entry;
}

void delete(char *name) {
      SymbolTable *symbol_table = get_symbol_table(0);
      // TODO: implement deletion, needed only in case of scoping.
}

void print_symbol_table(SymbolTable *symbol_table) {
      SymbolTableNode *current = symbol_table->head;

      while (current != NULL) {
            printf("Variable: %s\n", current->entry->name);
            current = current->next;
      }
}

void initial_assignment(char *variable_name, Type variable_type, ExprResult *expr_result) {
      check_types_eq(variable_type, expr_result->type);
      insert(variable_name, variable_type, expr_result->data);
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
            case DIF_OP: 
                  return dif(left, right);
            case MOL_OP: 
                  return mol(left, right);
            case DIV_OP: 
                  return div_op(left, right);
            case EXP_OP: 
                  return exp_op(left, right);
            case LOG_OP: 
                  return exp_op(left, right);
            default:
                  return left;
      }
}

ExprResult *single_operation(ExprResult *left, Operation operation) {
      ExprResult *new_result;

      switch (operation) {
            case LN_OP: 
                  return ln_op(left);
            case LOG10_OP: 
                  return log10_op(left);
            case SQRT_OP: 
                  return sqrt_op(left);
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

ExprResult *dif(ExprResult *left, ExprResult *right) {
      ExprResult *dif = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            dif->type = INT_TYPE;
            dif->data.int_value = left->data.int_value - right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            dif->type = REAL_TYPE;
            dif->data.real_value = left->data.int_value - right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            dif->type = REAL_TYPE;
            dif->data.real_value = left->data.real_value - right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            dif->type = REAL_TYPE;
            dif->data.real_value = left->data.real_value - right->data.real_value;
      } else {
            yyerror("invalid type/s for expression -");
      }

      return dif;
}

ExprResult *mol(ExprResult *left, ExprResult *right) {
      ExprResult *mol = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            mol->type = INT_TYPE;
            mol->data.int_value = left->data.int_value * right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            mol->type = REAL_TYPE;
            mol->data.real_value = left->data.int_value * right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            mol->type = REAL_TYPE;
            mol->data.real_value = left->data.real_value * right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            mol->type = REAL_TYPE;
            mol->data.real_value = left->data.real_value * right->data.real_value;
      } else {
            yyerror("invalid type/s for expression *");
      }

      return mol;
}

ExprResult *div_op(ExprResult *left, ExprResult *right) {
      ExprResult *div_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            div_op->type = INT_TYPE;
            div_op->data.int_value = left->data.int_value / right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            div_op->type = REAL_TYPE;
            div_op->data.real_value = left->data.int_value / right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            div_op->type = REAL_TYPE;
            div_op->data.real_value = left->data.real_value / right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            div_op->type = REAL_TYPE;
            div_op->data.real_value = left->data.real_value / right->data.real_value;
      } else {
            yyerror("invalid type/s for expression /");
      }

      return div_op;
}

ExprResult *exp_op(ExprResult *left, ExprResult *right) {
      ExprResult *exp_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            exp_op->type = INT_TYPE;
            exp_op->data.int_value = pow (left->data.int_value, right->data.int_value);
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            exp_op->type = REAL_TYPE;
            exp_op->data.real_value = pow (left->data.int_value, right->data.real_value);
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            exp_op->type = REAL_TYPE;
            exp_op->data.real_value = pow (left->data.real_value, right->data.int_value);
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            exp_op->type = REAL_TYPE;
            exp_op->data.real_value = pow (left->data.real_value, right->data.real_value);
      } else {
            yyerror("invalid type/s for expression ^");
      }

      return exp_op;
}

ExprResult *log_op(ExprResult *left, ExprResult *right) {
      ExprResult *log_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.int_value = log (left->data.int_value) / log (right->data.int_value);
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log (left->data.int_value) / log (right->data.real_value);
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log (left->data.real_value) / log (right->data.int_value);
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log (left->data.real_value) / log (right->data.real_value);
      } else {
            yyerror("invalid type/s for expression log");
      }

      return log_op;
}

ExprResult *ln_op(ExprResult *left) {
      ExprResult *ln_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            ln_op->type = REAL_TYPE;
            ln_op->data.real_value = log (left->data.int_value);
      } else if (left->type == INT_TYPE) {
            ln_op->type = REAL_TYPE;
            ln_op->data.real_value = log (left->data.int_value);
      } else {
            yyerror("invalid type/s for expression ln");
      }

      return ln_op;
}

ExprResult *log10_op(ExprResult *left) {
      ExprResult *log10_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            log10_op->type = REAL_TYPE;
            log10_op->data.real_value= log10 (left->data.int_value);
      } else if (left->type == INT_TYPE) {
            log10_op->type = REAL_TYPE;
            log10_op->data.real_value = log10 (left->data.int_value);
      } else {
            yyerror("invalid type/s for expression log10");
      }

      return log10_op;
}

ExprResult *sqrt_op(ExprResult *left) {
      ExprResult *sqrt_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            sqrt_op->type = REAL_TYPE;
            sqrt_op->data.real_value= sqrt (left->data.int_value);
      } else if (left->type == INT_TYPE) {
            sqrt_op->type = REAL_TYPE;
            sqrt_op->data.real_value = sqrt (left->data.int_value);
      } else {
            yyerror("invalid type/s for expression sqrt");
      }

      return sqrt_op;
}

void print_expr_result(ExprResult *expr_result) {
      switch (expr_result->type) {
            case INT_TYPE:
                  printf("int: %i\n", expr_result->data.int_value);
                  break;
            case REAL_TYPE:
                  printf("real: %f\n", expr_result->data.real_value);
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

int main(void) {
      printf("Waiting for input...\n");

      new_scope();

      return yyparse();
} 