%{
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>

#define ERROR_BUFFER_SIZE 100
#define OUTPUT_FILE "output.txt"

/* OPERATORS */
typedef enum {
      SUM_OP
} Operation;


/* TYPES */
typedef enum {
      VOID_TYPE,
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


/* STATEMENTS */
typedef struct {
      Type type;
      TypeData data;
} StatementResult;


/* EXPRESSIONS */
typedef struct {
      Type type;
      TypeData data;
} ExprResult;


/* FUNCTION PROTOTYPES */
int yylex();
void yyerror(const char *s);
void parse(FILE *fileInput);

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

void initial_assignment(char *variable_name, Type variable_type, StatementResult *statement_result);

StatementResult *build_statement_result(Type type, TypeData data);
StatementResult *build_statement_result_from(ExprResult *expr_result);
StatementResult *build_void_statement_result();

ExprResult *build_expr_result(Type type, TypeData data);
ExprResult *operation(ExprResult *left, ExprResult *right, Operation operation);
ExprResult *sum(ExprResult *left, ExprResult *right);

void print_expr_result(ExprResult *expr_result);

Program *MAIN = NULL;
%}

%union {
        int int_value;
        double real_value;
        char *lexeme;
        Type type;
        StatementResult *statement_result;
        ExprResult *expr_result;
       }

%token <int_value> INT_NUM
%token <real_value> REAL_NUM
%token <lexeme> ID
%token INT REAL PRINT BLOCK RETURN

%type <type> type
%type <statement_result> statement
%type <statement_result> stmt_block
%type <expr_result> expr

%left '+'

%start scope

%%

scope : statements { exit(0); }
      | /* epsilon */ { exit(0); }

statements : statement ';' statements
           | statement ';'
           ;

statement : expr { $$ = build_statement_result_from($1); }
          | ID ':' type '=' statement { initial_assignment($1, $3, $5); $$ = build_void_statement_result(); }
          | PRINT '(' expr ')' { print_expr_result($3); $$ = build_void_statement_result(); }
          | BLOCK '{' { new_scope(); } stmt_block { destroy_scope(); } '}' { $$ = $4; }
          ;

stmt_block : statements { $$ = build_void_statement_result(); }
           | statements RETURN expr ';' { $$ = build_statement_result_from($3); }
           | RETURN expr ';' { $$ = build_statement_result_from($2); }

type : INT { $$ = INT_TYPE; }
     | REAL { $$ = REAL_TYPE; }
     ;           

expr : '(' expr ')' { $$ = $2; }
     | expr '+' expr { $$ = operation($1, $3, SUM_OP); }
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
      Scope *current = program->current;

      if (current != NULL) {
            SymbolTable *symbol_table = current->symbol_table;
            SymbolTableNode *current = symbol_table->head;
            while (current != NULL) {
                  SymbolTableNode *next = current->next;
                  free(current->entry);
                  free(current);
                  current = next;
            }

            free(symbol_table);
            free(current);
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
            char message[ERROR_BUFFER_SIZE];
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
            char message[ERROR_BUFFER_SIZE];
            sprintf(message, "the variable %s is not in this scope", name);
            yyerror(message);
      }

      return found_entry;
}

void delete(char *name) {
      SymbolTable *symbol_table = get_symbol_table(0);

      if (strcmp(symbol_table->head->entry->name, name) == 0) {
            SymbolTableNode *head = symbol_table->head;
            symbol_table->head = head->next;
            free(head);
      } else {
            SymbolTableNode *prev = NULL;
            SymbolTableNode *current = symbol_table->head;

            while (current != NULL && strcmp(current->entry->name, name) != 0) {
                  prev = current;
                  current = current->next;
            }

            if (current != NULL) {
                  prev->next = current->next;
                  free(current);
            }
      }
}

void print_symbol_table(SymbolTable *symbol_table) {
      SymbolTableNode *current = symbol_table->head;

      while (current != NULL) {
            printf("Variable: %s\n", current->entry->name);
            current = current->next;
      }
}

void initial_assignment(char *variable_name, Type variable_type, StatementResult *statement_result) {
      check_types_eq(variable_type, statement_result->type);
      insert(variable_name, variable_type, statement_result->data);
}

StatementResult *build_statement_result(Type type, TypeData data) {
      StatementResult *statement_result = malloc(sizeof(StatementResult));
      statement_result->type = type;
      statement_result->data = data;

      return statement_result;
}

StatementResult *build_statement_result_from(ExprResult *expr_result) {
      return build_statement_result(expr_result->type, expr_result->data);
}

StatementResult *build_void_statement_result() {
      TypeData data;
      return build_statement_result(VOID_TYPE, data);
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
	FILE *fp = fopen(OUTPUT_FILE, "a");

	switch (expr_result->type) {
	    case INT_TYPE:
		  fprintf(fp, "int: %i\n", expr_result->data.int_value);
		  break;
	    case REAL_TYPE:
		  fprintf(fp, "real: %f\n", expr_result->data.real_value);
		  break;
	    default:
		  fprintf(fp, "Unknown type\n");   
		  break;   
      }
      fclose (fp);
}

void yyerror(const char *s) {
    fprintf(stderr, "Error at %d: %s\n", yylineno, s);
    exit(0);
}

void parse(FILE *fileInput) {
      yyin = fileInput;

      while(feof(yyin) == 0) {
            yyparse();
      }
}

int main(int argc, char* argv[]) {
	FILE *fp = fopen(OUTPUT_FILE, "w");
	fclose (fp);

	FILE* fileInput;
	if((fileInput = fopen(argv[1], "r")) == NULL) {
	      printf("Error while reading the file, try again.\n");
	      exit(0);
	}

	parse(fileInput);
} 
