%{
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdio.h>
#include <math.h>

#define ERROR_BUFFER_SIZE 100
#define OUTPUT_FILE "output.txt"
#define EPSILON 0.00001


/* BASIC TYPES */
typedef enum {
      FALSE,
      TRUE
} Boolean;


/* OPERATORS */
typedef enum {
      SUM_OP,
      DIF_OP,
      MOL_OP,
      DIV_OP,
      EXP_OP,
      FAC_OP,
      NEG_OP,
      LN_OP,
      LOG_OP,
      LOG10_OP,
      SQRT_OP,
      SIN_OP,
      COS_OP,
      TAN_OP,
      CON_OP,
      CON_SPACE_OP,
      EQ_OP,
      NE_OP,
      GT_OP,
      LT_OP,
      GE_OP,
      LE_OP
} Operation;


/* TYPES */
typedef enum {
      VOID_TYPE,
      INT_TYPE,
      REAL_TYPE,
      STRING_TYPE,
      BOOLEAN_TYPE
} Type;

typedef union {
      int int_value;
      double real_value;
      char *string_value;
      Boolean boolean_value;
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


/* HELPER FUNCTIONS */
int yylex();
void yyerror(const char *s);
void parse(FILE *fileInput);
void check_types_eq(Type type1, Type type2);
char *type_to_string(Type type);


/* PROGRAM FUNCTIONS */
Program *get_program();


/* SCOPE FUNCTIONS */
void destroy_scope();
void new_scope();


/* SYMBOL TABLE FUNCTIONS */
SymbolTable *init_symbol_table();
SymbolTable *get_symbol_table(int scope_index);
void insert(char *name, Type type, TypeData data);
void update(char *name, Type type, TypeData data);
SymbolTableEntry *search(char *name, int current_only);
SymbolTableEntry *lookup(char *name);
void delete(char *name);
void print_symbol_table(SymbolTable *symbol_table);


/* GENERIC FUNCTIONS */
void initial_assignment(char *variable_name, Type variable_type, StatementResult *statement_result);
void existing_assignment(char *variable_name, StatementResult *statement_result);


/* STATEMENT FUNCTIONS */
StatementResult *build_statement_result(Type type, TypeData data);
StatementResult *build_statement_result_from(ExprResult *expr_result);
StatementResult *build_void_statement_result();


/* EXPRESSION FUNCTIONS */
ExprResult *build_expr_result(Type type, TypeData data);
ExprResult *operation(ExprResult *left, ExprResult *right, Operation operation);
ExprResult *sum_op(ExprResult *left, ExprResult *right);
ExprResult *dif_op(ExprResult *left, ExprResult *right);
ExprResult *mol_op(ExprResult *left, ExprResult *right);
ExprResult *div_op(ExprResult *left, ExprResult *right);
ExprResult *exp_op(ExprResult *left, ExprResult *right);
ExprResult *log_op(ExprResult *left, ExprResult *right);
ExprResult *con_op(ExprResult *left, ExprResult *right);
ExprResult *con_space_op(ExprResult *left, ExprResult *right);
ExprResult *eq_op(ExprResult *left, ExprResult *right);
ExprResult *ne_op(ExprResult *left, ExprResult *right);
ExprResult *gt_op(ExprResult *left, ExprResult *right);
ExprResult *lt_op(ExprResult *left, ExprResult *right);
ExprResult *ge_op(ExprResult *left, ExprResult *right);
ExprResult *le_op(ExprResult *left, ExprResult *right);
ExprResult *single_operation(ExprResult *left, Operation operation);
ExprResult *neg_op(ExprResult *left);
ExprResult *fac_op(ExprResult *left);
ExprResult *ln_op(ExprResult *left);
ExprResult *log10_op(ExprResult *left);
ExprResult *sqrt_op(ExprResult *left);
ExprResult *sin_op(ExprResult *left);
ExprResult *cos_op(ExprResult *left);
ExprResult *tan_op(ExprResult *left);
void print_expr_result(ExprResult *expr_result);


/* GLOBAL VARIABLES */
Program *MAIN = NULL;
%}

%union {
        int int_value;
        double real_value;
        Boolean boolean_value;
        char *string_value;
        char *lexeme;
        Type type;
        StatementResult *statement_result;
        ExprResult *expr_result;
       }

%token <int_value> INT_VAL
%token <real_value> REAL_VAL
%token <boolean_value> BOOLEAN_VAL
%token <string_value> STRING_VAL
%token <lexeme> ID
%token PRINT BLOCK RETURN
%token INT REAL BOOLEAN STRING LN LOG LOG10 SQRT GT LT GE LE EQ NE 

%type <type> type
%type <statement_result> statement
%type <statement_result> stmt_block
%type <expr_result> expr

%left '-' '+'
%left '*' '/'
%left '^' '!'
%left LOG LN LOG10 SQRT SIN COS TAN
%left '.' '|'  
%left GT LT GE LE EQ NE 
%right UMINUS

%start program

%%

program : statements { exit(0); }
      | /* epsilon */ { exit(0); }

statements : statement ';' statements
           | statement ';'
           ;

statement : expr { $$ = build_statement_result_from($1); }
          | ID ':' type '=' statement { initial_assignment($1, $3, $5); $$ = build_void_statement_result(); }
          | ID '=' statement { existing_assignment($1, $3); $$ = build_void_statement_result(); }
          | PRINT '(' expr ')' { print_expr_result($3); $$ = build_void_statement_result(); }
          | BLOCK '{' { new_scope(); } stmt_block { destroy_scope(); } '}' { $$ = $4; }
          ;

stmt_block : statements { $$ = build_void_statement_result(); }
           | statements RETURN expr ';' { $$ = build_statement_result_from($3); }
           | RETURN expr ';' { $$ = build_statement_result_from($2); }

type : INT { $$ = INT_TYPE; }
     | REAL { $$ = REAL_TYPE; }
     | STRING { $$ = STRING_TYPE; }
     | BOOLEAN { $$ = BOOLEAN_TYPE; }
     ;

expr : '(' expr ')' { $$ = $2; }
     | expr '+' expr { $$ = operation($1, $3, SUM_OP); }
     | expr '-' expr { $$ = operation($1, $3, DIF_OP); }
     | expr '*' expr { $$ = operation($1, $3, MOL_OP); }
     | expr '/' expr { $$ = operation($1, $3, DIV_OP); }
     | expr '^' expr { $$ = operation($1, $3, EXP_OP); }
     | expr '!' { $$ = single_operation($1, FAC_OP); }
     | '-' expr %prec UMINUS { $$ = single_operation($2,  NEG_OP); }
     | expr '.' expr { $$ = operation($1, $3, CON_OP); }
     | expr '|' expr { $$ = operation($1, $3, CON_SPACE_OP); }
     | LOG '(' expr ',' expr ')' { $$ = operation($3, $5, LOG_OP); }
     | LN '(' expr ')' { $$ = single_operation($3, LN_OP); }
     | LOG10 '(' expr ')' { $$ = single_operation($3, LOG10_OP); }
     | SQRT '(' expr ')' { $$ = single_operation($3, SQRT_OP); }
     | SIN '(' expr ')' { $$ = single_operation($3, SIN_OP); }
     | COS '(' expr ')' { $$ = single_operation($3, COS_OP); }
     | TAN '(' expr ')' { $$ = single_operation($3, TAN_OP); }
     | expr GT expr  { $$ = operation($1, $3, GT_OP); }
     | expr LT expr  { $$ = operation($1, $3, LT_OP); }
     | expr GE expr  { $$ = operation($1, $3, GE_OP); }
     | expr LE expr  { $$ = operation($1, $3, LE_OP); }
     | expr EQ expr  { $$ = operation($1, $3, EQ_OP); }
     | expr NE expr  { $$ = operation($1, $3, NE_OP); }
     | INT_VAL { TypeData data; data.int_value = $1; $$ = build_expr_result(INT_TYPE, data); }
     | REAL_VAL { TypeData data; data.real_value = $1; $$ = build_expr_result(REAL_TYPE, data); }
     | BOOLEAN_VAL { TypeData data; data.boolean_value = $1 == 0 ? FALSE : TRUE; $$ = build_expr_result(BOOLEAN_TYPE, data); }
     | STRING_VAL { TypeData data; data.string_value = $1; $$ = build_expr_result(STRING_TYPE, data); }
     | ID { SymbolTableEntry *entry = lookup($1); $$ = build_expr_result(entry->type, entry->data); }
     ;

%%

#include "lex.yy.c"

/**
      Checks if two types are equal, otherwise throws an error.
*/
void check_types_eq(Type type1, Type type2) {
      if (type1 != type2) {
            char message[ERROR_BUFFER_SIZE];
            sprintf(message, "incompatible types\nrequired: %s\nfound: %s", type_to_string(type1), type_to_string(type2));
            yyerror(message);
      }
}

/**
      Converts a type to its string representation.
*/
char *type_to_string(Type type) {
      switch (type) {
            case VOID_TYPE: return "void";
            case INT_TYPE: return "int";
            case REAL_TYPE: return "real";
            case STRING_TYPE: return "string";
            case BOOLEAN_TYPE: return "Boolean";
            default: return "unknown";
      }
}

/**
      Gets the program which is currently running.

      In this case we have one single MAIN program which has linked to it the
      current scope in execution.      
*/
Program *get_program() {
      if (MAIN == NULL) MAIN = malloc(sizeof(Program));

      return MAIN;
}

/**
      Destroys the current scope, together with all the symbol table entries.

      If there exist an outer scope we will set that as the new current scope for
      the program.      
*/
void destroy_scope() {
      Program *program = get_program();
      Scope *current_scope = program->current;

      if (current_scope != NULL) {
            SymbolTable *symbol_table = current_scope->symbol_table;
            SymbolTableNode *current_node = symbol_table->head;

            while (current_node != NULL) {
                  SymbolTableNode *next = current_node->next;
                  free(current_node->entry);
                  free(current_node);
                  current_node = next;
            }

            free(symbol_table);
            program->current = current_scope->outer;
            free(current_scope);
      }
}

/**
      Creates a new scope from the current scope.

      If there exist a current scope it will link that scope as the outer scope
      of the newly created scope.
*/
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

/**
      Initialized the symbol table in memory.      
*/
SymbolTable *init_symbol_table() {
      SymbolTable *symbol_table = malloc(sizeof(SymbolTable));
      return symbol_table;
}

/**
      Gets the symbol table at a given scope index, where the index 0 corresponds
      to the current scope and the other index + 1 will correspond to the outer scopes.
*/
SymbolTable *get_symbol_table(int scope_index) {
      if (MAIN == NULL) new_scope();

      int index = 0;
      Program *program = get_program();
      Scope *current_scope = program->current;
      while (current_scope != NULL && index < scope_index) {
            current_scope = current_scope->outer;
            index++;
      }

      return current_scope == NULL ? NULL : current_scope->symbol_table;
}

/**
      Inserts an entry into the symbol table.      
*/
void insert(char *name, Type type, TypeData data) {
      SymbolTable *symbol_table = get_symbol_table(0);

      SymbolTableEntry *entry = malloc(sizeof(SymbolTableEntry));
      entry->name = name;
      entry->type = type;
      entry->data = data;

      SymbolTableNode *node = malloc(sizeof(SymbolTableNode));
      node->entry = entry;

      if (search(name, 1) != NULL) {
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

/**
      Updates an entry into the symbol table.

      This update can be done only if the new type and old type are the same.      
*/
void update(char *name, Type type, TypeData data) {
      SymbolTableEntry *found_entry = search(name, 0);

      if (found_entry == NULL) {
            char message[ERROR_BUFFER_SIZE];
            sprintf(message, "the variable %s is not in this scope", name);
            yyerror(message);
      }

      check_types_eq(found_entry->type, type);

      found_entry->data = data;
}

/**
      Searches for a symbol table entry by name.

      If current only is set to 1 this means that we will search only in the
      symbol table for the current scope, otherwise it will check in the outer scopes.      
*/
SymbolTableEntry *search(char *name, int current_only) {
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

                  if (current_only == 1) {
                        return NULL;
                  }

                  scope_index++;
            }
      } while (symbol_table != NULL);

      return NULL;
}

/**
      Looks up for a symbol table entry by name.      
*/
SymbolTableEntry *lookup(char *name) {
      SymbolTableEntry *found_entry = search(name, 0);

      if (found_entry == NULL) {
            char message[ERROR_BUFFER_SIZE];
            sprintf(message, "the variable %s is not in this scope", name);
            yyerror(message);
      }

      return found_entry;
}

/**
      Deletes an entry in the symbol table by name.      
*/
void delete(char *name) {
      SymbolTable *symbol_table = get_symbol_table(0);

      if (strcmp(symbol_table->head->entry->name, name) == 0) {
            // If we want to delete the head of the list we need to replace it.
            SymbolTableNode *head = symbol_table->head;
            symbol_table->head = head->next;
            free(head);
      } else {
            SymbolTableNode *prev = NULL;
            SymbolTableNode *current = symbol_table->head;

            // We search for the value which we want to delete and we keep his previous element.
            while (current != NULL && strcmp(current->entry->name, name) != 0) {
                  prev = current;
                  current = current->next;
            }

            if (current != NULL) {
                  // If we delete the last element we update the tail.
                  if (current->next == NULL) 
                        symbol_table->tail = prev;

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

void existing_assignment(char *variable_name, StatementResult *statement_result) {
      update(variable_name, statement_result->type, statement_result->data);
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
                  return sum_op(left, right);
            case DIF_OP: 
                  return dif_op(left, right);
            case MOL_OP: 
                  return mol_op(left, right);
            case DIV_OP: 
                  return div_op(left, right);
            case EXP_OP: 
                  return exp_op(left, right);
            case LOG_OP: 
                  return log_op(left, right);
            case CON_OP: 
                  return con_op(left, right);
            case CON_SPACE_OP: 
                  return con_space_op(left, right);
            case EQ_OP: 
                  return eq_op(left, right);   
            case NE_OP: 
                  return ne_op(left, right); 
            case GT_OP: 
                  return gt_op(left, right);  
            case LT_OP: 
                  return lt_op(left, right);   
            case GE_OP: 
                  return ge_op(left, right);   
            case LE_OP: 
                  return le_op(left, right); 
            default:
                  return left;
      }
}

ExprResult *single_operation(ExprResult *left, Operation operation) {
      ExprResult *new_result;

      switch (operation) {
            case NEG_OP: 
                  return neg_op(left);
            case FAC_OP: 
                  return fac_op(left);
            case LN_OP: 
                  return ln_op(left);
            case LOG10_OP: 
                  return log10_op(left);
            case SQRT_OP: 
                  return sqrt_op(left);
            case SIN_OP: 
                  return sin_op(left);
            case COS_OP: 
                  return cos_op(left);
            case TAN_OP: 
                  return tan_op(left);
            default:
                  return left;
      }
}

ExprResult *sum_op(ExprResult *left, ExprResult *right) {
      ExprResult *sum_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            sum_op->type = INT_TYPE;
            sum_op->data.int_value = left->data.int_value + right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            sum_op->type = REAL_TYPE;
            sum_op->data.real_value = left->data.int_value + right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            sum_op->type = REAL_TYPE;
            sum_op->data.real_value = left->data.real_value + right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            sum_op->type = REAL_TYPE;
            sum_op->data.real_value = left->data.real_value + right->data.real_value;
      } else {
            yyerror("invalid type/s for expression +");
      }

      return sum_op;
}

ExprResult *dif_op(ExprResult *left, ExprResult *right) {
      ExprResult *dif_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            dif_op->type = INT_TYPE;
            dif_op->data.int_value = left->data.int_value - right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            dif_op->type = REAL_TYPE;
            dif_op->data.real_value = left->data.int_value - right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            dif_op->type = REAL_TYPE;
            dif_op->data.real_value = left->data.real_value - right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            dif_op->type = REAL_TYPE;
            dif_op->data.real_value = left->data.real_value - right->data.real_value;
      } else {
            yyerror("invalid type/s for expression -");
      }

      return dif_op;
}

ExprResult *mol_op(ExprResult *left, ExprResult *right) {
      ExprResult *mol_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            mol_op->type = INT_TYPE;
            mol_op->data.int_value = left->data.int_value * right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            mol_op->type = REAL_TYPE;
            mol_op->data.real_value = left->data.int_value * right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            mol_op->type = REAL_TYPE;
            mol_op->data.real_value = left->data.real_value * right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            mol_op->type = REAL_TYPE;
            mol_op->data.real_value = left->data.real_value * right->data.real_value;
      } else {
            yyerror("invalid type/s for expression *");
      }

      return mol_op;
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
            exp_op->data.int_value = pow(left->data.int_value, right->data.int_value);
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            exp_op->type = REAL_TYPE;
            exp_op->data.real_value = pow(left->data.int_value, right->data.real_value);
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            exp_op->type = REAL_TYPE;
            exp_op->data.real_value = pow(left->data.real_value, right->data.int_value);
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            exp_op->type = REAL_TYPE;
            exp_op->data.real_value = pow(left->data.real_value, right->data.real_value);
      } else {
            yyerror("invalid type/s for expression ^");
      }

      return exp_op;
}

ExprResult *log_op(ExprResult *left, ExprResult *right) {
      ExprResult *log_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log(left->data.int_value) / log(right->data.int_value);
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log(left->data.int_value) / log(right->data.real_value);
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log(left->data.real_value) / log(right->data.int_value);
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            log_op->type = REAL_TYPE;
            log_op->data.real_value = log(left->data.real_value) / log(right->data.real_value);
      } else {
            yyerror("invalid type/s for expression log");
      }

      return log_op;
}

ExprResult *eq_op(ExprResult *left, ExprResult *right) {
      ExprResult *eq_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            eq_op->type = BOOLEAN_TYPE;
            eq_op->data.boolean_value = left->data.int_value == right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            eq_op->type = BOOLEAN_TYPE;
            eq_op->data.boolean_value = fabs(left->data.int_value - right->data.real_value) < EPSILON;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            eq_op->type = BOOLEAN_TYPE;
            eq_op->data.boolean_value = fabs(left->data.real_value - right->data.int_value) < EPSILON;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            eq_op->type = BOOLEAN_TYPE;
            eq_op->data.boolean_value = fabs(left->data.real_value - right->data.real_value) < EPSILON;
      } else {
            yyerror("invalid type/s for expression ==");
      }

      return eq_op;
}

ExprResult *ne_op(ExprResult *left, ExprResult *right) {
      ExprResult *ne_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            ne_op->type = BOOLEAN_TYPE;
            ne_op->data.boolean_value = left->data.int_value != right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            ne_op->type = BOOLEAN_TYPE;
            ne_op->data.boolean_value = !(fabs(left->data.int_value - right->data.real_value) < EPSILON);
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            ne_op->type = BOOLEAN_TYPE;
            ne_op->data.boolean_value = !(fabs(left->data.real_value - right->data.int_value) < EPSILON);
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            ne_op->type = BOOLEAN_TYPE;
            ne_op->data.boolean_value = !(fabs(left->data.real_value - right->data.real_value) < EPSILON);
      } else {
            yyerror("invalid type/s for expression !=");
      }

      return ne_op;
}

ExprResult *gt_op(ExprResult *left, ExprResult *right) {
      ExprResult *gt_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            gt_op->type = BOOLEAN_TYPE;
            gt_op->data.boolean_value = left->data.int_value > right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            gt_op->type = BOOLEAN_TYPE;
            gt_op->data.boolean_value = left->data.int_value > right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            gt_op->type = BOOLEAN_TYPE;
            gt_op->data.boolean_value = left->data.real_value > right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            gt_op->type = BOOLEAN_TYPE;
            gt_op->data.boolean_value = left->data.real_value > right->data.real_value;
      } else {
            yyerror("invalid type/s for expression >");
      }

      return gt_op;
}

ExprResult *lt_op(ExprResult *left, ExprResult *right) {
      ExprResult *lt_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            lt_op->type = BOOLEAN_TYPE;
            lt_op->data.boolean_value = left->data.int_value < right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            lt_op->type = BOOLEAN_TYPE;
            lt_op->data.boolean_value = left->data.int_value < right->data.real_value;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            lt_op->type = BOOLEAN_TYPE;
            lt_op->data.boolean_value = left->data.real_value < right->data.int_value;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            lt_op->type = BOOLEAN_TYPE;
            lt_op->data.boolean_value = left->data.real_value < right->data.real_value;
      } else {
            yyerror("invalid type/s for expression <");
      }

      return lt_op;
}

ExprResult *ge_op(ExprResult *left, ExprResult *right) {
      ExprResult *ge_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            ge_op->type = BOOLEAN_TYPE;
            ge_op->data.boolean_value = left->data.int_value >= right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            ge_op->type = BOOLEAN_TYPE;
            ge_op->data.boolean_value = left->data.int_value > right->data.real_value || fabs(left->data.int_value - right->data.real_value) < EPSILON;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            ge_op->type = BOOLEAN_TYPE;
            ge_op->data.boolean_value = left->data.real_value > right->data.int_value || fabs(left->data.real_value - right->data.int_value) < EPSILON;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            ge_op->type = BOOLEAN_TYPE;
            ge_op->data.boolean_value = left->data.real_value > right->data.real_value || fabs(left->data.real_value - right->data.real_value) < EPSILON;
      } else {
            yyerror("invalid type/s for expression >=");
      }

      return ge_op;
}

ExprResult *le_op(ExprResult *left, ExprResult *right) {
      ExprResult *le_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE && right->type == INT_TYPE) {
            le_op->type = BOOLEAN_TYPE;
            le_op->data.boolean_value = left->data.int_value <= right->data.int_value;
      } else if (left->type == INT_TYPE && right->type == REAL_TYPE) {
            le_op->type = BOOLEAN_TYPE;
            le_op->data.boolean_value = left->data.int_value < right->data.real_value || fabs(left->data.int_value - right->data.real_value) < EPSILON;
      } else if (left->type == REAL_TYPE && right->type == INT_TYPE) {
            le_op->type = BOOLEAN_TYPE;
            le_op->data.boolean_value = left->data.real_value < right->data.int_value || fabs(left->data.real_value - right->data.int_value) < EPSILON;
      } else if (left->type == REAL_TYPE && right->type == REAL_TYPE) {
            le_op->type = BOOLEAN_TYPE;
            le_op->data.boolean_value = left->data.real_value < right->data.real_value || fabs(left->data.real_value - right->data.real_value) < EPSILON;
      } else {
            yyerror("invalid type/s for expression <=");
      }

      return le_op;
}

ExprResult *con_op(ExprResult *left, ExprResult *right) {
      ExprResult *con_op = malloc(sizeof(ExprResult));

      if (left->type == STRING_TYPE && right->type == STRING_TYPE) {
            con_op->type = STRING_TYPE;
            char *new_str;
            new_str = malloc(strlen(left->data.string_value) + strlen(right->data.string_value));
            new_str[0] = '\0';
            strcat(new_str, left->data.string_value);
      
            strcat(new_str, right->data.string_value);
            con_op->data.string_value = new_str;
      } else {
            yyerror("invalid type/s for expression .");
      } 

      return con_op;
}

ExprResult *con_space_op(ExprResult *left, ExprResult *right) {
      ExprResult *con_op = malloc(sizeof(ExprResult));

      if (left->type == STRING_TYPE && right->type == STRING_TYPE) {
            con_op->type = STRING_TYPE;
            char *new_str;
            new_str = malloc(strlen(left->data.string_value) + 1 + strlen(right->data.string_value));
            new_str[0] = '\0';
            strcat(new_str, left->data.string_value);
            strcat(new_str, " ");
            strcat(new_str, right->data.string_value);
            con_op->data.string_value = new_str;
      } else {
            yyerror("invalid type/s for expression |");
      } 

      return con_op;
}

ExprResult *neg_op(ExprResult *left) {
      ExprResult *neg_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            neg_op->type = INT_TYPE;
            neg_op->data.int_value = -(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            neg_op->type = REAL_TYPE;
            neg_op->data.real_value = -(left->data.int_value);
      } else {
            yyerror("invalid type/s for expression -");
      }

      return neg_op;
}

ExprResult *fac_op(ExprResult *left) {
      ExprResult *fac_op = malloc(sizeof(ExprResult));
      if (left->type == INT_TYPE) {
            fac_op->type = INT_TYPE;
            int n = left->data.int_value;
            if (n < 0) yyerror("invalid type/s for expression !");

            int fact = 1;  
            for (int i = 1; i <= n; ++i) fact *= i;

            fac_op->data.int_value = fact;
      } else {
            yyerror("invalid type/s for expression !");
      }

      return fac_op;
}

ExprResult *ln_op(ExprResult *left) {
      ExprResult *ln_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            ln_op->type = REAL_TYPE;
            ln_op->data.real_value = log(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            ln_op->type = REAL_TYPE;
            ln_op->data.real_value = log(left->data.int_value);
      } else {
            yyerror("invalid type/s for expression ln");
      }

      return ln_op;
}

ExprResult *log10_op(ExprResult *left) {
      ExprResult *log10_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            log10_op->type = REAL_TYPE;
            log10_op->data.real_value= log10(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            log10_op->type = REAL_TYPE;
            log10_op->data.real_value = log10(left->data.real_value);
      } else {
            yyerror("invalid type/s for expression log10");
      }

      return log10_op;
}

ExprResult *sqrt_op(ExprResult *left) {
      ExprResult *sqrt_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            sqrt_op->type = REAL_TYPE;
            sqrt_op->data.real_value= sqrt(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            sqrt_op->type = REAL_TYPE;
            sqrt_op->data.real_value = sqrt(left->data.real_value);
      } else {
            yyerror("invalid type/s for expression sqrt");
      }

      return sqrt_op;
}

ExprResult *sin_op(ExprResult *left) {
      ExprResult *sin_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            sin_op->type = REAL_TYPE;
            sin_op->data.real_value= sin(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            sin_op->type = REAL_TYPE;
            sin_op->data.real_value = sin(left->data.real_value);
      } else {
            yyerror("invalid type/s for expression sin");
      }

      return sin_op;
}

ExprResult *cos_op(ExprResult *left) {
      ExprResult *cos_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            cos_op->type = REAL_TYPE;
            cos_op->data.real_value= cos(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            cos_op->type = REAL_TYPE;
            cos_op->data.real_value = cos(left->data.real_value);
      } else {
            yyerror("invalid type/s for expression cos");
      }

      return cos_op;
}

ExprResult *tan_op(ExprResult *left) {
      ExprResult *tan_op = malloc(sizeof(ExprResult));

      if (left->type == INT_TYPE) {
            tan_op->type = REAL_TYPE;
            tan_op->data.real_value= tan(left->data.int_value);
      } else if (left->type == REAL_TYPE) {
            tan_op->type = REAL_TYPE;
            tan_op->data.real_value = tan(left->data.real_value);
      } else {
            yyerror("invalid type/s for expression tan");
      }

      return tan_op;
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
	    case STRING_TYPE:
		  fprintf(fp, "string: %s\n", expr_result->data.string_value);
		  break;
	    case BOOLEAN_TYPE:
		  fprintf(fp, "boolean: %s\n", expr_result->data.boolean_value == TRUE ? "true" : "false");
		  break;
	    default:
		  fprintf(fp, "unknown type\n");   
		  break;   
      }

      fclose(fp);
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

      // It is important here to initialize the global scope before
      // starting the parsing.
      new_scope();
	parse(fileInput);
} 