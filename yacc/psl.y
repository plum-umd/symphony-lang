%{
#include <ctype.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
FILE *yyin;
void yyerror (char const *s) {
  char next[20];
  fread(next, 1, 20, yyin);
  fprintf (stderr, "%s at: %s\n", s, next);
  exit(0);
}
int yylex();
%}

%start toplist

%token PRINCIPAL DEF
%token VAR
%token CONS NIL UNIT
%token IF THEN ELSE
%token LET IN FUN
%token EQL LT LTE GT GTE
%token MOD PLUS MINUS TIMES DIV
%token ARROW
%token MUX PAR REVEAL SHARE
%token YAO BGV BGW GMW ;
%token INTLIT NATLIT FLOATLIT STRINGLIT
%token INP REV
%token RANDRANGE

%%

toplist : | top toplist
/* toplist : expr */

top : PRINCIPAL prin prinlist
    | DEF VAR patlist '=' topexpr
    | DEF VAR ':' type
    ;

prinlist : | prin prinlist ;

prin : VAR | VAR ',' prin ;

patlist : | pat patlist ;

pat : VAR                     // pattern variable
    | UNIT                    // unit
    | NIL                     // nil
    | '(' pat commapat ')'
    /* | pat CONS pat            // cons */
    /* | '<<>>'                  // empty tuple */
    /* << prin . pat >> ++ */ // principal
    /* | pat ':' type            // type annotation */
    /* | NIL */
    ;

commapat : | ',' pat commapat ;

topexpr : let | expr ;

// sequence of applications
expr : nonapp apptail ;

apptail : nonapp apptail | /* empty */ ;

binop : EQL | LT | GT | LTE | GTE
      | MOD | PLUS | MINUS | TIMES | DIV ;

protocol : YAO | BGV | BGW | GMW ;

nonapp : VAR
       | MUX IF expr THEN topexpr ELSE topexpr
       | IF expr THEN topexpr ELSE topexpr
       | expr binop expr
       | expr ',' expr
       | PAR '{' prin '}' topexpr
       | REVEAL '{' prin '}' expr
       | SHARE '{' protocol ':' prin ARROW prin '}' expr
       /* | 'case' expr '{' arms '}' */
       | FUN recbinding patlist ARROW topexpr // TODO there is a bug in PSL parser?
       | '(' topexpr ')'
       | INTLIT | NATLIT | FLOATLIT | STRINGLIT
       | UNIT
       | NIL
       | RANDRANGE typenonapp expr
       /* | expr CONS expr */
       /* | expr ':' type */
       ;

let : LET pat commapat '=' expr lettail ;

lettail : IN topexpr | let ;

recbinding : '[' VAR ']' | ;


/* // case analysis arms */
/* arms : arm armstail | /1* empty *1/ ; */

/* arm : pat '->' expr */

/* armstail : ';' arm armstail | /1* empty *1/ ; */

type : typenonapp typetail ;

typetail : typenonapp typetail | ;

typenonapp : VAR
           | typenonapp '{' protocol ':' prin '}'
           | type ARROW type
           | '{' INP ':' prin ';' REV ':' prin '}' type
           | '(' type ')'
           ;

%%

int get() { return fgetc(yyin); }
int unget(int c) { return ungetc(c, yyin); }


int peek() {
  int c = get();
  if (c != EOF) { unget(c); }
  return c;
}

void back(int distance) {
  int c = peek();
  fseek(yyin, 0-distance , SEEK_CUR);
}


int match(const char* s) {
  int pos = 0;
  char c;
  while (s[pos] != '\0') {
    if (peek() != s[pos]) {
      back(pos);
      return 0;
    }
    get();
    ++pos;
  }
  return 1;
}


int isvarchar(int c) {
  return isdigit(c) || isalpha(c) || c == '_' || c == '-' || c == '\'';
}


int reserved(const char* s) {
  if (match(s)) {
    if (isvarchar(peek())) {
      back(strlen(s));
      return 0;
    } else {
      return 1;
    }
  }
  return 0;
}


int number() {
  if (!isdigit(peek())) {
    return 0;
  }
  get();
  while (isdigit(peek())) {
    get();
  }
  return 1;
}


int stringlit() {
  if (peek() == '"') {
    do {
      int c = peek();
      if (c == EOF || c == '\n') {
        yyerror("Unterminated string");
      }
      if (c == '\\') {
        get();
        get();
      } else {
        get();
      }
    } while (peek() != '"');
    get();
    return 1;
  } else {
    return 0;
  }
}


int numeric() {
  if (!number()) { return 0; }
  if (peek() == 'n') {
    get();
    return NATLIT;
  }
  if (peek() == '.') {
    get();
    if (!number()) {
      yyerror("Floating point with no number after '.'");
    }
    return FLOATLIT;
  }
  if (isvarchar(peek())) {
    yyerror("number with trailing alpha characters");
  }
  return INTLIT;
}


int token() {
  if (reserved("principal")) { return PRINCIPAL; }
  if (reserved("def")) { return DEF; }
  if (reserved("fun")) { return FUN; }
  if (reserved("let")) { return LET; }
  if (reserved("in")) { return IN; }

  if (reserved("if")) { return IF; }
  if (reserved("then")) { return THEN; }
  if (reserved("else")) { return ELSE; }

  if (reserved("mux")) { return MUX; }
  if (reserved("par")) { return PAR; }
  if (reserved("reveal")) { return REVEAL; }
  if (reserved("share")) { return SHARE; }

  if (reserved("yao")) { return YAO; }
  if (reserved("bgw")) { return BGW; }
  if (reserved("bgv")) { return BGV; }
  if (reserved("gmw")) { return GMW; }

  if (reserved("rand-range")) { return RANDRANGE; }

  if (reserved("inp")) { return INP; }
  if (reserved("rev")) { return REV; }

  if (match("()")) { return UNIT; }
  if (match("::")) { return CONS; }
  if (match("[]")) { return NIL; }

  if (match("->")) { return ARROW; }

  if (match("==")) { return EQL; }
  if (match("<")) { return LT; }
  if (match("<=")) { return LTE; }
  if (match(">")) { return GT; }
  if (match(">=")) { return GTE; }
  if (match("%")) { return MOD; }
  if (match("+")) { return PLUS; }
  if (match("-")) { return MINUS; }
  if (match("*")) { return TIMES; }
  if (match("/")) { return DIV; }

  int n = numeric(); if (n > 0) { return n; }
  if (stringlit()) { return STRINGLIT; }
  int c = get();
  if (isalpha(c) || c == '_') {
    while (isvarchar(peek())) {
      get();
    }
    return VAR;
  }
  if (c == EOF) { return 0; }
  return c;
}

int comment() {
  if (match("--")) {
    while (peek() != '\n' && peek() != EOF) {
      get();
    }
    return 1;
  }
  return 0;
}

int space() {
  int res = 0;
  while (isspace(peek())) {
    res = 1;
    get();
  }
  return res;
}


int yylex() {
  while (comment() || space()) { }
  return token();
}

void usage(char* name) {
  fprintf(stderr, "Usage: %s <filename>\n", name);
  exit(0);
}

int main(int argc, char **argv) {
  if (argc < 2) {
    usage(argv[0]);
  }
  yyin = fopen(argv[1], "r");
  if (!yyin) {
    fprintf(stderr, "Invalid filename: %s\n", argv[1]);
    usage(argv[0]);
  }
  int a = yyparse();
  puts("Good");
}
