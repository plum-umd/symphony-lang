%{
#include <ctype.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
FILE *yyin;
void yyerror (char const *s) {
  char next[30];
  fread(next, 1, 30, yyin);
  fprintf (stderr, "%s at: %s\n", s, next);
  exit(0);
}
int yylex();
%}

%start toplist

%token PRINCIPAL DEF
%token VAR
%token CONS NIL UNIT
%token IF THEN ELSE CASE
%token LET IN FUN DO
%token BOT
%token SWAP

%token EQL LT LTE GT GTE
%token MOD PLUS MINUS TIMES DIV EXP
%token AND OR
%token PLUSPLUS

%token ARROW ASSIGN
%token MUX PAR REVEAL SHARE SEND SOLO AS READ
%token YAO BGV BGW GMW SPDZ ISEC SSEC
%token INTLIT NATLIT FLOATLIT STRINGLIT
%token INP REV
%token RANDRANGE

%token FORALL TYPE PRIN PRINS

%token EMPTYPRINS UNION EMPTYSET

%token LLANGLE RRANGLE

%%

toplist : | top toplist

top : PRINCIPAL prin prinlist
    | DEF VAR patlist '=' topexpr
    | DEF VAR ':' type
    ;

prinlist : | prin prinlist ;

prin : VAR | VAR ',' prin | VAR '[' expr ']';

patlist : | pat patlist ;

pat : VAR
    | UNIT
    | NIL
    | '(' pat commapat ')'
    | EMPTYPRINS
    | EMPTYSET
    | LLANGLE VAR '|' VAR RRANGLE
    | '{' prin '}'
    | pat PLUSPLUS pat
    | pat UNION pat
    | pat CONS pat
    | '[' pat ']'
    ;

commapat : | ',' pat commapat ;

topexpr : expr
        | LET pat commapat '=' expr lettail
        | LET VAR ':' type lettail
        | DO topexpr lettail
        | VAR ASSIGN expr
        ;

lettail : IN topexpr | topexpr ;


// sequence of applications
expr : nonapp apptail ;

apptail : nonapp apptail | /* empty */ ;

binop : EQL | LT | GT | LTE | GTE
      | MOD | PLUS | MINUS | TIMES | DIV | EXP
      | AND | OR
      | PLUSPLUS
      ;

protocol : YAO | BGV | BGW | GMW | SPDZ | ISEC | SSEC ;

nonapp : atom
       | MUX IF expr THEN topexpr ELSE topexpr
       | IF expr THEN topexpr ELSE topexpr
       | CASE atom '{' arms '}'
       | expr binop expr
       | expr '?' expr SWAP expr
       | expr ',' expr
       | PAR '{' prin '}' topexpr
       | REVEAL '{' prin '}' expr
       | SHARE '{' protocol ':' prin ARROW prin '}' expr
       | SEND '{' prin ARROW prin '}' expr
       | SOLO '{' prin '}' AS VAR IN expr
       | FUN recbinding patlist ARROW topexpr
       | READ typenonapp expr
       | RANDRANGE typenonapp expr
       | expr CONS expr
       ;

atom : VAR
     | BOT
     | '(' topexpr ')'
     | '{' expr '}'
     | '[' expr vecexpr ']'
     | LLANGLE VAR '|' expr RRANGLE
     | '!' atom
     | INTLIT | NATLIT | FLOATLIT | STRINGLIT
     | UNIT
     | NIL
     | EMPTYSET
     | atom '@' atom
     ;

vecexpr : | ';' expr vecexpr ;


recbinding : '[' VAR ']' | ;

arms : arm armstail ;

arm : pat ARROW topexpr ;

armstail : ';' arm armstail | ;

type : typenonapp typetail
     | FORALL quantifier quantifiers '.' type
     ;

quantifiers : ',' quantifier quantifiers | ;

quantifier : VAR ':' kind

kind : TYPE | PRINS | PRIN

typetail : typenonapp typetail | ;

typenonapp : typeatom
           | type ARROW type
           | type TIMES type
           | type ':' kind
           | type '|' constraint
           ;

constraint : type LTE type

typeatom : VAR
         | '{' INP ':' prin ';' REV ':' prin '}' typeatom
         | typeatom '{' protocol ':' prin '}'
         | typeatom '{' prin '}'
         | '(' type ')'
         | UNIT
         | '{' prin '}'
         | PRIN
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
  int is_neg = 0;
  if (peek() == '-') {
    get();
    is_neg = 1;
  }
  if (!number()) {
    if (is_neg) { back(1); }
    return 0;
  }
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
  if (reserved("do")) { return DO; }

  if (reserved("if")) { return IF; }
  if (reserved("case")) { return CASE; }
  if (reserved("then")) { return THEN; }
  if (reserved("else")) { return ELSE; }

  if (reserved("mux")) { return MUX; }
  if (reserved("par")) { return PAR; }
  if (reserved("reveal")) { return REVEAL; }
  if (reserved("share")) { return SHARE; }
  if (reserved("send")) { return SEND; }
  if (reserved("solo")) { return SOLO; }
  if (reserved("as")) { return AS; }
  if (reserved("read")) { return READ; }
  if (reserved("rand-range")) { return RANDRANGE; }

  if (reserved("yao")) { return YAO; }
  if (reserved("bgw")) { return BGW; }
  if (reserved("bgv")) { return BGV; }
  if (reserved("gmw")) { return GMW; }
  if (reserved("spdz")) { return SPDZ; }
  if (reserved("isec")) { return ISEC; }
  if (reserved("ssec")) { return SSEC; }

  if (reserved("inp")) { return INP; }
  if (reserved("rev")) { return REV; }

  if (reserved("type")) { return TYPE; }
  if (reserved("prin")) { return PRIN; }
  if (reserved("prins")) { return PRINS; }
  if (reserved("forall")) { return FORALL; }

  if (match("()")) { return UNIT; }
  if (match("{}")) { return EMPTYPRINS; }
  if (match("::")) { return CONS; }
  if (match("[]")) { return NIL; }
  if (match("<<>>")) { return EMPTYSET; }
  if (match("\\/")) { return UNION; }

  if (match("->")) { return ARROW; }
  if (match(":=")) { return ASSIGN; }

  if (match("><")) { return SWAP; }
  if (match("++")) { return PLUSPLUS; }
  if (match("_|_")) { return BOT; }
  if (match("==")) { return EQL; }
  if (match("<<")) { return LLANGLE; }
  if (match(">>")) { return RRANGLE; }
  if (match("<=")) { return LTE; }
  if (match("<")) { return LT; }
  if (match(">=")) { return GTE; }
  if (match(">")) { return GT; }
  if (match("%")) { return MOD; }
  if (match("+")) { return PLUS; }
  if (match("*")) { return TIMES; }
  if (match("/")) { return DIV; }
  if (match("^")) { return EXP; }
  if (match("&&")) { return AND; }
  if (match("||")) { return OR; }

  int n = numeric(); if (n > 0) { return n; }
  if (match("-")) { return MINUS; }

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
  if (match("{-")) {
    while (!(match("-}")) && peek() != EOF) {
      get();
    }
    get(); get();
    return 1;
  }

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
