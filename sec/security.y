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

%start security_spec

%token ENC REVEAL NAT

%token CONNECT BROADCAST

%token FULL UNI BI

%token NODE_NM VAR

%token VERIFIED PROVER VERIFIER MPC FOREACH IN

%token ATTACK CORRUPTIBLE

%token SEMI_HONEST SEMI_MAL MAL

%token CRAND BEAVER_TRIPLES SQ_TRIPLES OBLIV_TRANSFER OBLIV_LIN_EX ZERO_SHRS

%token SETUP PKI CRS_NIZK CRS_UC

%%

security_spec :
nodes_decl
connect_decl
reveal_decl
verified_decl
attack_decl
crand_decl
setup_decl
;

nodes_decl :
| node_decl nodes_decl
;

node_decl : NODE_NM opt_dim '{'
  ENC ':' NAT
'}'
;

opt_dim :
| '[' NAT ']'
;

connect_decl :
CONNECT '{'
  broadcast_opt
  link_clauses
'}'
;

broadcast_opt :
| BROADCAST ':' node_set
;

link_clauses :
| link_clause link_clauses
;

link_clause :
FULL ':' node_set
| node_set UNI node_set
| node_set BI node_set
;

node_set :
node_exp
| node_exp ',' node_set
;

node_exp : NODE_NM opt_access
;

opt_access :
| '[' NAT ']'
;

reveal_decl : REVEAL '{' link_clauses '}'
;

verified_decl : VERIFIED '{' ver_clauses '}'
;

ver_clauses :
| ver_clause ver_clauses
;

ver_clause :
'{' PROVER ':' mpc_opt node_set
    VERIFIER ':' node_set
'}'
| FOREACH VAR IN node_set ':' ver_clause
;

mpc_opt :
| MPC
;

attack_decl :
ATTACK '{'
  attack_clauses
'}'
;

attack_clauses :
| attack_clause attack_clauses
;

attack_clause : attack_model CORRUPTIBLE ':' '{' corruption_clauses '}'
;

attack_model :
SEMI_HONEST
| SEMI_MAL
| MAL
;

corruption_clauses :
corruption_clause
| corruption_clause ',' corruption_clauses
;

corruption_clause : node_set ':' nat_expr
;

nat_expr :
nat_term
| nat_term '+' nat_expr
| nat_term '-' nat_expr
;

nat_term :
nat_atom
| nat_atom '*' nat_term
| nat_atom '/' nat_term
;

nat_atom :
NAT
| 'n'
| '(' nat_expr ')'
;

crand_decl :
CRAND '{'
  crand_clauses
'}'
;

crand_clauses :
| crand_clause
;

crand_clause : crand ':' node_set
;

crand :
BEAVER_TRIPLES
| SQ_TRIPLES
| OBLIV_TRANSFER
| OBLIV_LIN_EX
| ZERO_SHRS
;

setup_decl :
SETUP '{'
  setup_clauses
'}'
;

setup_clauses :
| setup_clause setup_clauses
;

setup_clause : setup_class ':' node_set
;

setup_class :
PKI
| CRS_NIZK
| CRS_UC
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
  // TODO Bill replace these!
  if (reserved("principal")) { return PRINCIPAL; }
  if (reserved("def")) { return DEF; }
  if (reserved("import")) { return IMPORT; }
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

  if (reserved("auto")) { return AUTO; }
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
