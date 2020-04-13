%start security_spec

%token ENC REVEAL NAT

%token CONNECT BROADCAST

%token FULL UNI BI

%token NODE_NM

%token ATTACK CORRUPTIBLE

%token SEMI_HONEST SEMI_MAL MAL

%token CRAND BEAVER_TRIPLES SQ_TRIPLES OBLIV_TRANSFER OBLIV_LIN_EX ZERO_SHRS

%token SETUP PKI CRS_NIZK CRS_UC

%%

security_spec :
nodes_decl
connect_decl
reveal_decl
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

connect_decl : CONNECT '{'
  broadcast_opt
  link_clauses '}'
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
NODE_NM
| NODE_NM ',' node_set
;

reveal_decl : REVEAL '{' link_clauses '}'
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
