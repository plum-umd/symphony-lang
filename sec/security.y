%start security_spec

%token ENC REVEAL NAT

%token CONNECT

%token FULL UNI BI

%token NODE_NM

%token SECURITY CORRUPTIBLE

%token SEMI_HONEST SEMI_MAL MAL

%%

security_spec : nodes_decl connect_decl reveal_decl security_decl
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

connect_decl : CONNECT '{' link_clauses '}'
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

security_decl :
SECURITY '{'
  attack_clauses
  crand_clauses
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

crand_clauses :
| crand_clause
;

crand_clause : 'crand' ':' node_set
