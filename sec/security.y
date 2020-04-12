%start security_spec

%token NAT

%token CONNECT

%token FULL UNI BI

%token NODE_NM

%token SECURITY CORRUPTIBLE

%token SEMI_HONEST SEMI_MAL MAL

%%

security_spec : nodes_decl connect_decl security_decl
;

nodes_decl :
| node_decl nodes_decl
;

node_decl : NODE_NM opt_dim
;

opt_dim :
| '[' NAT ']'
;

connect_decl :
CONNECT '{'
connect_clauses
'}'
;

connect_clauses :
| connect_clause connect_clauses
;

connect_clause :
FULL ':' node_set
| node_set UNI node_set
| node_set BI node_set
;

node_set :
NODE_NM
| NODE_NM ',' node_set
;

security_decl :
SECURITY '{'
  attack_model CORRUPTIBLE ':' '{' attack_clauses '}'
'}'
;

attack_model :
SEMI_HONEST
| SEMI_MAL
| MAL
;

attack_clauses :
attack_clause
| attack_clause ',' attack_clauses
;

attack_clause : node_set ':' nat_expr
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
