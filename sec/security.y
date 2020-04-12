%start security_spec

%token ENC REVEALS NAT

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

node_decl : NODE_NM opt_dim '{'
  ENC ':' NAT
  REVEALS ':' node_set
'}'
;

opt_dim :
| '[' NAT ']'
;

connect_decl : CONNECT '{' connect_clauses '}'
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

security_decl : SECURITY '{' attack_clauses '}'
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
