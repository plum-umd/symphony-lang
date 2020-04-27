// grammar for the metadata rich backend description langauge

%token TOPOLOGY

%token BROADCAST CONNECT FULL UNI BI

%token SIZES

%token BOOL_NM FLT_NM IMPL INT_NM NAT_NM NAT PROTO PROTO_NM SRC_FILENM SYM_NM TYPES

%token MAL SEMI_HON SEMI_MAL

%token CORRUPT PARTIES ATTACKERS

%token OPS

%token CRAND GATES COMM ROUNDS MEM

%token BEAVER_TRIPLES SQ_TRIPLES OBLIV_TRANSFER OBLIV_LIN_EX ZERO_SHRS

%token SHARE REVEAL AND XOR PLUS MINUS MULT DIV

%start crypto_backend_spec

%%

 /* A spec is a 
  * 
  * 1. a declaration of a protocol name;
  * 
  * 2. a declaration of a source filename;
  * 
  * 3. a sequence of declarations of threat models: */
crypto_backend_spec :
  nm_decl
  file_decl
  topology_decl
  threat_decls
  ;

// A protocol name declaration is the constnat
nm_decl : PROTO ':' PROTO_NM
;

// File declaration:
file_decl : IMPL ':' SRC_FILENM
;

// Declaration of the party topology:
topology_decl :
TOPOLOGY '{'
  parties_decl
  sizes_decl
  connect_decl
'}' ;

parties_decl : PARTIES ':' party_seq
;

party_seq : PARTY_NM
| PARTY_NM ',' party_seq
;

sizes_decl :
SIZES '{'
  size_decls
'}' ;

size_decls :
| PARTY_NM : NAT size_decls
;

// connect_decl: declare required connections
connect_decl :
CONNECT '{'
  broadcast_opt
  link_clauses
'}' ;

broadcast_opt :
| BROADCAST ':' party_seq
;

link_clauses :
| link_clause link_clauses
;

link_clause :
FULL ':' party_seq
| party_seq UNI party_seq
| party_seq BI party_seq
;

// thread_models: a sequence of threat models
threat_decls :
| threat_decl threat_decls
;

threat_decl :
threat_model '{'
  attackers_decl
  share_ty_decls
  op_decls
'}'
;

threat_model :
  SEMI_HON
| SEMI_MAL
| MAL
;

// attackers_decl: declares a threshold on attackers
attackers_decl :
ATTACKERS '{'
  threshold_clauses
'}' ;

threshold_clauses :
| party_seq ':' threshold threshold_clauses
;

threshold : threshold_expr
;

threshold_expr :
  threshold_term
| threshold_term '+' threshold_expr
| threshold_term '-' threshold_expr
  ;

threshold_term :
  threshold_atom
| threshold_atom '*' threshold_term
| threshold_atom '/' threshold_term
  ;

threshold_atom :
  NAT
| 'n'
| '(' threshold ')'
  ;

share_ty_decls :
| share_ty_decl share_ty_decls
;

// share_ty_decl: declares a type of shares:
share_ty_decl :
TYPES '{'
  type_decls
'}' ;

type_decls :
| type_decl type_decls ;

type_decl :
base_ty '{'
  type_clauses
'}' ;

type_clauses :
| PARTY_NM ':' SYM_NM
;

base_ty :
BOOL_NM
| NAT_NM NAT
| INT_NM NAT
| FLT_NM NAT NAT
;

op_decls :
OPS '{'
  op_seq
'}';

op_seq : 
| op op_seq
;

// op_decl: declares operations over shares:
op : op_nm '{'
  IMPL ':' SYM_NM
  CRAND ':' crand_seq
  GATES ':' threshold
  COMM ':' threshold
  ROUNDS ':' threshold
  MEM ':' threshold
'}' ;

crand_seq :
| crand  crand_seq
;

crand :
BEAVER_TRIPLES
| SQ_TRIPLES
| OBLIV_TRANSFER
| OBLIV_LIN_EX
| ZERO_SHRS
;

// op_nm: a name of an operation
op_nm :
  SHARE base_ty
| REVEAL base_ty
| AND
| XOR
| PLUS base_ty
| MINUS base_ty
| MULT base_ty
| DIV base_ty
  ;
