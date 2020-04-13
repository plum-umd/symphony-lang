// grammar for the metadata rich backend description langauge

%token BOOL_NM FLT_NM IMPL INT_NM NAT_NM NAT PROTO PROTO_NM SRC_FILENM SYM_NM 

%token MAL SEMI_HON 

%token CORRUPT PARTIES SECURITY 

%token ANY

%token CRAND GATES ROUNDS

%token BEAVER

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
crypto_backend_spec : nm_decl file_decl threat_decls
;

// A protocol name declaration is the constnat
nm_decl : PROTO ':' PROTO_NM
;

// File declaration:
file_decl : IMPL ':' SRC_FILENM
;

// thread_models: a sequence of threat models
threat_decls :
| threat_decl threat_decls
;

threat_decl :
threat_model '{'
sec_decl
share_ty_decls
op_decls
'}'
;

threat_model :
  SEMI_HON
| SEMI_MAL
| MAL
;

// sec_decl: declares security parameters:
sec_decl :
SECURITY '{'
PARTIES ':' party_num
CORRUPT ':' threshold
'}'
;

party_num :
NAT
| ANY
;

threshold : threshold_expr
;

threshold_exp :
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
SHARE base_ty ':' SYM_NM
;

base_ty :
BOOL_NM
| NAT_NM NAT
| INT_NM NAT
| FLT_NM NAT NAT
;

op_decls :
| op_decl op_decls
;

// op_decl: declares operations over shares:
op_decl : op_nm '{'
IMPL ':' SYM_NM
CRAND ':' crand_seq
GATES ':' NAT
ROUNDS ':' NAT
'}'
;

crand_seq :
| crand  crand_seq
;

crand : BEAVER
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
