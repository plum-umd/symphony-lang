// grammar for the metadata rich backend description langauge

%token ANY BASE_TY CORRUPT GATE_NM IMPL NAT OP_NM PARTIES RESOURCE_NM ROUNDS_NM SECURITY SRC_FILENM SYM_NM THREAT_MODEL

%%

 /* A spec is a source filename and a sequence of threat models
  *  declarations: */
start : file_src threat_decls ;

file_src : IMPL ':' SRC_FILENM ;

// thread_models: a sequence of threat models
threat_decls :
| threat_decl threat_decls
;

threat_decl : THREAT_MODEL '{'
sec_decl
share_ty_decls
op_decls
'}' ;

// sec_decl: declares security parameters:
sec_decl : SECURITY '{'
PARTIES ':' party_num
CORRUPT ':' threshold
'}'

party_num : NAT
| ANY
;

threshold : NAT
| 'n' '/' NAT
;

share_ty_decls :
| share_ty_decl share_ty_decls
;

// share_ty_decl: declares a type of shares:
share_ty_decl : BASE_TY ':' SYM_NM
;

op_decls :
| op_decl op_decls
;

// op_decl: declares operations over shares:
op_decl : OP_NM '{'
IMPL ':' SYM_NM
GATE_NM ':' NAT
ROUNDS_NM ':' NAT
'}'
;
