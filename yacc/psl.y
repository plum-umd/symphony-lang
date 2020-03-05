%token DIGIT LETTER CONS

%%

var : LETTER vartail ;

vartail : DIGIT vartail | LETTER vartail | /* empty */ ;

// sequence of applications
expr : nonapp apptail ;

apptail : nonapp apptail | /* empty */ ;

nonapp : var
       | 'let' pat '=' expr 'in' expr
       | 'let' var ':' type 'in' expr
       | 'case' expr '{' arms '}'
       | 'fun' pat '->' expr // TODO there is a bug in PSL parser?
       | '(' expr ')'
       /* numbers TODO */
       | '(' ')'
       | '[' ']'
       | expr CONS expr
       | expr ',' expr
       | expr ':' type
       ;

// case analysis arms
arms : arm armstail | /* empty */ ;

arm : pat '->' expr

armstail : ';' arm armstail | /* empty */ ;

pat : var                     // pattern variable
    | '(' ')'                 // unit
    | pat ',' pat             // pair
    | '[' ']'                 // nil
    | pat CONS pat          // cons
    | '<<>>'                  // empty tuple
    /* << prin . pat >> ++ */ // principal
    | pat ':' type            // type annotation
    | '_'                     // wildcard
    | '(' pat ')'
    | '[' patlist ']'
    ;

patlist : pat patlisttail | /* empty */ ;

patlisttail : ';' pat patlisttail | /* empty */ ;

type : var
     ;

%%

yylex() {
  int c;

  // TODO token CONS

  while((c=getchar()) == ' ')  {
    /*  skip  blanks  */
  }

  if (islower(c)) { return LETTER; }
  else if (isdigit(c)) { return DIGIT; }
  else { return c; }
}
