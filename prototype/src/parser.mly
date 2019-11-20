/* 
 * Yacc grammar for the parser. The files parser.mli and parser.ml
 * are generated automatically from parser.mly.
 */

%{
  open Syntax
%}

%token <string> IDENT OPER IOPER FILENAME LABEL
%token TYPEFROM 
%token PROOFOF
%token DEFINITION VARIABLE AXIOM INDUCTIVE THEORY THEOREM
%token COMBINES MIXIN WITH OVER THEOREM ENRICH TO INJECT VIA INTO VIEW
%token USE LET
%token INSTANCE OF
%token DATA CODATA
%token CASE LIFT
%token FACT CONCEPT TRANSFORMER AS BY EXTENDED IMPORT CONSERVATIVELY
%token BAR TYPEPLUS QUESTION TYPE SUBTYPE
%token FORALL EXISTS IN AND IMPLIES NOT IOTA EPSILON IFF EXISTSUNIQ LAMBDA
%token TLAMBDA
%token POWER LQUOTE RQUOTE
%token TRUE FALSE UNDERSCORE IF THEN ELSE MEMBER
%token COLONEQUAL COLON COMMA ARROW DOT EQUAL OR SEMICOLON DOUBLESEMI
%token LPAREN RPAREN
%token LBRACE RBRACE LEVAL REVAL REVALAT LESCAPE RESCAPE AMPERSAND
%token LSQUARE RSQUARE 
%token PARCOMP ARROWID ACCESSORS
%token REALM WORLD
%token EOF                  /* End of file/

%right DOUBLESEMI            /* lowest */
%right SEMICOLON
%right EXTENDED
%nonassoc DEFINITION THEORY INDUCTIVE COMBINES
%nonassoc LSQUARE RSQUARE
%nonassoc COLONEQUAL
%nonassoc TO VIA
%nonassoc TRUE FALSE
%nonassoc SUBTYPE COLON
%right REVALAT
%left QUESTION
%left WITH
%left PARCOMP
%right IN
%right THEN ELSE
%right FORALL EXISTS IOTA EPSILON EXISTSUNIQ LAMBDA TLAMBDA
%right DOT
%nonassoc MEMBER
%right COMMA ARROW
%left AND
%left OR
%left IFF
%right IMPLIES
%nonassoc NOT
%right EQUAL
%right LET
%nonassoc OPER UNDERSCORE
%nonassoc IDENT LABEL
%nonassoc IOPER
%right LBRACE LPAREN
%left APPL
%nonassoc RPAREN RBRACE
%nonassoc EOF

%start main                          /* entry point */
%type <Syntax.toplevel_expr> main    /* the parser will return an Abstract Syntax Tree */

%%

/* Main body of the parser definition */
main:
  | toplevel_expr EOF                                  { $1 }
;

toplevel_expr:
  | /* empty */                                        { [] }
  | declarations toplevel_expr                         { $1 :: $2}
;

atom:
  | IDENT                                              { Ident $1 }
  | LPAREN OPER RPAREN                                 { Ident $2 }
  | LABEL                                              { Ident $1 }
  | p_strict_expr_list                                 { Tuple $1 }
  | b_record_list                                      { Record $1 }
  | LPAREN expr RPAREN                                 { $2 }
  | LESCAPE expr RESCAPE                               { Escape $2 }
  | LQUOTE expr RQUOTE                                 { Quote $2 }
  | LEVAL expr REVALAT full_type                       { Eval($2, $4) }
  | TRUE                                               { BTrue }
  | FALSE                                              { BFalse }
;

expr:
  | expr AND expr                                      { And ($1, $3) }
  | expr OR  expr                                      { Or ($1, $3) }
  | expr IMPLIES expr                                  { Implies ($1, $3) }
  | expr IFF expr                                      { Iff ($1, $3) }
  | NOT expr                                           { Not $2 }
  | atom                                               { $1 }
  | quantifier                                         { $1 }
  | relation_expr                                      { $1 }
  | application_expr                                   { $1 }
  | oper_expr                                          { $1 }
  | expr DOT io                                        { Selector ($1, $3) }
  | expr MEMBER full_type                              { In ($1, $3) }
  | LET IDENT EQUAL expr IN expr                       { Let ($2, $4, $6) }
  | CASE expr OF cases                                 { Case( $2, $4) }
  | IF expr THEN expr ELSE expr                        { If($2, $4, $6) }
  | LAMBDA var_spec_optional_type DOT expr             { Binder(Abs, $2, $4) }
;

quantifier:
  | forall_expr                                        { $1 }
  | exists_expr                                        { $1 }
  | iota_expr                                          { $1 }
  | epsilon_expr                                       { $1 }
;

forall_expr:
  | FORALL var_spec DOT expr                     { Binder(Forall, $2, $4) }
;

exists_expr:
  | EXISTS var_spec DOT expr                     { Binder(Exists, $2, $4) }
  | EXISTSUNIQ var_spec DOT expr                 { Binder(ExistsUniq, $2, $4) }
;

iota_expr:
  | IOTA IDENT COLON full_type DOT expr                    { Desc (Iota, $2, $4, $6) }
;

epsilon_expr:
  | EPSILON IDENT COLON full_type DOT expr                 { Desc (Epsilon, $2, $4, $6) }
;

relation_expr:
  | expr EQUAL expr                                    { EqOp ($1, $3) }
;

cases:
  | LBRACE RBRACE                                      { [] }
  | LBRACE case_list RBRACE                            { $2 }
;

case_list:
  | case                                               { [ $1 ] }
  | case case_list                                     { $1 :: $2 }
;

case:
  | BAR pattern ARROW expr                             { Branch ($2,$4) }
;

base_pat:
  | IDENT                                              { PatIdent $1 }
  | OPER                                               { PatIdent $1 }
  | LABEL                                              { PatConst $1 }
  | UNDERSCORE                                         { PatNone }
;

pattern_list:
  | pattern                                            { [$1] }
  | pattern COMMA pattern_list                         { $1 :: $3 }
;

pat_record_list:
  | IDENT EQUAL pattern                                { [($1,$3)] }
  | OPER  EQUAL pattern                                { [($1,$3)] }
  | IDENT EQUAL pattern COMMA pat_record_list          { ($1,$3)::$5 }
  | OPER  EQUAL pattern COMMA pat_record_list          { ($1,$3)::$5 }
;

pattern:
  | base_pat                                           { $1 }
  | LPAREN pattern RPAREN                              { $2 }
  | pattern pattern %prec APPL                         { PatApp($1, $2) }
  | LPAREN pattern COMMA pattern_list RPAREN           { PatTuple($2 :: $4) }
  | LBRACE RBRACE                                      { PatRecord [] }
  | LBRACE pat_record_list RBRACE                      { PatRecord $2 }
;

var_spec:
  | ident_list COLON full_type                         { VarSpec ($1, Some $3) }
;

var_spec_optional_type:
  | ident_list                                         { VarSpec ($1, None) }
  | ident_list COLON full_type                         { VarSpec ($1, Some $3) }
;

ident_list:
  | io                                                 { [$1] }
  | LPAREN OPER RPAREN                                 { [$2] }
  | IDENT COMMA ident_list                             { $1 :: $3 }
  | OPER COMMA ident_list                              { $1 :: $3 }
;


io:
  | IDENT                                              { $1 }
  | OPER                                               { $1 }
;

iol:
  | IDENT                                              { $1 }
  | OPER                                               { $1 }
  | LABEL                                              { $1 }
;

id_eq:
  | iol TO iol                                         { ($1, $3) }
;

id_eq_list:
  | id_eq %prec TO                                     { [ $1 ]}
  | id_eq COMMA id_eq_list                             { $1 :: $3 }
;

expr_list:
  | expr                                               { [$1] }
  | expr COMMA expr_list                               { $1 :: $3 }
;

record_list:
  | field_mem                                          { [$1] }
  | field_mem COMMA record_list                        { $1 :: $3 }
;

b_record_list:
  | LBRACE RBRACE                                      { [] }
  | LBRACE record_list RBRACE                          { $2 }
;

p_strict_expr_list:
  | LPAREN expr COMMA expr_list RPAREN                 { $2 :: $4 }
;

p_ident_list:                                          /* paren ident list */
  | LPAREN ident_list RPAREN                           { $2 }
;

subst_list:
  | single_subst                                       { [$1] }
  | single_subst COMMA subst_list                      { $1 :: $3 }
;

single_subst:
  | IDENT TO expr                                      { Subst($1,$3) }
  | IDENT TO OPER                                      { Subst($1,Ident $3) }
;

application_expr:
  | atom atom                                          { Appl (false, $1, $2) }
  | application_expr atom                              { Appl (false, $1, $2) }
;

oper_expr:
  | expr inline_oper atom %prec APPL                   { Appl (true, Ident($2), Tuple([$1;$3]) ) }
;

param_decl:
  | IDENT                                              { PConst $1 }
  | IDENT p_ident_list %prec APPL                      { mkPApp false $1 $2 }
  | IDENT inline_oper IDENT                            { mkPApp true $2 [$1; $3] }
;

pident:
  | LPAREN IDENT RPAREN                                { $2 }
;

inline_oper:
  | OPER                                               { $1 }
  | IOPER                                              { cut_first ($1) }
;

tident:
  | ident_list COLON full_type                         { build_type $3 $1 }
  | pident COLON full_type                             { TBase ($1, mkType $3) }
;

tident_list2:
  | tident                                             { [$1] }
  | tident COMMA tident_list2                          { $1 :: $3 }
;

record_field_list:
  | record_field_sig                                   { [$1] }
  | record_field_sig COMMA record_field_list           { $1 :: $3 }
;

thyident:
  | IDENT COLON IDENT                                  { ($1, $3) }

top_type:
  | thyident                                           { [$1] }
  | thyident COMMA top_type                            { ($1) :: $3 }
;

full_type:
  | TYPE                                               { Type }
  | type2                                              { $1 }
  | full_type ARROW full_type                          { TArrow ($1, $3) }
  | full_type QUESTION                                 { TPredicate $1 }
  | LPAREN full_type RPAREN                            { $2 }
  | TLAMBDA var_spec_optional_type DOT full_type       { TBinder($2, $4) }
  | LBRACE record_field_list RBRACE                    { TRecord $2 }
  | POWER IDENT                                        { TPower (TId $2) }
  | POWER LPAREN full_type RPAREN                      { TPower $3 }
  | AMPERSAND IDENT                                    { TTheory $2 }
  | PROOFOF LPAREN expr RPAREN                         { TProof $3 }
;

type2:
  | typeapp                                            { $1 }
  | LPAREN IDENT COLON full_type RPAREN                { TDepId ($2,$4) }
  | LPAREN type_seq1 RPAREN                            { TProd $2 }
  | LPAREN DATA IDENT DOT typespec RPAREN              { TInduct ($3,$5) }
  | LIFT atom                                          { TLift $2 }
;

typeapp: /* type7 */
  | type8                                              { $1 }
  | typeapp type8 %prec APPL                           { TApp ($1, $2) }
  | typeapp LPAREN full_type RPAREN %prec APPL         { TApp ($1, $3) }
;

type8:
  | IDENT                                              { TId $1 }
  | OPER                                               { TLift (Ident $1) }
;

top_full_type:
  | full_type                                          { $1 }
  | DATA IDENT DOT typespec                            { TInduct ($2, $4) }
  | TYPEFROM LPAREN IDENT RPAREN                       { TTypeFromTheory $3} 
;

record_field_sig:
  | IDENT COLON full_type                              { FieldSig ($1,$3) }
  | OPER COLON full_type                               { FieldSig ($1,$3) }
;

induct_field_sig:
  | LABEL COLON full_type                              { FieldSig ($1,$3) }
;

field_mem:
  | io COLON full_type EQUAL expr                      { FieldMem ($1, Some $3, $5) }
  | io EQUAL expr                                      { FieldMem ($1, None, $3) }
;

typespec:
  | induct_field_sig                                   { [ $1 ] }
  | induct_field_sig BAR typespec                      { $1 :: $3 }
;

type_seq1:
  | full_type COMMA type_seq0                          { $1 :: $3 }
;

type_seq0:
  | full_type                                          { [$1] }
  | full_type COMMA type_seq0                          { $1 :: $3 }
;

type_defn:
  | TYPE IDENT EQUAL top_full_type                     { TypDecl (TBase( $2, mkManifest $4) ) }
  | IDENT SUBTYPE full_type                            { TypDecl (TBase( $1, mkSubtype $3)) }
;

induct_declaration:
  | INDUCTIVE IDENT                                    { Induct ($2, []) }
  | INDUCTIVE IDENT BAR typespec                       { Induct ($2, $4) }
;

single_declaration:
  | typ_declaration                                    { $1 }
  | type_defn                                          { $1 }
  | func_defn_declaration                              { $1 }
  | axiom_declaration                                  { $1 }
  | induct_declaration                                 { $1 }
  | var_declaration                                    { $1 }

declaration:
  | single_declaration SEMICOLON declaration           { ($1::$3) }
  | single_declaration SEMICOLON                       { [$1] }
  | single_declaration                                 { [$1] }
;
 
func_defn_declaration:
  | func_defn                                          { FuncDecl $1 }
;

func_defn:
  | param_decl EQUAL expr                                { ($1, $3) }
;

typ_declaration:
  | tident                                             { TypDecl $1 }
;

var_declaration:
  | VARIABLE tident_list2                              { VarDecl $2 }
;

single_fact:
  | AXIOM COLON expr                                   { (None,$3,true) }
  | AXIOM io COLON expr                                { (Some $2,$4,true) }
  | THEOREM COLON expr                                 { (None,$3,false) }
  | THEOREM io COLON expr                              { (Some $2,$4,false) }
;

axiom_declaration:
  | single_fact                                        { Axiom $1 }
;

declarations:
  | IDENT COLONEQUAL 
    INSTANCE IDENT OF IDENT VIA LSQUARE subst_list RSQUARE { NamedArrow($1, AInstance($4, $6, $9)) }
  | IDENT COLONEQUAL arrow                             { NamedArrow($1,$3) }
  | IDENT COLONEQUAL thy_expr                          { NamedArrow( $1, AThy $3) }
  | IDENT COLONEQUAL subst                             { NamedSubst( $1, $3) }
  /* | IDENT COLONEQUAL REALM FROM ident_list LBRACE export_list RBRACE { NamedRealm ($1, $5, $7) } */
;
/* original realm syntax was
   realm groups from T*
       (export w from t as g)* */
  
arrow_comp:
  | IDENT SEMICOLON IDENT                              { [$1; $3 ] }
  | IDENT SEMICOLON arrow_comp                         { $1 :: $3 }
;

extension:
  | IDENT EXTENDED LBRACE declaration RBRACE        { AExtend ($1,General,$4) }
  | IDENT EXTENDED BY LBRACE declaration RBRACE     { AExtend ($1,General,$5) }
  | IDENT EXTENDED CONSERVATIVELY BY LBRACE declaration RBRACE
                                                       { AExtend ($1, Conservative,$6) }
;

rename:
  | IDENT LSQUARE id_eq_list RSQUARE                   { ($1, $3) }
;

arrow:
  | IDENT                                              { ArrowName $1 }
  | ARROWID                                            { ArrowId }
  | LPAREN arrow_comp RPAREN                           { mkSeqComp $2 }
  | IDENT PARCOMP IDENT                                { AParComp($1, $3) }
  | extension                                          { $1 }
  | COMBINES ident_list OVER IDENT %prec EXTENDED      { ACombine ($2, $4) }
  | MIXIN rename COMMA rename                          { AMixin ($2,$4) }
  | rename                                             { ARename $1 }
;

subst:
  | LSQUARE subst_list RSQUARE                          { $2 }
;

thy_expr:
  | THEORY LBRACE RBRACE                               { [] }
  | THEORY LBRACE declaration RBRACE                   { $3 }
  | THEORY LPAREN top_type RPAREN LBRACE declaration RBRACE                   
      { failwith "Theory Functor syntax reserved for future use" }
;

%%
