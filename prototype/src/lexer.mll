(* 
  The lexical analyzer: lexer.ml is generated automatically
  from lexer.mll
*)

{
  open Parser            (* The type token is defined in parser.mli *)
  open Lexing
  exception Lexical_error of string
  
  let kwd_tbl = ["axiom", AXIOM;
                 "theorem", THEOREM;
                 "Theory", THEORY;
                 "forall", FORALL;
                 "exist", EXISTS;
                 "exists", EXISTS;
                 "exist!", EXISTSUNIQ;
                 "exists!", EXISTSUNIQ;
                 "implies", IMPLIES;
                 "iota", IOTA;
                 "epsilon", EPSILON;
                 "not", NOT;
                 "combine", COMBINES;
                 "mixin", MIXIN;
                 "over", OVER;
                 "with", WITH;
                 "enrich", ENRICH;
                 "Inductive", INDUCTIVE;
                 "conservatively", CONSERVATIVELY;
                 "Concept", CONCEPT;
                 "Concepts", CONCEPT;
                 "concept", CONCEPT;
                 "concepts", CONCEPT;
                 "Transformer", TRANSFORMER;
                 "Transformers", TRANSFORMER;
                 "transformer", TRANSFORMER;
                 "transformers", TRANSFORMER;
                 "Definition", DEFINITION;
                 "Definitions", DEFINITION;
                 "definition", DEFINITION;
                 "definitions", DEFINITION;
                 "Fact", FACT;
                 "Facts", FACT;
                 "fact", FACT;
                 "facts", FACT;
                 "as", AS;
                 "by", BY;
                 "of", OF;
                 "if", IF;
                 "in", IN;
                 "let", LET;
                 "then", THEN;
                 "else", ELSE;
                 "via", VIA;
                 "into", INTO;
                 "extended", EXTENDED;
                 "variable", VARIABLE;
                 "variables", VARIABLE;
                 "lambda", LAMBDA;
                 "fun", LAMBDA;
                 "Lambda", TLAMBDA;
                 "type", TYPE;
                 "view", VIEW;
                 "View", VIEW;
                 "inject", INJECT;
                 "Inject", INJECT;
                 "data", DATA;
                 "codata", CODATA;
                 "case", CASE;
                 "instance", INSTANCE;
                 "power", POWER;
                 "lift", LIFT;
                 "#use", USE;
                 "TypeFrom", TYPEFROM;
                 "Id", ARROWID;
                 "%true", TRUE;
                 "%false", FALSE;
                 "accessors", ACCESSORS;
                 "realm", REALM;
                 "world", WORLD;
                 ]
  let id_or_kwd s = try List.assoc s kwd_tbl with _ -> IDENT (s)
    
  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
      pos_cnum=0
    }

  let incr_lineno lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <- { pos with
      pos_lnum = pos.pos_lnum + 1;
      pos_bol = pos.pos_cnum;
    }
}

(* assign names to commonly-used regular expressions *)

let alpha = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let tick = '`'
let symbol = '+' | '*' | '<' | '>' | '^' | '/' | '\\' | '#' | '_' | '@' | '-' |
'\'' | '=' | '|'
let alphanum = (alpha | digit)+
(* operators are made up of symbols, potentially with trailing digits *)
let oper  = symbol+ digit*

let alpha_ident = alphanum (('_' | '-')? (alphanum | oper) '\''?)*
let const = '%' alpha_ident

let ident = (alpha_ident ('?' | '!' | '\'' | '#')?) | ('\'' (([^'\'''\\']+ | ('\\'[^'\''])) ('\\' '\'')?)* '\'')
let inline_oper = tick alpha_ident
let label = '~' ( ident | oper )
let filename = '"' (alpha | digit | symbol | ':' | '.' )+ '"'

rule token = parse
  | '\n'                           { newline lexbuf; token lexbuf }
  | [' ' '\t' '\r']+               { token lexbuf }     (* skip blanks in dos and unix *)
  | "(@*"                          { comment 0 lexbuf}
  | ','                            { COMMA }
  | ":<"                           { SUBTYPE }
  | ':'                            { COLON }
  | ";;"                           { DOUBLESEMI }
  | ';'                            { SEMICOLON }
  | "->"                           { ARROW }
  | "|->"                          { TO }
  | "||"                           { PARCOMP }
  | '('                            { LPAREN }
  | ')'                            { RPAREN }
  | '{'                            { LBRACE }
  | '}'                            { RBRACE }
  | "[["                           { LEVAL }
  | "]]_"                          { REVALAT }
  | "]]"                           { REVAL }
  | "|_"                           { LESCAPE }
  | "_|"                           { RESCAPE }
  | "|^"                           { LQUOTE }
  | "^|"                           { RQUOTE }
  | '&'                            { AMPERSAND }
  | '['                            { LSQUARE }
  | ']'                            { RSQUARE }
  | '='                            { EQUAL }
  | '|'                            { BAR }
  | "or"                           { OR }
  | "and"                          { AND }
  | "iff"                          { IFF }
  | ":="                           { COLONEQUAL }
  | '.'                            { DOT }
  | "`in"                          { MEMBER }
  | inline_oper                    { IOPER (lexeme lexbuf) }
  | filename                       { let s = lexeme lexbuf in
                                     let l = String.length s in
                                     FILENAME (String.sub s 1 (l-2)) }
  | ident                          { id_or_kwd (lexeme lexbuf) }
  | oper                           { OPER (lexeme lexbuf) }
  | const                          { id_or_kwd (lexeme lexbuf) }
  | label                          { LABEL (lexeme lexbuf) }
  | '?'                            { QUESTION }
  | '_'                            { UNDERSCORE }
  | eof                            { EOF }
  | _                              { raise (Lexical_error ("Illegal character '"
  ^ (lexeme lexbuf) ^ "'")) } 
and comment level = parse 
  | "*@)"                          { if level = 0 then token lexbuf else
                                                       comment (level-1) lexbuf}
  | "(@*"                          { comment (level+1) lexbuf }
  | '\n'                           { newline lexbuf; comment level lexbuf }
  | eof                            { raise (Lexical_error "unterminated comment") }
  | _                              { comment level lexbuf }

