(* library.ml *)

(* Takes an AST and generates theory bindings
 *
 * This is done via tracking the definitions of each piece 
 *
 *)

open Syntax
open Bindings

module NS = Util.NS
module SM = Util.StringMap

type library = {
    lname : string;
    arrows : arrow SM.t;
    theories : bindings SM.t;
    subst : subst list SM.t;
}

(**
 * Creates an empty (theory) library
 * 
 * @param lname        : The name of the library 
 *)
let empty_lib nam = 
    {arrows = SM.empty; theories = SM.empty; subst = SM.empty; lname = nam}

(**
 * Copies a library
 * 
 * @param l    : The source library 
 * @param nam  : The name of the new library
 *)
let copy_lib l nam = { theories = l.theories; arrows = l.arrows; lname = nam; subst = l.subst }

(**
 * Finds an arrow in a library
 * 
 * @param lib  : The library to look in           
 * @param x    : The name of arrow to look for
 * 
 * @return     : 
 *)
let resolve lib x = SM.find x lib.arrows

exception LookingFor of string
exception LookingForProp of string

(**
 * Looks up whether name is a name of a theory in a library
 * 
 * @param lib  : The library to look in           
 * @param y    : The name of theory to look for
 * 
 * @return     : 
 *)
let rec lookup_arrow lib y = 
    let chain = [(resolve lib)] in
    try Util.chain_lookup chain y
    with Not_found -> raise (LookingFor y)

let map_add s k v m = 
    if SM.mem k m then
        raise (Exceptions.MultiplyDefined("Symbol", k, s))
    else 
        Log.log (Printf.sprintf "Theory %s defines symbol %s\n" s k);
        SM.add k v m

let add_arrow lib k v =
    if SM.mem k lib.arrows then
        raise (Exceptions.MultiplyDefined("Arrow", k, ""))
    else 
        Log.log (Printf.sprintf "%s defined\n" k);
        {lib with arrows = SM.add k v lib.arrows}

let add_subst lib k v =
    if SM.mem k lib.subst then
        raise (Exceptions.MultiplyDefined("Substitution", k, ""))
    else 
        Log.log (Printf.sprintf "%s defined\n" k);
        {lib with subst = SM.add k v lib.subst}

let report_loc file (b,e) =
  let l = b.Lexing.pos_lnum in
  let fc = b.Lexing.pos_cnum - b.Lexing.pos_bol + 1 in
  let lc = e.Lexing.pos_cnum - b.Lexing.pos_bol + 1 in
  Printf.sprintf "File \"%s\", line %d, characters %d-%d:\n" file l fc lc
    
let read file =
  if not (Sys.file_exists file) then (
    Printf.eprintf "Reading library %s: no such file." file; exit 2) 
  else
    begin
    (* get the channel *)
    let ic = open_in file in  
    let lb = Lexing.from_channel ic in
    
    try 
        Parser.main Lexer.token lb
    with
      | Lexer.Lexical_error s ->
        Printf.eprintf "%s\n" (report_loc file 
            (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb));
        Printf.eprintf "lexical error: %s\n" s;
        exit 1
      | Parsing.Parse_error ->
        Printf.eprintf "%s\n" (report_loc file 
            (Lexing.lexeme_start_p lb, Lexing.lexeme_end_p lb));
        Printf.eprintf "syntax error\n";
        exit 1
   end
