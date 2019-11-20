(* bindings.mli *)

(* Takes an AST and generates theory bindings *)

open Syntax

(* Represent the bindings of a theory. *)
(* In the bindings of a theory, we always named axioms/theorems *)
type axiom = expr * bool

(*  Tracks the bindings made in a theory *)
type pre_bindings = {
    types : typ_decl Util.StringMap.t;
    functions : funcdefn Util.StringMap.t;
    variables : type_comp Util.StringMap.t;
    axioms : axiom Util.StringMap.t;
}

type arrow_def = name * arrow
and combine = name list * name

(*  These are the actual bindings, sorted properly *)
and bindings = {
    symbols : typ_decl Util.StringMap.t;
    defns : (typ_decl * funcdefn) Util.StringMap.t;
    vars : type_comp Util.StringMap.t;
    props : axiom Util.StringMap.t;
    fields : type_comp Util.StringMap.t; (* for reverse-lookup *)
}

val emptyThyName : name

val empty_bindings : unit -> bindings
val empty_pre_bindings : unit -> pre_bindings
val copy_bindings : bindings -> bindings

(* convenient pre_bindings utilities *)
val get_types : pre_bindings -> typ_decl Util.StringMap.t
val get_axioms : pre_bindings -> axiom Util.StringMap.t
val get_variables : pre_bindings -> type_comp Util.StringMap.t
val get_funs : pre_bindings -> funcdefn Util.StringMap.t

(* convenient bindings utilities *)
val get_symb : bindings -> typ_decl Util.StringMap.t
val get_vars : bindings -> type_comp Util.StringMap.t
val get_defns : bindings -> (typ_decl * funcdefn) Util.StringMap.t
val get_props : bindings -> axiom Util.StringMap.t
val get_fields : bindings -> type_comp Util.StringMap.t

val get_depends : bindings -> Util.NS.t Util.StringMap.t

val map_add : string -> Util.StringMap.key -> 'a -> 'a Util.StringMap.t -> 
        'a Util.StringMap.t

val type_dps_on : type_comp -> Util.NS.t
val symb_dps_on : typ_decl -> Util.NS.t
val expr_dps_on : expr -> Util.NS.t
val thy_dps_on  : arrow -> Util.NS.t

val extract_bindings : pre_bindings -> bindings
val add_pre_into_bindings : pre_bindings -> bindings -> bindings
