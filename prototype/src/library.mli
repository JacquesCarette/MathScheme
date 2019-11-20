(* library.mli *)

open Syntax
open Bindings

(* a record of theories and arrows *)
type library = {
    lname : string;
    arrows : arrow Util.StringMap.t;
    theories : bindings Util.StringMap.t;
    subst : subst list Util.StringMap.t;
}

val empty_lib : string -> library
val copy_lib : library -> string -> library

val add_arrow : library -> Util.StringMap.key -> arrow -> library
val add_subst : library -> Util.StringMap.key -> subst list -> library

exception LookingFor of string
exception LookingForProp of string

val lookup_arrow : library -> string -> arrow

val read : string -> toplevel_expr
