(* 
 * This module contains functions that tracks various definitions of
 * parser-oriented data structures (in syntax.ml) and translate them
 * into corresponding more theory-oriented data structures defined in 
 * bindings.ml
 *)

open Syntax
open Bindings

(**
 * Tracks declarations 
 *
 * @param name : Name of theory being dealt with
 * @param b    : Binding of type pre_bindings declared in bindings.ml
 * @param dl   : List of declarations
 * @return     : pre_bindings structure
 *)
let rec tr_decl name b dl = 
     (**
    * This function 'f' takes a binding, a declaration and enhances the binding
    * with the info tracked in the declaration
    * @param env  : the current binding     
    * @return     : The binding 'env' enhanced with tracked infos
    *)
    let rec f env = function
    | TypDecl t -> tr_typedecl env t
    | Axiom a -> tr_axiom env a
    | VarDecl l -> List.fold_left tr_vardecl env l
    | FuncDecl x -> tr_funcdecl env x
    | Induct (n,l) -> (* this de facto expands the declarations *)
        (* Add the type declaration of the inductive data type to the binding 'env' *)
        tr_typedecl env (TBase(n, {kind = Type; defn = Manifest(TInduct(n,l))}))
    and tr_typedecl env = function
    | TBase (s, t) -> {env with types = map_add name s t env.types }
    | TExtension (sl, t) -> 
        let tt = mkType t in
        let nt = List.fold_left (fun k e -> map_add name e tt k) env.types sl in
        {env with types = nt }
    and tr_vardecl env v = 
        let addvar = function
        (* the typechecker should make sure it's not Manifest *)
        | TBase (s, t) -> map_add name s t.kind env.variables
        | TExtension (sl, t) -> 
            List.fold_left 
                (fun tbl x -> map_add name x t tbl) env.variables sl
        in
        {env with variables = addvar v}
    and tr_axiom env = function
    | (Some n, e, bb) -> 
        {env with axioms = map_add name n (e,bb) env.axioms}
    | (None, e, bb) -> let n = Util.gen_axiom_name () in
        {env with axioms = map_add name n (e,bb) env.axioms}
    and tr_funcdecl env (sa,e) = 
        {env with functions = 
            map_add name (param_decl_name sa) (sa,e) env.functions}
    in List.fold_left f b dl

(**
 * Tracks each assignment in the top-level expression
 *
 * @param lib      : The current library
 * @return         : tr_lib is a function that takes as input a library
 *                   and an assignment and returns a new library enhanced with newly tracked info.
 *)
let rec tr_lib lib = function
  | NamedArrow (s, arr_spec) -> Library.add_arrow lib s arr_spec
  | NamedSubst (s, subst) -> Library.add_subst lib s subst

(**
 * Creates a (theory) library from a top-level expression
 * 
 * @param nam      : The name of the library
 * @param t        : Top-level expression = assign list. (of type 'toplevel_expr' defined in syntax.ml).
 * @return         : A library populated with info from the top-level expression.
 *                   The type 'library' is declared in library.ml   
 *)
let create_lib nam t = List.fold_left tr_lib (Library.empty_lib nam) t
