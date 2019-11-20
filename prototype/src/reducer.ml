open Syntax
open Plate
open Bindings
open Library
open Eval

module SM = Util.StringMap

(* keep track of local context -- used in expr below *)
type local_ctx = {lvars:name list}

(** 
 * Reduces certain shorthands in a library 
 * Currently, the following shorthands are reduced:
 *     - TypeFrom (Theory Identifier)
 *     - TermFrom (Theory Identifier)
 *
 * Should also reduce Access
 *
 * @param lib : The library
 * @param r   : A base binding
 * @return    : New base binding where abovementioned shorthands are expanded
 *)
let reduce lib name r =
    let rec expand lc = 
       { bT = (fun x -> match x with
        | TProof fm -> TProof ((expand {lvars=[]}).cT fm)
        | TTypeFromTheory thyname -> reifyTheoryToType lc thyname 
        | TTheory i -> reflectTheory lc i
        | TInduct (i, l) -> TInduct (i,
            List.map (ETT.CS.mapChildren ETT.plate_field_sig (expand {lvars=[i]@lc.lvars})) l)
        | _ -> (mapChildrenT (lazy (expand lc))).bT x
        )
       ; cT = (fun x -> match x with
        | Binder (b, (VarSpec(l,t)),e) -> 
            Binder(b, (VarSpec(l, Util.map_option (expand lc).bT t)),
                      (expand {lvars=l@lc.lvars}).cT e)
        | Desc (b, n, t, e) -> 
            Desc (b, n, (expand lc).bT t, (expand {lvars=[n]@lc.lvars}).cT e)
        | Ident _      (* we might want to look this up? *)
        | _ -> (mapChildrenT (lazy (expand lc))).cT x
    )}

    (** 
     * Reifies a (biform) theory to a type expression 
     *
     * @param thyname : The name of the theory to be reified
     * @return        : The dependent DAG representing the type
     *)
    and reifyTheoryToType lc thyname = 
        let thy = SM.find thyname lib.theories in
        let type_fields1 = SM.fold (fun k v r -> (FieldSig (k, v.kind)) :: r ) (get_symb thy) [] in
        let type_fields2 = SM.fold (fun k (v,_) r -> (FieldSig (k, v.kind)) :: r ) (get_defns thy) [] in
        let type_fields = List.append type_fields1 type_fields2 in
        let axiom_fields = SM.fold (fun k v r -> if snd v then (FieldSig (k, TProof (fst v)) ) :: r else r ) (get_props thy) [] in 
        (expand lc).bT (TRecord (List.append type_fields axiom_fields))       
    (** 
     * Creates a term algebra for a biform theory 
     *
     * @param thyname : The name of the theory to be reified
     * @return        : The dependent DAG representing the type
     *)    
    and reflectTheory lc i =
        let bb = SM.find i lib.theories in
        let fv = "FreshVariable" in
        let mkctr n ty = if is_type_defn ty then [] else
            let signature = match ty with
               | TArrow (TProd l, _) | TPredicate (TProd l) -> TArrow (TProd (Util.replicate (List.length l) (TId fv)), TId fv)
               | TArrow _ | TPredicate _ -> (TArrow (TId fv, TId fv))
               | Type | TId _ | TApp _ | TProd _ | TLift _ | TTheory _
               | TTypeFromTheory _ | TProof _ | TBinder _
               | TPower _ | TRecord _ | TDepId _ | TInduct _ -> (TId fv) in
            [FieldSig ("~"^n^"#", signature)] in
        let add1 = fun k v r -> (mkctr k v.kind) :: r in
        let add2 = fun k (v,_) r -> (mkctr k v.kind) :: r in
        let lsymb = List.flatten (SM.fold add1 (get_symb bb) []) in
        let ldefn = List.flatten (SM.fold add2 (get_defns bb) []) in
        let thy = TInduct (fv, List.append lsymb ldefn) in
        (expand lc).bT thy in
    let refl_tydcl {kind = t; defn = d} = 
        { kind = (expand {lvars=[]}).bT t
        ; defn = apply_to_type (expand {lvars=[]}).bT d} in
    let func_defn (ty,(sa,e)) = 
        (* only reduce "constants", not under binders *)
        let red param exp = match param with
          | PConst _ -> eval r exp
          | _        -> exp in
        let exp_e = (expand {lvars=param_decl_params sa}).cT (red sa e) in
        let exp_ty = refl_tydcl ty in
        (exp_ty, (sa, exp_e)) in
    let expand_var t       = (expand {lvars=[]}).bT t in
    let expand_prop (b,c) = ((expand {lvars=[]}).cT b, c) in
    let expand_fields t       = (expand {lvars=[]}).bT t in
    Log.log ("Reducing base theory "^name^"\n");
    (* starts from r.types, which essentially makes a copy *)
    (* refl_tydcl will reflect theories into an inductive type *)
    let nsymbs = SM.map refl_tydcl r.symbols in
    let ndefns = SM.map func_defn r.defns in
    let nvars = SM.map expand_var r.vars in
    let nprops = SM.map expand_prop r.props in
    let nfields = SM.map expand_fields r.fields in
    {symbols = nsymbs; defns = ndefns; vars = nvars; props = nprops;
     fields = nfields}

let reducer lib = 
   {lib with (* should theories be reduced? *)
        theories = Util.StringMap.mapi (reduce lib) lib.theories }
