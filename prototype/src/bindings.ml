(* bindings.ml *)

(* Takes an AST and generates theory bindings
 *
 * This is done via tracking the definitions of each piece 
 *)

open Syntax

module NS = Util.NS
module SM = Util.StringMap

(* Represent the bindings of a theory. *)
type axiom = expr * bool (* true means it is an axiom, false a theorem *)

type pre_bindings = {
    types : typ_decl SM.t;
    functions : funcdefn SM.t;
    variables : type_comp SM.t;
    axioms : axiom SM.t
}

type arrow_def = name * arrow
and combine = name list * name

(*  These are the actual bindings, sorted properly *)
and bindings = {
    symbols : typ_decl Util.StringMap.t;
    defns : (typ_decl * funcdefn) Util.StringMap.t;
    vars : type_comp Util.StringMap.t;
    props : axiom Util.StringMap.t;
    fields : type_comp Util.StringMap.t;
}

(* special case *)
let emptyThyName = "Empty"

let empty_pre_bindings () =
    {axioms=SM.empty; types=SM.empty; variables=SM.empty; functions=SM.empty}

let empty_bindings () =
    {props=SM.empty; symbols=SM.empty; vars=SM.empty; defns=SM.empty;
     fields=SM.empty}

(**
 * Copies a binding
 * @param b  : The binding we are copying from
 *
 * @return   : A new copy of the binding 
 *)
let copy_bindings b =
    { props=b.props; vars=b.vars; defns=b.defns; symbols=b.symbols;
      fields=b.fields }

(* convenient pre_bindings utilities *)
let get_types b = b.types
let get_axioms b = b.axioms
let get_variables b = b.variables
let get_funs b = b.functions

(* convenient bindings utilities *)
let get_symb b = b.symbols
let get_vars b = b.vars
let get_defns b = b.defns
let get_props b = b.props
let get_fields b = b.fields

(**
 * Adds a (name, value) pair to a map
 * 
 * @param s : The name of the theory (solely for logging) 
 * @param k : The name 
 * @param v : The value
 * @m       : The map 
 * @return  : The string map extended with the newly added pair 
 *)     
let map_add s k v m = 
    if SM.mem k m then
        raise (Exceptions.MultiplyDefined("Symbol", k, s))
    else 
        Log.log (Printf.sprintf "Theory %s defines symbol %s\n" s k);
        SM.add k v m

(* Do a pass on everything and 'remember' what is seen.
 * This means tracking the definitions as well as all occurences of
 * symbols.  This gives a "depends on" relation, which is useful for
 * topological sorts of dependencies *)

(* compute the "depends on" relation for symbols *)
let rec symb_dps_on {kind = t; defn = d} =
    let td = type_dps_on t in
    match d with
    | Manifest dd | SubType dd -> NS.union (td) (type_dps_on dd)
    | NoDefn    -> td

and type_dps_on = 
    let parts (FieldSig(_,tc)) = type_dps_on tc in
    function
    | Type -> NS.empty
    | TId x -> NS.singleton x (* no need to chase through graph here! *)
    | TDepId (i,t) -> NS.union (NS.singleton i) (type_dps_on t)
    | TApp (t,t1) -> NS.union (type_dps_on t) (type_dps_on t1)
    | TProd tl -> NS.setlist_union (List.map type_dps_on tl)
    | TArrow (t1,t2) -> NS.union (type_dps_on t1) (type_dps_on t2)
    | TInduct (n,cl) -> 
        NS.diff (NS.setlist_union (List.map parts cl)) (NS.singleton n)
    | TTheory i -> NS.singleton i
    | TTypeFromTheory i -> NS.singleton i
    | TProof x -> expr_dps_on x
    | TPower t -> type_dps_on t
    | TPredicate t -> type_dps_on t
    | TRecord tl -> 
        NS.setlist_union (List.map parts tl)
    | TLift x -> expr_dps_on x
    | TBinder (VarSpec(nl,tc), tp) ->
        let ns = NS.list_to_set nl in
        let diff = NS.diff (type_dps_on tp) ns in
        (match tc with
        | Some tt -> NS.union (type_dps_on tt) diff
        | None    -> diff)

(* track the "depends on" relation for expressions *)
and expr_dps_on = function
  | Ident i -> NS.singleton i
  | BTrue | BFalse -> NS.empty
  | In (e, t) -> NS.union (expr_dps_on e) (type_dps_on t)
  | EqOp (e1,e2) -> NS.union (expr_dps_on e1) (expr_dps_on e2)
  | And (e1,e2) -> NS.union (expr_dps_on e1) (expr_dps_on e2)
  | Or (e1,e2) -> NS.union (expr_dps_on e1) (expr_dps_on e2)
  | Not e -> expr_dps_on e
  | Iff (e1,e2) -> NS.union (expr_dps_on e1) (expr_dps_on e2)
  | If (b, e1, e2) -> NS.union (expr_dps_on b)
      (NS.union (expr_dps_on e1) (expr_dps_on e2))
  | Implies (e1,e2) -> NS.union (expr_dps_on e1) (expr_dps_on e2)
  | Appl(_,e1,e2) -> NS.union (expr_dps_on e1) (expr_dps_on e2)
  | Binder (_,VarSpec(nl,tc),e) ->
      let ns = NS.list_to_set nl in
      let diff = NS.diff (expr_dps_on e) ns in
      (match tc with
      | Some tp -> NS.union (type_dps_on tp) diff
      | None    -> diff)
  | Let(i, e1, e2) ->
      let e1d = expr_dps_on e1 in
      NS.union e1d (NS.remove i (expr_dps_on e2))
  | Desc (_, n,tc,e) ->
      NS.remove n (NS.union (type_dps_on tc) (expr_dps_on e))
  | Tuple tl -> NS.setlist_union (List.map expr_dps_on tl)
  | Record rl -> NS.setlist_union (List.map (fun (FieldMem (_,t,x)) -> 
                 NS.union (Util.maybe type_dps_on NS.empty t) (expr_dps_on x)) rl)
  | Selector (e,_) -> expr_dps_on e
  | Case (e, l) -> NS.union (expr_dps_on e) 
                       (NS.setlist_union (List.map branch_dps_on l))
  | ProofObject _ -> failwith "What does a proof object depend on?"
  | Escape _ -> failwith "What does an escape depend on?"
  | Quote _ -> failwith "What does a quote depend on?"
  | Eval _ -> failwith "What does an eval depend on?"

and branch_dps_on (Branch(pat, e)) = 
    NS.diff (expr_dps_on e) (pat_binds pat)

and pat_binds = function
    | PatNone -> NS.empty
    | PatConst _ -> NS.empty
    | PatIdent i -> NS.singleton i
    | PatTuple t -> NS.setlist_union (List.map pat_binds t)
    | PatRecord l -> 
        NS.setlist_union (List.map (fun (_,rhs) -> pat_binds rhs) l)
    | PatApp(p1,p2) -> NS.union (pat_binds p1) (pat_binds p2)

(* compute "depends on" for arrows *)
let rec thy_dps_on = function
    | AThy _ -> NS.empty (* base theories do not even depend on Empty! *)
    | ACombine (nl,_) -> NS.list_to_set nl
      (* above: the base is a transitive dependency, don't add it *)
    | AExtend (n,_,_) -> NS.singleton n
    | AInstance (_,n,_) -> NS.singleton n
    | ArrowName n -> NS.singleton n
    | AParComp (p1,p2) -> NS.list_to_set [p1;p2]
    | ASeqComp (x,y,l) -> NS.setlist_union [NS.singleton x; NS.singleton y; NS.list_to_set l]
    | ARename (n, _) -> NS.singleton n
    | ArrowId -> NS.empty
    | AMixin ( (n1,_), (n2,_) ) -> NS.setlist_union [NS.singleton n1; NS.singleton n2]

let func_dps_on (t,(a,e)) =
    let g_deps = Util.NS.list_to_set (param_decl_params a) in
    let s1 = Util.NS.diff (expr_dps_on e) g_deps in
    let s2 = symb_dps_on t in
    Util.NS.union s1 s2

let props_dps_on (a,_) = expr_dps_on a

let get_depends b =
    let mk f x i = SM.fold (fun k v sm -> SM.add_with k (function None -> f v | Some s -> NS.union (f v) s) sm) x i in
    let fdps = mk func_dps_on b.defns SM.empty in
    let adps = mk props_dps_on b.props fdps in
    let tdps = mk symb_dps_on b.symbols adps in
    let vdps = mk type_dps_on b.vars tdps in
    vdps

let extract_defn k a b = match (a,b) with
  | (Some x, Some y) -> Some (x,y)
  | (None  , Some _) -> failwith (k^" has a definition but no type")
  | (_     , _     ) -> None

let extract_symb k a b = match (a,b) with
  | (Some _, Some _) -> None
  | (None  , Some _) -> failwith (k^" has a definition but no type")
  | (z     , None  ) -> z

let extract_fields k td m =
  match (td.kind, td.defn) with
  | (Type, Manifest(TInduct(n,flds))) -> 
    let tt = TInduct(n, flds) in
    List.fold_left (fun mm (FieldSig (nm, tp)) -> SM.add nm tt mm) m flds
  | _ -> m

let extract_bindings pre = 
    let module SM = Util.StringMap in
    { symbols = SM.merge extract_symb pre.types pre.functions;
      defns = SM.merge extract_defn pre.types pre.functions;
      vars = SM.copy pre.variables;
      props = SM.copy pre.axioms;
      fields = SM.fold extract_fields pre.types SM.empty } (* TODO *)

let add_pre_into_bindings pre b =
    let module SM = Util.StringMap in
    let symbs = SM.merge extract_symb pre.types pre.functions in
    let defs = SM.merge extract_defn pre.types pre.functions in
    { symbols = SM.fold SM.add symbs b.symbols;
      defns = SM.fold SM.add defs b.defns;
      vars = SM.fold SM.add pre.variables b.vars;
      props = SM.fold SM.add pre.axioms b.props;
      fields = SM.fold extract_fields pre.types b.fields } (* TODO *)
