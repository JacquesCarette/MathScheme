(* subst.ml *)

(* Deals with substitutions and low-level renaming *)

open Syntax
open Bindings
open Plate
open List

type substitution = {
    type_subs : (ident * type_comp) list;
    expr_subs : subst list;
    var_subs : (name * name) list;
}

let empty_subs = 
    {type_subs = []; expr_subs = []; var_subs = []}

let mkTId n = TId n

let mkId n = Ident n

let rec is_ident = function
  | Ident n -> Some n
  | BTrue | BFalse
  | EqOp _ | And _ | Or _ | Not _ | Iff _ | Implies _ 
  | Selector _ | In _ | Case _ | If _
  | Appl _ | Binder _ | Desc _ | Tuple _ | Record _ | Let _
  | Escape _ | Quote _ | Eval _ | ProofObject _ -> None

(* this should probably do some filtering ! *)
let rec is_name = function
  | Ident x -> Some x
  | BTrue | BFalse
  | EqOp _ | And _ | Or _ | Not _ | Iff _ | Implies _ 
  | Selector _ | In _ | Case _ | If _
  | Appl _ | Binder _ | Desc _ | Tuple _ | Record _ | Let _
  | Escape _ | Quote _ | Eval _ | ProofObject _ -> None

let rec convert p g c = function
  | []          -> []
  | (i,x) :: xs -> (match p x with 
                   | Some n -> (c i, g n) :: convert p g c xs
                   | None   ->               convert p g c xs)

(**
 * Expands a binding
 * 
 * @param lib :  A library
 * @param bb  :  A theory binding              
 *
 * @return    : 
 *) 
(* SimpApp-based substitution generalization *)
let from_substlist (s:ren list) :substitution =
    let expr_from_subst (i,n) = Subst(i, mkId n) in
    let typ_from_subst (i,n) = (i, mkTId n) in
    { type_subs = List.map typ_from_subst s;
      expr_subs = List.map expr_from_subst s;
      var_subs = s
    }

let from_exprlist (l : (name*expr) list) : substitution =
    { type_subs = convert is_ident mkTId Util.identity l;
      expr_subs = List.map (fun (e1,e2) -> Subst(e1,e2)) l;
      var_subs = convert is_name Util.identity Util.identity l
    }

(* lift 'up' a name-based substitution *)
let from_namelist (l : (name*name) list) : substitution =
    { type_subs = List.map (fun (x,y) -> (x,mkTId y)) l;
      expr_subs = List.map (fun (x,y) -> Subst(x,mkId y)) l;
      var_subs = l
    }

let simpleTypeSub (n:name) (t:type_comp) : substitution =
    { type_subs = [(n,t)];
      expr_subs = [];
      var_subs = []
    }

let simpleExprSub (n:name) (e:expr) : substitution =
    { type_subs = [];
      expr_subs = [Subst(n,e)];
      var_subs = []
    }

(* useful short-hand -- don't export *)
let subst t a b = Util.total_rename (List.map (fun (Subst(x,y)) -> (x,y)) t) a b
let rename = Util.total_rename

(* useful for renaming just names *)
let rename_name sub x =
    let y = rename sub.var_subs x x in
    if y <> x then Log.log ("Renamed "^x^" to "^y^"\n");
    y

(* For 'parametrized' names, i.e. names with _ in them *)
let rename_param_name sub x =
    let expl = Util.explode '_' x in
    let parts = List.map (rename_name sub) expl in
    String.concat "_" parts

let rec used_variable_pattern n = function
    | PatNone -> false
    | PatIdent i -> n = i
    | PatConst _ -> false
    | PatTuple pl -> exists (used_variable_pattern n) pl
    | PatRecord ipl -> exists (fun (i,p) -> n = i || used_variable_pattern n p) ipl
    | PatApp (p1, p2) -> used_variable_pattern n p1 || used_variable_pattern n p2

let used_variable_plate n sy b = match sy with
    | ETT.SyntaxB (TId i)         
    | ETT.SyntaxB (TDepId (i, _))
    | ETT.SyntaxB (TInduct (i, _))
    | ETT.SyntaxB (TTheory i)      
    | ETT.SyntaxB (TTypeFromTheory i)
    | ETT.SyntaxC (Ident i)
    | ETT.SyntaxC (Desc (_, i, _, _)) -> (n = i) || b
    | ETT.SyntaxB (TRecord fsl) -> (exists (fun (FieldSig (i,_)) -> n = i) fsl) || b
    | ETT.SyntaxC (Record fml) -> (exists (fun (FieldMem (i,_,_)) -> n = i) fml) || b
    | ETT.SyntaxC (Binder (_, (VarSpec (il,_)), _)) -> (exists (fun i -> n = i) il) || b
    | ETT.SyntaxC (Case (_, cl)) -> (exists (fun (Branch (p,_)) -> used_variable_pattern n p) cl) || b
    | _ -> b
    
let used_variable n sy = ETT.foldFamily (used_variable_plate n) sy false

let used_variable_subs n subs = 
  fold_left (fun b (_,ty) -> ETT.foldFamily (used_variable_plate n) (ETT.SyntaxB ty) b)
   (fold_left (fun b (Subst(_,ex)) -> ETT.foldFamily (used_variable_plate n) (ETT.SyntaxC ex) b)
    (fold_left (fun _ (_,i) -> n = i) false subs.var_subs)
   subs.expr_subs)
  subs.type_subs

let rec fresh_name n sy = if used_variable n sy then fresh_name (n^"'") sy else n

let rec fresh_name_subs n subs = if used_variable_subs n subs then fresh_name_subs (n^"'") subs else n
  
let slide_sub_under_binders subs il = fold_left 
    (fun subs0 i -> if used_variable_subs i subs0 
                    then let fn = fresh_name_subs i subs0 in
                         { type_subs = (i, TId fn)::(subs0.type_subs)
                         ; expr_subs = Subst(i, Ident fn)::(subs0.expr_subs)
                         ; var_subs  = (i, fn)::(subs0.var_subs)
                         }
                    else subs0)
    subs il

(* Renaming routines are just a map on the name part of the syntax *)
let ren_typrecord sub t = Fold.Name.map_typrecord (rename_name sub) t
let ren_funcdefn sub t = Fold.Name.map_funcdefn (rename_name sub) t
let ren_type sub t = Fold.Name.map_type (rename_name sub) t
let ren_axiom sub t = Fold.Name.map_axiom (rename_name sub) t
let ren_fields sub t = Fold.Name.map_fields (rename_name sub) t

let ren_defn sub t = Fold.Name.map_defn (rename_name sub) t

(* Rename everything in a theory *)
let thy_rename sub b =
    let module SM = Util.StringMap in
    let ren_name a = rename_name sub a in
    let map2 f g m = SM.fold (fun k v -> SM.add (f k) (g v)) m SM.empty in
    let ns = map2 ren_name (ren_typrecord sub) b.symbols in
    let ndefns = map2 ren_name (ren_defn sub) b.defns in
    let nvars = map2 Util.identity (ren_type sub) b.vars in
    let naxioms = map2 (rename_param_name sub) 
                       (ren_axiom sub) b.props in
    let nfields = map2 ren_name (ren_type sub) b.fields in
    { symbols = ns; defns = ndefns; vars = nvars; props = naxioms;
      fields = nfields }

let rec type_sub (sub:substitution) (t:type_comp) : type_comp = match t with
    | Type -> Type
    | TId x -> rename sub.type_subs x t
    | TDepId (i,t) -> TDepId (rename_name sub i, type_sub sub t)
    | TProd p -> TProd (List.map (type_sub sub) p)
    | TArrow (TDepId (i, l), r) -> let sub' = slide_sub_under_binders sub [i] in
                                   TArrow (TDepId (rename_name sub' i, type_sub sub l), type_sub sub' r)
    | TArrow (l,r) -> TArrow (type_sub sub l, type_sub sub r)
    | TInduct (i,l) ->
        let sub' = slide_sub_under_binders sub [i] in
        TInduct (rename_name sub' i,
        (List.map (fun (FieldSig(a,b)) -> FieldSig(a, type_sub sub' b)) l))
    | TTheory _ -> t
    | TTypeFromTheory _ -> t
    | TProof _ -> t
    | TPredicate p -> TPredicate (type_sub sub p)
    | TPower t -> TPower (type_sub sub t)
    | TRecord _ -> failwith "don't know how to rename records (yet)"
    | TApp (t,tc) -> TApp( type_sub sub t, type_sub sub tc)
    | TLift x -> TLift (expr_sub sub x)
    | TBinder (VarSpec(l,t),tp) ->
        let sub' = slide_sub_under_binders sub l in
        TBinder(VarSpec(map (rename_name sub') l, Util.map_option (type_sub sub) t), type_sub sub' tp)

(* should take care of alpha-renaming in Forall/Exists *)
(* should renaming happen for functions names & operators names?
 * we don't support higher-order _expressions_ right now *)
and expr_sub (sub:substitution) (e:expr) : expr =
    (* need to know if renaming produces an operator *)
    let rec expr x = match x with
        | Ident y -> subst sub.expr_subs y x
        | BTrue | BFalse -> x
        | In (y, t) -> In( expr y, type_sub sub t)
        | EqOp (e1, e2) -> EqOp( expr e1, expr e2)
        | And (e1,e2) -> And( expr e1, expr e2)
        | Or (e1,e2) -> Or( expr e1, expr e2)
        | Not e -> Not (expr e)
        | Implies (e1,e2) -> Implies( expr e1, expr e2)
        | Iff (e1,e2) -> Iff( expr e1, expr e2)
        | If (b, e1, e2) -> If( expr b, expr e1, expr e2)
        | Appl (b,f,args) -> Appl(b, expr f, expr args)
        | Binder (b, VarSpec(l,t),e) -> 
            let sub' = slide_sub_under_binders sub l in
            Binder(b, VarSpec(map (rename_name sub') l, Util.map_option (type_sub sub) t), expr_sub sub' e)
        | Let (i,e1,e2) ->
            let sub' = slide_sub_under_binders sub [i] in
            Let(rename_name sub' i, expr e1, expr_sub sub' e2)
        | Desc (b, n, t,e) -> 
            let sub' = slide_sub_under_binders sub [n] in
            Desc (b, rename_name sub' n, type_sub sub t, expr_sub sub' e)
        | Record l -> Record( List.map (fun (FieldMem (i,t,e)) -> 
                                            (FieldMem (i, Util.map_option (type_sub sub) t, expr e))) l)
        | Tuple l -> Tuple( List.map expr l)
        | Selector (e, n) -> Selector( expr e, n )
        | Case (e, l) -> Case( expr e, List.map case_sub l)
        | Escape e -> Escape e
        | Quote e -> Quote e
        | Eval (e,t) -> Eval ( expr e, type_sub sub t)
        | ProofObject t -> ProofObject t
    and case_sub (Branch(pat, e)) = Branch(pat_sub pat, expr e)
    and pat_sub pat = pat (* do not substitute in patterns ! *)
    in expr e
