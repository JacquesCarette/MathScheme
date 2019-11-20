(* typeChecker.ml *)

(** This module provides functions for typechecking types, terms and declarations.
    Generally type sythensis is done on types and terms and declaration checking
    returns extended contexts *)

open Syntax
open List

module NS = Util.NS

module FieldMap = Util.MakeBetterMap(String)
module P = Printers.String.M
let p = P.p
let showType = P.showType
let showPattern = P.p_pat
let expr = P.expr
let decl = P.decl

(* type check a type *)

type type_expr = TypeComp of type_comp | Prop (* boolean *)

let showTypeExpr = function
 | TypeComp tc -> showType tc
 | Prop -> p "Proposition "

(* sort_type is a combination of 2 levels, for classifying types (kinds)
 * and type-definitions (aka kinds classifiers, sorts) *)
type kinds = KStar | KArrow of kinds * kinds
type sort_type = Kind of kinds | Sort

let rec showKinds = function
 | KStar -> p "*"
 | KArrow (KStar,k2) -> p "* -> "; showKinds k2
 | KArrow (k1,KStar) -> showKinds k1; p " -> *"
 | KArrow (k1,k2) -> p "("; showKinds k1; p ") -> ("; showKinds k2; p ")"

let showSortType = function
 | Kind k -> showKinds k
 | Sort -> p "Kind "

type typeExceptionData =
 | NameNotFound of name
 | TypeNotType
 | Unexpected of type_comp
 | UnsupportedTerm of expr
 | TypeTypeError of sort_type (* infered (expected Type) *)
                   *type_comp (* in type *)
 | DuplicateFieldNamesType of type_comp
 | TypeError of type_expr (* expected *)
               *type_expr (* infered *)
               *expr      (* in expression *)
 | TypeKindError of type_expr (* expected *)
                   *type_expr (* infered *)
                   *type_comp (* in type *)
 | AppError of type_expr (* infered while function type expected*)
              *expr      (* in expression *)
 | TAppError of type_comp (* infered while function type expected*)
               *type_comp (* in type *)
 | PredicateError of expr (* in expression *)
 | PropError of expr (* got a Prop when a regular type was expected in expression *)
 | BadDescriptionList of expr (* description quantifiers must bind one variable *)
 | DuplicateFieldNames of expr
 | TypeAnnotationRequired of expr
 | DuplicateBinderNames of expr
 | DuplicateTBinderNames of type_comp
 | TypDeclError of typedecl
 | AxiomError of axdecl
 | FunctionArrowExpected of expr * type_expr
 | ArrowExpected of pattern * type_comp
 | ProdExpected of pattern * type_comp
 | TProdExpected of expr * type_expr
 | TProdWrongLength of expr * type_expr
 | TProdDifferentTypes of type_comp * sort_type * sort_type 
 | ParameterNumberMismatch of pattern * type_comp
 | DuplicateBindings of name
 | FuncDeclBodyError of name * type_expr * type_expr
 | ConstructorTypeError of name * name * sort_type
 | ConstructorCodomainError of name * name * type_comp
 | SelectorNeedsRecord of expr
 | FieldNameNotFound of expr
 | CaseNeedsInductive of expr
 | BranchesHaveDifferentTypes of expr * type_expr list
 | CannotSynthesizeCaseType of expr
 | PatternNumberMismatch of (name * expr)
 | BadInductiveType of (name * expr)
 | TupleExpected of expr
 | PatTupleNumberMismatch of expr
 | FieldTypeAnnotationMismatch of (type_comp * type_comp * expr)
 | FormulaExpected of expr 
 | TODO of string

let printTypeExceptionData e = 
 let lprint = function 
 | NameNotFound n -> p ("NameNotFound: " ^ n)
 | TypeNotType -> p "TypeNotType "
 | Unexpected tc -> p "Unexpected: "; showType tc
 | UnsupportedTerm t -> p "Unsupported term: "; expr t
 | TypeTypeError (tc1,tc2) -> p "Infered kind "; showSortType tc1;
                             p "\nin type "; showType tc2
 | DuplicateFieldNamesType tc -> p "DuplicateFieldNameType: "; showType tc
 | TypeKindError (te1,te2,te) -> p "Infered type "; showTypeExpr te1;
                                 p "\nexpected type "; showTypeExpr te2;
                                 p "\nin type: "; showType te
 | TypeError (te1,te2,e) -> p "Infered type "; showTypeExpr te1;
                           p "\nexpected type "; showTypeExpr te2;
                           p "\nin expression: "; expr e
 | AppError (te,e) -> p "Infered type "; showTypeExpr te;
                     p "expected function type in "; expr e
 | TAppError (te,te0) -> p "Infered type "; showType te;
                         p " expected type-function in "; showType te0
 | PredicateError e -> p "PredicateError: "; expr e
 | PropError e -> p "PropError: "; expr e
 | BadDescriptionList e -> p "BadDescriptionList: "; expr e
 | DuplicateFieldNames e -> p "DuplicateFieldNames: "; expr e
 | TypeAnnotationRequired e -> p "Type annotation required in "; expr e
 | DuplicateBinderNames e -> p "DuplicateBinderNames: "; expr e
 | DuplicateTBinderNames e -> p "DuplicateTBinderNames: "; showType e
 | TypDeclError td -> p "TypDeclError: "; decl (TypDecl td)
 | AxiomError ae -> p "AxiomError: "; decl (Axiom ae)
 | FunctionArrowExpected (te, ty) -> p "FunctionArrowExpected: "; expr te; p "; "; showTypeExpr ty
 | ArrowExpected (n,tc) -> 
     p "ArrowExpected: "; showPattern n; p "; "; showType tc
 | ParameterNumberMismatch (n,tc) -> 
     p "ParameterNumberMismatch: "; showPattern n; p "; "; showType tc
 | ProdExpected (n,tc) -> p "ProdExpected: "; showPattern n;p "; "; showType tc
 | TProdExpected (te, ty) -> p "TProdExpected: "; expr te; p "; "; showTypeExpr ty
 | TProdWrongLength (te, ty) -> p "TProdWrongLength: "; expr te; p "; "; showTypeExpr ty
 | TProdDifferentTypes(tc, k, k') -> 
   p "Member of TypeProduct "; showType tc; p " has kind ";
   showSortType k; p " but was expected to be "; showSortType k'
 | DuplicateBindings n -> p ("DuplicateBindings : "^n)
 | FuncDeclBodyError (n,t1,t2) -> 
     p ("FuncDeclBodyError: "^n^" expected "); showTypeExpr t1; p " got ";
     showTypeExpr t2
 | ConstructorTypeError (n1,n2,tc) -> p ("ConstructorTypeError: "^n1^"; "^n2^"; "); showSortType tc
 | ConstructorCodomainError (n1,n2,tc) -> p ("ConstructorCodomainError: "^n1^"; "^n2^"; "); showType tc
 | SelectorNeedsRecord e -> p ("SelectorNeedsRecord: "); expr e
 | FieldNameNotFound e -> p ("FieldNameNotFound: "); expr e
 | CaseNeedsInductive e -> p ("CaseNeedsInductive: Expected Inductive type but got"); expr e
 | BranchesHaveDifferentTypes (e,tys) -> p ("BranchesHaveDifferentTypes: "); expr e; p("; "); iter showTypeExpr tys
 | CannotSynthesizeCaseType e -> p ("CannotSynthesizeCaseType on "); expr e
 | PatternNumberMismatch (n,e) -> p ("PatternNumberMismatch for branch "^n^"; "); expr e
 | BadInductiveType (n,e) -> p ("BadInductiveType for branch "^n^"; "); expr e
 | TupleExpected e -> p ("TupleExpected on "); expr e
 | PatTupleNumberMismatch e -> p ("PatTupleNumberMismatch on "); expr e
 | FieldTypeAnnotationMismatch (t1,t2,e) -> p "FieldTypeAnnotationMismatch: expected "; showType t1; 
                                            p " but recieved "; showType t2;
                                            p " in "; expr e
 | FormulaExpected e -> p ("Formula expected, but here : "); expr e 
 | TODO msg -> p ("TODO: "^msg)
 
 in lprint e; Format.flush_str_formatter ()

exception TypeException of typeExceptionData

let raiseTypeException t = raise (TypeException t)

type context = {tydecl : name -> type_comp
               ;tydefn : name -> type_comp}

let lookupType ctx x = ctx.tydecl x
let lookupDef ctx x = ctx.tydefn x

(** empty_ctx: context
    The empty context *)
let empty_ctx : context =
 {tydecl = (fun x -> raiseTypeException (NameNotFound x))
 ;tydefn = (fun x -> raiseTypeException (NameNotFound x))}

(** extend_ctx: context -> name list -> type_comp -> conxtext
    Takes a given context and extends it by adding names all with the same given type
    the new context is returned. *)
let extend_ctx (ctx:context) names ty : context =
 {tydecl = (fun x -> if (mem x names) then ty else (ctx.tydecl x))
 ;tydefn = ctx.tydefn}

let extend_ctx1 (ctx:context) name ty = extend_ctx ctx [name] ty

let extend_ctx_def (ctx:context) name ty : context =
 {tydecl = ctx.tydecl
 ;tydefn = (fun x -> if x=name then ty else (ctx.tydefn x))}

(* Do definition expansions until the type is in head normal form. *)
let rec headNormalForm (ctx:context) (t:type_comp) = match t with 
  | TId n -> begin try
              headNormalForm ctx (lookupDef ctx n)
             with TypeException (NameNotFound _) -> TId n
             end
  | Type | TApp _ | TProd _ | TArrow _ | TInduct _ | TTheory _
  | TTypeFromTheory _ | TBinder _
  | TPower _ | TPredicate _ | TRecord _ | TDepId _ | TLift _ | TProof _ -> t
  
let headNormalFormExpr ctx (t:type_expr) = match t with
  | TypeComp ty -> TypeComp (headNormalForm ctx ty)
  | Prop -> Prop

(**
 * Checks whether two sort types are identical
 * @param (ctx : context)   : Typing context
 * @param (t1  : type_comp) : The first type
 * @param (t2  : type_comp) : The second type
 * @return(bool)            : True if they are identical, false otherwise
 *)
let equivTypes (ctx:context) (t1:type_comp) (t2:type_comp) =
     let compareVariables n bv1 m bv2 =
         match bv1 n, bv2 m with
         | Some i, Some j -> i = j
         | None  , None   -> n = m
         | _     , _      -> false
     in
     let rec equivTypes_rec (counter : int) 
                           (t1:type_comp) (bv1 : name -> int option)
                           (t2:type_comp) (bv2 : name -> int option) =
     let recurse t1' t2' = equivTypes_rec counter t1' bv1 t2' bv2 in
     match t1, t2 with
     | TId n, TId m when compareVariables n bv1 m bv2 -> true
     | _ -> let t1' = headNormalForm ctx t1 in
            let t2' = headNormalForm ctx t2 in
            (* This match is fundamentally fragile *)
            match t1', t2' with
            | TId n, TId m -> compareVariables n bv1 m bv2
            | TDepId (n,nt), TDepId (m,mt) -> n = m && recurse nt mt
            | Type, Type -> true
            | TApp (x1,y1), TApp (x2,y2) -> recurse x1 x2 && recurse y1 y2 
            | TProd x1, TProd x2 -> begin try for_all2 recurse x1 x2
                                    with Invalid_argument _ -> false
                                    end
            | TArrow (x1,y1), TArrow (x2,y2) -> 
              let (n1, t1) = getDepId x1 in
              let (n2, t2) = getDepId x2 in
              let bv1' i = if Some i = n1 then Some counter else bv1 i in
              let bv2' i = if Some i = n2 then Some counter else bv2 i in
              recurse t1 t2 && equivTypes_rec (counter+1) y1 bv1' y2 bv2' 
            | TPower x1, TPower x2 -> recurse x1 x2
            | TPredicate x1, TPredicate x2 -> recurse x1 x2
            | TRecord x1, TRecord x2 -> 
               FieldMap.equal recurse
                (FieldMap.assoc_list_to_map (List.map (function (FieldSig (x,y)) -> (x,y)) x1))
                (FieldMap.assoc_list_to_map (List.map (function (FieldSig (x,y)) -> (x,y)) x2))
            (* This line below is a hack to test alpha equivalent comparision *)
            | TLift x1, TLift x2 -> equivTerms_rec counter x1 bv1 x2 bv2
            (* TODO: is missing a bunch of cases *)
            | _ -> false
     and equivTerms_rec (counter : int)
                        (e1:expr) (bv1 : name -> int option)
                        (e2:expr) (bv2 : name -> int option) =
         match e1, e2 with
         | Ident n , Ident m -> compareVariables n bv1 m bv2
         | Tuple t1, Tuple t2 ->
           if (length t1 = length t2)
           then 
             let f x1 x2 b = equivTerms_rec counter x1 bv1 x2 bv2 && b
             in fold_right2 f t1 t2 true
           else false
         (* Incomplete definition of Appl *)
         | Appl (_,Ident f,t1), Appl (_,Ident g,t2) -> compareVariables f bv1 g bv2
                                                    && equivTerms_rec counter t1 bv1 t2 bv2
         | _       , _       ->
           raiseTypeException (TODO "complete equivTerms_rec function")
     in equivTypes_rec 0 t1 (fun _ -> None) t2 (fun _ -> None)

let equivTypeExprs (ctx:context) (t1:type_expr) (t2:type_expr) =
     match t1, t2 with
     | Prop, Prop -> true
     | TypeComp t1', TypeComp t2' -> equivTypes ctx t1' t2'
     | TypeComp _, Prop
     | Prop, TypeComp _ -> false

(**
 * Checks whether two sort types are identical
 * @param (t1 : sort_type) : The first sort type
 * @param (t2 : sort_type) : The second sort type
 * @return(bool)           : True if they are identical, false otherwise
 *)
let equivSortTypes t1 t2 = match t1, t2 with
     | Kind a, Kind b -> a = b
     | Sort, Sort -> true
     | Sort, Kind _
     | Kind _, Sort -> false

let uniqueTypes (ctx:context) = function
    | [] -> true
    | t :: ts -> for_all (fun s -> equivTypeExprs ctx t s) ts

(* useful type-checking abbreviations *)
(**
 * Checks if a type expression is a type (not a kind)
 *
 * @param ttx  : Type expression to check
 * @param orig :
 * @return (bool) : True if the type expression is a 'type', false otherwise  
 *)
let check_type_type ttx orig = match ttx with
    | Sort   -> raiseTypeException (TypeTypeError (ttx, orig))
    | Kind _ -> ()

let check_typecomp ctx t a orig =
     if not (equivTypeExprs ctx t (TypeComp a)) then 
         raiseTypeException (TypeError (TypeComp a, t, orig))

let check_typetypecomp ctx t a orig =
     if not (equivTypeExprs ctx t (TypeComp a)) then raiseTypeException (TypeKindError (TypeComp a, t, orig))

let check_prop ctx t orig =
     if not (equivTypeExprs ctx t Prop) then raiseTypeException (TypeError (Prop, t, orig))

(* checks if b:a is consistent *)
let check_consistent a b = equivSortTypes b a

(** codomain: type_comp -> type_comp
    Returns the "deep" codomain of a (curried) function.
    This is used to type check inductive data types *)
let rec codomain ctx t = match headNormalForm ctx t with
   | TArrow (_,c) -> codomain ctx c
   | TDepId (_,c) -> codomain ctx c
   | Type | TId _ | TApp _ | TProd _ | TInduct _ | TTheory _
   | TTypeFromTheory _
   | TPower _ | TPredicate _ | TRecord _ | TLift _ | TProof _ -> t
   | TBinder _ -> failwith "what is the codomain of a type constructor?"

let rec lookupField term fl f = match fl with
    | [] -> raiseTypeException (FieldNameNotFound term)
    | (FieldSig (n,t)) :: fl' -> if n = f then t else lookupField term fl' f 

(**
 * Given context, this checks that a 'type_comp' is a valid type.
 * It returns the synthesised kind of the type
 *
 * @param ctx: The typing context
 * @param ty : The type_comp to be checked
 * @return   : The synthesized kind of the that type_comp (of type sort_type) 
 *)
let rec type_type_check (ctx:context) ty = 
 let type_type_check_list l = 
   iter (fun t -> let tx = type_type_check ctx t in check_type_type tx ty) l;
   Kind KStar
 in match ty with
 | Type -> Sort
 | TId x -> 
    let tx = lookupType ctx x in
    let ttx = type_type_check ctx tx in
    if equivSortTypes ttx Sort then Kind KStar
    else 
        raiseTypeException (TypeTypeError (ttx, ty))
 | TDepId (_,_) -> (*conservatively raise an error for now *)
    raiseTypeException (Unexpected ty) (* type_type_check ctx t *)
 | TApp (t1,t2) -> 
    let _ = type_type_check ctx t1 in
    let t1' = evalType ctx (headNormalForm ctx t1) in
    (* t1' is fine as a type, dispatch on it *)
    begin match t1' with
         | TArrow (ta,_) -> 
             let t2' = evalType ctx t2 in
             if not (equivTypes ctx ta t2') then 
                 raiseTypeException (TypeKindError (TypeComp ta, TypeComp t2, ty))
             else
                 Kind KStar
         | TDepId _ (* could this happen? *)
         | Type | TId _ | TApp _ | TProd _ | TInduct _ 
         | TPower _ | TPredicate _ | TRecord _ | TLift _ | TTheory _ 
         | TTypeFromTheory _ | TProof _ -> 
            raiseTypeException (TAppError (t1',ty)) 
         | TBinder _ -> raiseTypeException (TODO "uh oh, TApp of a TBinder!")
     end
 | TProd l -> let (tx, _) = 
     fold_left acc_dep_type_type_check (Kind KStar, ctx) l in tx
 | TArrow (t1,t2) -> 
     let (k1, ctx') = dep_type_type_check ctx t1 in
     let k2 = type_type_check ctx' t2 in                     
     (match (k1,k2) with
     | (Kind _, Kind _) -> Kind KStar
     | (Sort, Kind kk2) -> Kind KStar
     | (Kind kk1, Sort) -> Sort
     | (Sort, Sort)     -> Sort)
 | TInduct (n,cs) -> iter (checkConstrDecl n ctx) cs; Kind KStar
 | TTheory _ -> failwith "TTheory should have been expanded away before typechecking"
 | TTypeFromTheory _ -> failwith "TTypeFromTheory should have been expanded away before typechecking"
 | TPower t -> type_type_check_list [t]
 | TPredicate t -> type_type_check_list [t]
 | TRecord tdl -> 
    (* Make sure there are no duplicate labels *)
    if not (Util.unique (map getFieldSigName tdl)) then 
        raiseTypeException (DuplicateFieldNamesType ty);                                    
    (* Define the depends_on function *)                                    
    let dps x =
        try
            let field = find (fun y -> x = getFieldSigName y) tdl in
               Bindings.type_dps_on (getFieldSigType field)
        with
              (* The field does not depend on any other fields in the record, 
                   it might have been defined in the outside scope *)
            | Not_found -> Util.NS.empty
    in                  
    (* Convert the list of fields into a string map since Toposort.stable_top_sort requires this*)
    let stringMap = List.fold_left 
                     (fun currentMap (FieldSig (n,typ)) -> Util.StringMap.add n typ currentMap)
                   Util.StringMap.empty tdl in
    (* All labels in the record *)
    let labels = Util.keys stringMap in        
    let depth_map = Toposort.depth_mark_objs labels dps in
    (* Sort the fields topologically *)
    let ret = Toposort.stable_top_sort depth_map stringMap in        
       ignore (List.fold_left (fun ctx0 (n,t) -> 
           ignore (type_type_check ctx0 t);
           extend_ctx1 ctx0 n t) ctx ret);
       Kind KStar
 | TLift tm -> ignore (term_synth ctx tm); Kind KStar
 | TProof tm ->  (match (term_synth ctx tm) with
                   | Prop -> Kind KStar
                   | TypeComp _ -> raiseTypeException (FormulaExpected tm))
 | TBinder (VarSpec(_, None), _) -> failwith "must annotate TBinder"
 | TBinder (VarSpec(names, Some vty), ttt) -> 
   if not (Util.unique names) then raiseTypeException (DuplicateTBinderNames ttt);
   let _ = type_type_check ctx vty in
   let ctx' = extend_ctx ctx names vty in
   let t2 = type_type_check ctx' ttt in
   if equivSortTypes t2 Sort then Sort
   else (check_type_type t2 ty; Kind KStar )
and dep_type_type_check (ctx:context) ty : sort_type * context = match ty with
 | TDepId (n,t) -> (type_type_check ctx t, extend_ctx ctx [n] t)
 | Type | TId _ | TApp _ | TProd _ | TInduct _ | TTheory _ | TArrow _
 | TTypeFromTheory _ | TBinder _
 | TPower _ | TPredicate _ | TRecord _ | TLift _ | TProof _ -> 
     (type_type_check ctx ty, ctx)
and acc_dep_type_type_check (k,ctx) ty =
    let (k', ctx') = dep_type_type_check ctx ty in
    if k = k' then (k', ctx')
    else raiseTypeException (TProdDifferentTypes(ty, k', k))
 
(** checkConstrDecl: indent -> context -> constructor -> ()
    Given the name of the inductive type and a context this 
    checks that a given constructor is type correct and has a return type
    of the given name.  This does not check positivity of the operator as
    that check is in general undecidable and requires a proof. *)
and checkConstrDecl (name:ident) (ctx:context) (dcl:field_sig) = 
        let ctx' = extend_ctx ctx [name] Type in
        match dcl with
        | FieldSig (x,t) -> 
           if not (equivSortTypes (type_type_check ctx' t) (Kind KStar))
           then raiseTypeException (ConstructorTypeError (name,x,(type_type_check ctx' t)));
           let codom = codomain ctx' t in
           if not (equivTypeExprs ctx' (TypeComp codom) (TypeComp (TId name)))
           then raiseTypeException (ConstructorCodomainError (name,x,codom))

(** term_synth : context -> expr -> type_expr
    This type checks a given expression in a given context.
    It returns the synthesized type for the expression. *)
and term_synth (ctx:context) term = 
 let rec term_synth_application e fun_type = 
       match headNormalForm ctx fun_type with
       | TArrow (a,b) -> 
          let (n, a') = getDepId a in
          term_check ctx e (TypeComp a');
          let b' = match n with
                   | Some n' -> Subst.type_sub (Subst.simpleExprSub n' e) b
                   | None    -> b
                   in
          let ttx = type_type_check ctx b' in
          check_type_type ttx b';
          TypeComp b'
       | TPredicate a ->
          term_check ctx e (TypeComp a);
          Prop
       | TBinder _ -> failwith "term_synth_application on a TBinder"
       | Type | TId _ | TApp _ | TProd _ | TInduct _  | TPower _ 
       | TTheory _ | TDepId _ | TLift _ | TTypeFromTheory _ | TProof _
       | TRecord _ -> raiseTypeException (AppError (TypeComp fun_type,term))
 in let checkName n = let tx = lookupType ctx n in
                      let ttx = type_type_check ctx tx in 
                      check_type_type ttx tx;
                      TypeComp tx
 in let check2prop e1 e2 = 
        let t1 = term_synth ctx e1 in check_prop ctx t1 term;
        let t2 = term_synth ctx e2 in check_prop ctx t2 term;
        Prop
 in match term with
 | Ident x -> checkName x
 | BTrue | BFalse -> Prop
 | EqOp (e1,e2) -> let t1 = term_synth ctx e1 in
                   let t2 = term_synth ctx e2 in
                   if not (equivTypeExprs ctx t1 t2) then raiseTypeException (TypeError (t1, t2, term));
                   Prop

 | In (e, ty) -> 
    let t1 = term_synth ctx e in
    let tty = type_type_check ctx ty in
    check_type_type tty ty;
    if not (equivTypeExprs ctx t1 (TypeComp ty)) then 
        raiseTypeException (TypeError(t1, TypeComp(ty), term));
    Prop

 | And (e1,e2) -> check2prop e1 e2
 | Or (e1,e2) -> check2prop e1 e2
 | Not e -> let t = term_synth ctx e in check_prop ctx t term; Prop
 | Iff (e1,e2) -> check2prop e1 e2
 | If (b, e1,e2) -> 
     let tb = term_synth ctx b in check_prop ctx tb term;
     let t1 = term_synth ctx e1 in
     let t2 = term_synth ctx e2 in
     if not (equivTypeExprs ctx t1 t2) then raiseTypeException (TypeError (t1, t2, term));
     t1
 | Implies (e1,e2) -> check2prop e1 e2
 | Appl (_,e1,e2) -> 
     let t1 = term_synth ctx e1 in
     begin match t1 with
     | Prop -> raiseTypeException (AppError (Prop,term))
     | TypeComp t1' -> term_synth_application e2 t1'
     end 
 | Desc (_, n, ty, e) ->
     let tty = type_type_check ctx ty in
     let t = term_synth (extend_ctx ctx [n] ty) e in
     check_type_type tty ty;
     check_prop ctx t term;
     TypeComp ty
 | Binder (_, VarSpec (_, None), _) -> raiseTypeException (TypeAnnotationRequired term);
 | Binder (q, VarSpec (names, Some ty), e) ->
   if not (Util.unique names) then raiseTypeException (DuplicateBinderNames term);
   let tty = type_type_check ctx ty in
   let t = term_synth (extend_ctx ctx names ty) e in
   check_type_type tty ty;
   (match q with
   | Forall | Exists | ExistsUniq -> check_prop ctx t term; Prop
   | Abs -> 
     (match t with
     | Prop -> if length names <> 1 then raiseTypeException (BadDescriptionList term);
               TypeComp (TPredicate ty)
     | TypeComp t' -> TypeComp 
       (fold_right (fun i b -> TArrow (TDepId (i, ty),b)) names t')
     )
   )
 | Let (i, e1, e2) ->
    let t1 = term_synth ctx e1 in
    (match t1 with
    | TypeComp t -> term_synth (extend_ctx ctx [i] t) e2
    | Prop -> raiseTypeException (PropError e1) )
 | Tuple es -> TypeComp (TProd (map 
     (fun e -> 
         match term_synth ctx e with
         | Prop -> raiseTypeException (PropError term)
         | TypeComp t -> t) es))
 | Record rs ->  if not (Util.unique (map (fun (FieldMem (n,_,_)) -> n) rs)) 
                 then raiseTypeException (DuplicateFieldNames term);
                 TypeComp (TRecord (snd (Util.map_accum_left (field_synth term) ctx rs)))
 | Selector (e,f) -> begin
     match term_synth ctx e with
     | Prop -> raiseTypeException (SelectorNeedsRecord term) 
     | TypeComp te -> TypeComp
      (match headNormalForm ctx te with
       | TRecord fns -> lookupField term fns f
       | Type | TId _ | TApp _ | TProd _ | TInduct _ | TPower _
       | TDepId _ | TLift _ | TTheory _ | TTypeFromTheory _ | TProof _
       | TBinder _
       | TPredicate _ | TArrow _ -> raiseTypeException (SelectorNeedsRecord term))
    end
 | Case _ -> raiseTypeException (CannotSynthesizeCaseType term)
 | Escape _ -> failwith "don't know how to typecheck escape"
 | Quote _ -> failwith "don't know how to typecheck quote"
 | Eval _ -> failwith "don't know how to typecheck eval"
 | ProofObject _ -> failwith "don't know how to typecheck proof object"
and field_synth term ctx (FieldMem (n,t,e)) = 
 let syn = (match term_synth ctx e with
                        | Prop -> raiseTypeException (PropError term)
                        | TypeComp t -> t)
 in (extend_ctx_def ctx n (TLift e),
     match t with
     | None -> FieldSig (n,syn)
     | Some ty ->  
         if not (equivTypes ctx ty syn) 
         then raiseTypeException (FieldTypeAnnotationMismatch (ty, syn, term));
         FieldSig (n,ty)
    )
and pattern_match ctx term ty pat =
    let rec chasePatApp p l = match p with 
       | PatConst i -> 
         let ity = headNormalForm ctx ty in
         let (iname, conty) = match ity with
             | TInduct (iname, fns) -> (iname, lookupField term fns i)
             | Type | TId _ | TApp _ | TProd _ | TPower _
             | TDepId _ | TLift _ | TRecord _ | TProof _ | TBinder _
             | TPredicate _ | TArrow _ -> raiseTypeException (CaseNeedsInductive term)
             | TTheory _ -> failwith "TTheory should have been expanded away before typechecking"
             | TTypeFromTheory _ -> failwith "TTypeFromTheory should have been expanded away before typechecking"       
         in let rec f ctx0 conty0 = 
                 let ctxInd = extend_ctx_def ctx0 iname ity in function
                 | []       -> if headNormalForm ctxInd conty0 = ity then ctx0
                               else raiseTypeException (BadInductiveType (iname, term))
                 | (p0::pl) -> begin match headNormalForm ctxInd conty0 with 
                               | TArrow (dom,codom) -> f (pattern_match ctx0 term dom p0) codom pl
                               | Type | TId _ | TApp _ | TProd _ | TInduct _ | TPower _
                               | TDepId _ | TLift _ | TPredicate _ | TTheory _ | TTypeFromTheory _ | TProof _
                               | TRecord _ -> raiseTypeException (ArrowExpected (p0, conty))
                               | TBinder _ -> failwith "no higher-order pattern match?"
                               end
         in f ctx conty l
       | PatApp (p1,p2) -> chasePatApp p1 (p2::l)
       | PatNone | PatIdent _ | PatTuple _ | PatRecord _ -> raiseTypeException (CaseNeedsInductive term)
    in let rec zipPatTuple ctx patl tyl = match patl, tyl with
       | [], [] -> ctx
       | (p::pl), (ty::tl) -> zipPatTuple (pattern_match ctx term ty p) pl tl
       | _, _   -> raiseTypeException (PatTupleNumberMismatch term)  
    in match pat with
       | PatNone -> ctx
       | PatIdent i -> extend_ctx1 ctx i ty
       | PatTuple patl -> begin match headNormalForm ctx ty with
                          | TProd tys -> zipPatTuple ctx patl tys
                          | Type | TId _ | TArrow _ | TApp _ | TInduct _ | TPower _
                          | TDepId _ | TLift _ | TPredicate _ | TTheory _ | TTypeFromTheory _ | TProof _
                          | TBinder _
                          | TRecord _ -> raiseTypeException (TupleExpected term)
                          end
       | PatRecord _ -> failwith "PatRecord NIY"
       | PatConst _ | PatApp _ -> chasePatApp pat []
and branch_check ctx term ty tye (Branch (pat, e)) = term_check (pattern_match ctx term ty pat) e tye
(** evalType : context -> type_comp -> type_comp 
    In a given context, resolve all the names of types up one level.
    This is used for type application checking; someone else will ensure
    that this is indeed 'valid' *)
and evalType ctx t = 
  let e = evalType ctx in
  match t with
  | Type -> t
  | TId x -> lookupType ctx x
  | TApp (x,y) -> TApp(e x, e y)
  | TArrow (x,y) -> TArrow(e x, e y)
  | TDepId (i,c) -> TDepId(i, e c)
  | TProd l -> TProd (List.map e l)
  | TInduct (n,l) -> 
      let ctx' = extend_ctx1 ctx n t in 
      let ee = evalType ctx' in
      TInduct(n, List.map (fun (FieldSig(n,s)) -> FieldSig(n,ee s)) l)
  | TTheory _ -> failwith "TTheory should have been expanded away before typechecking"
  | TTypeFromTheory _ -> failwith "TTypeFromTheory should have been expanded away before typechecking"
  | TPower t -> TPower(e t)
  | TPredicate t -> TPredicate(e t)
  | TLift x -> begin
      match term_synth ctx x with
      | TypeComp tx -> tx
      | Prop -> raiseTypeException (PropError x)
      end
   | TRecord l -> TRecord (List.map (fun (FieldSig(n,t)) -> FieldSig(n, e t)) l)
   | TProof _ -> failwith "What to do with TPRoof?" 
   | TBinder _ -> t (* don't evaluate under binders? *)

(** term_check : context -> expr -> type_expr -> ()
    This type checks that a given expression has a given type in a given context. *)
and term_check (ctx:context) term (ty:type_expr) = 
 match term with
 | Tuple l -> begin match headNormalFormExpr ctx ty with
              | TypeComp (TProd tys) ->
                     if not (length l = length tys) then raiseTypeException (TProdWrongLength (term, ty));
                     iter2 (fun x y -> term_check ctx x (TypeComp y)) l tys
              | _ -> raiseTypeException (TProdExpected (term, ty))
              end
 | Binder (Abs, VarSpec (names, tyn), e) ->
   if not (Util.unique names) then raiseTypeException (DuplicateBinderNames term);
   let _ = Util.map_option 
       (fun x -> check_type_type (type_type_check ctx x) x) tyn in
   let rec domains ctx0 ty0 l = 
           begin match headNormalForm ctx0 ty0, l with
           | _, [] -> (ctx0, TypeComp ty0)
           | TPredicate dom, [n] ->
                      let (_,domty) = getDepId dom in
                      begin match tyn with
                      | Some tyn0 -> if not (equivTypes ctx0 domty tyn0)
                                     then raiseTypeException (TypeError (TypeComp tyn0, TypeComp domty, term))
                      | None -> ()
                      end;
                      (extend_ctx1 ctx0 n domty, Prop)
           | TArrow (dom,codom), (n::t) ->
                      let (domn,domty) = getDepId dom in 
                      begin match tyn with
                      | Some tyn0 -> if not (equivTypes ctx0 domty tyn0)
                                     then raiseTypeException (TypeError (TypeComp tyn0, TypeComp domty, term))
                      | None -> ()
                      end;
                      let codom' = match domn with
                                   | Some n' -> Subst.type_sub (Subst.simpleExprSub n' (Ident n)) codom
                                   | None    -> codom
                      in domains (extend_ctx1 ctx0 n domty) codom' t
           | _, _ -> raiseTypeException (FunctionArrowExpected (term, TypeComp ty0))
           end in
   let (ctx0, codom) = begin match ty with
                       | Prop -> raiseTypeException (FunctionArrowExpected (term, ty))
                       | TypeComp ty0 -> domains ctx ty0 names
                       end in
   term_check ctx0 e codom
 | Case (e,cs) -> begin
     match term_synth ctx e with
     | Prop -> raiseTypeException (CaseNeedsInductive term) 
     (* TODO: Currently there is a bug that allows bindings to escape into 
              the types of the expressions in each branch.
              (This is a dependent typing issue) *)
     | TypeComp te -> iter (branch_check ctx term (headNormalForm ctx te) ty) cs
     end
  | Let(i,e1,e2) -> begin
    let t1 = term_synth ctx e1 in
    match t1 with
    | TypeComp t -> term_check (extend_ctx ctx [i] t) e2 ty
    | Prop -> raiseTypeException (PropError e1) 
    end
  | _ -> 
    let ty' = term_synth ctx term in
    if not (equivTypeExprs ctx ty ty') then raiseTypeException (TypeError (ty', ty, term))

(* Check various kinds of declarations and produces an extended context *)
(* TODO: this should be rewritten to operate on a more abstract data type *)
(**
 *   This checks that a given type declaration is valid in a given context.
 *
 *   @param ctx : typing context 
 *   @param decl: The type declaration to check
 *   @return    : the context extended with the new type declaration. 
 *)
let rec checkTypDecl (ctx:context) (dcl:typedecl) = 
    let check1 ctx t = 
        let tt = type_type_check ctx t in
        if not (equivSortTypes tt Sort || equivSortTypes tt (Kind KStar)) then
            raiseTypeException (TypDeclError dcl)
        else ctx in
    match dcl with
    | TBase (x,{kind = t; defn = d}) -> 
        let ctx' = (checkTypDecl ctx (TExtension ([x],t))) in
        (on_kind (fun d0 -> extend_ctx_def (check1 ctx' d0) x d0) ctx' d)
    | TExtension (names,t) -> extend_ctx (check1 ctx t) names t

(** checkAxiom: context -> axdecl -> ()
    This checks that a given axiom/theorem declaration is valid in a given context. *)
let checkAxiom (ctx:context) ((_,e,_) as dcl : axdecl) =
        let te = term_synth ctx e in
        if not (equivTypeExprs ctx te Prop) then raiseTypeException (AxiomError dcl)

(** checkFuncDecl: context -> funcdefn  -> ()
    This checks that a function declaration has the type in the given context.  *)

let checkFuncDecl (ctx:context) (lhs, e) = 
   let n = param_decl_name lhs in
   let ty = lookupType ctx n in
   let getDomains () = match headNormalForm ctx ty with
        | Type | TId _ | TApp _ | TProd _ | TInduct _ | TPower _
        | TDepId _ | TLift _ | TTheory _ | TTypeFromTheory _ | TProof _
        | TRecord _ -> raiseTypeException (ArrowExpected (PatIdent n,ty))
        | TBinder _  -> failwith "getDomains of TBinder"
        | TArrow (dom,codom) -> (dom, TypeComp codom)
        | TPredicate dom -> (dom,Prop) in
   let (ctx', codom) = match lhs with
       | PConst _ -> (ctx, TypeComp ty)
       | PUniOp (_,x) -> let (dom,codom) = getDomains () in 
                         (extend_ctx1 ctx x dom,codom)
       | PApp (n,_,ns) ->
         if not (Util.unique ns) then raiseTypeException (DuplicateBindings n);
         let (dom,codom) = getDomains () in
         match headNormalForm ctx dom with
         | Type | TId _ | TApp _ | TArrow _ | TInduct _ | TPredicate _
         | TDepId _ | TLift _  | TTheory _ | TTypeFromTheory _ | TProof _
         | TPower _ | TRecord _ | TBinder _ -> raiseTypeException (ProdExpected (PatIdent n,ty))
         | TProd l -> 
             if length ns <> length l then 
                 raiseTypeException (ParameterNumberMismatch (PatIdent n,ty));
             (fold_left2 extend_ctx1 ctx ns l, codom) in
    term_check ctx' e codom

(** checkDecl: context -> declaration -> context
    This checks that a given declariation is typesafe.
    It returns the new context that is valid after the declariation. *)
let rec checkDecl (ctx:context) = function 
    | TypDecl dcl -> checkTypDecl ctx dcl
    (* special kind of TypDecl *)
    | Induct (n,l) -> checkTypDecl ctx 
        (TBase(n, {kind = Type; defn = Manifest(TInduct(n,l))}))
    | FuncDecl dcl -> (checkFuncDecl ctx dcl; ctx)
    (* for the purposes of type checking, VarDecl is the same as TypDecl *)
    | VarDecl dcl -> fold_left checkTypDecl ctx dcl
    | Axiom dcl -> (checkAxiom ctx dcl; ctx)

(** checkDeclList: context -> declaration list -> context
    This checks that a given sequence declariation is typesafe.
    It returns the new context that is valid after the declariation sequence. *)
and checkDeclList (ctx:context) decls = fold_left checkDecl ctx decls

and typecheck = function
  | NamedArrow (_,AThy dcllist) ->
      let (_ : context) = checkDeclList empty_ctx dcllist in ()
  | NamedArrow _ | NamedSubst _ -> ()

exception TypeExceptionAt of (ident*typeExceptionData) list

let typecheck_toplevel (parse:toplevel_expr) =
    let tc parseItem =
        try typecheck parseItem; []
        with TypeException ex -> [(assign_name parseItem,ex)] in 
    let errs = flatten (map tc parse) in
    if not ([] = errs) then raise (TypeExceptionAt errs)

