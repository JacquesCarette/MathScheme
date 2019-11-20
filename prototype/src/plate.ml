open Syntax

(***************** Multiplate implementation for two mutually recursive types *********************)

(*******  syntaxTransforms are just a 2-tuple of transformers *******)
type ('b,'c) syntaxTransform = { bT : 'b -> 'b ; cT : 'c -> 'c }

let idT = { bT = fun t -> t;
          ; cT = fun e -> e;
          }

let composeT f1 f2 = 
    { bT = (fun t -> (f1).bT ((f2).bT t))
    ; cT = (fun e -> (f1).cT ((f2).cT e))
    }

module type Two = sig 
  type b 
  type c
end

(*****  A Multiplate depends on an n-ary Cartesian Store (parametrically) *****)
module CartStore(T:Two) = struct 
type 'a cartesianStore = 
    Unit of 'a
  | B    of T.b * (T.b -> 'a) cartesianStore
  | C    of T.c * (T.c -> 'a) cartesianStore

(* This will work in Ocaml 3.12 
let rec storeMap : 'a 'b . ('a -> 'b) -> 'a cartesianStore -> 'b cartesianStore =
  fun f -> function
  | Unit a -> Unit (f a)
  | B (ty,s) -> B (ty, storeMap (fun g x -> f (g x)) s)
  | C (ex,s) -> C (ex, storeMap (fun g x -> f (g x)) s)
*)
let storeMap f x = 
  let module StoreMap = struct
    type sm = { sm : 'a 'b . ('a -> 'b) -> 'a cartesianStore -> 'b cartesianStore }
    let rec storeMap = { sm = fun f -> function
        | Unit a -> Unit (f a)
        | B (ty,s) -> B (ty, storeMap.sm (fun g x -> f (g x)) s)
        | C (ex,s) -> C (ex, storeMap.sm (fun g x -> f (g x)) s)
        }
    end in StoreMap.storeMap.StoreMap.sm f x
    
(* This will work in Ocaml 3.12 
let rec storeExtract : 'a . 'a cartesianStore -> 'a = function 
  | Unit a -> a
  | B (ty,s) -> storeExtract s ty
  | C (ex,s) -> storeExtract s ex
*)
let storeExtract x = 
  let module StoreExtract = struct
    type se = { se : 'a . 'a cartesianStore -> 'a }
    let rec storeExtract = { se = function
        | Unit a -> a
        | B (ty,s) -> storeExtract.se s ty
        | C (ex,s) -> storeExtract.se s ex
        }
    end in StoreExtract.storeExtract.StoreExtract.se x
    
(* This will work in Ocaml 3.12 
let rec storeAp : 'a 'b . ('a -> 'b) cartesianStore -> 'a cartesianStore -> 'b cartesianStore =
   fun f = function
   | Unit a             -> storeMap (fun g -> g a) f
   | B (ty,s) -> B (ty, storeAp (storeMap (fun g h x -> (g (h x))) f) s)
   | C (ex,s) -> C (ex, storeAp (storeMap (fun g h x -> (g (h x))) f) s)
*)
let storeAp f x = 
  let module StoreAp = struct
    type sa = { sa : 'a 'b . ('a -> 'b) cartesianStore -> 'a cartesianStore -> 'b cartesianStore }
    let rec storeAp = { sa = fun f -> function
        | Unit a             -> storeMap (fun g -> g a) f
        | B (ty,s) -> B (ty, storeAp.sa (storeMap (fun g h x -> (g (h x))) f) s)
        | C (ex,s) -> C (ex, storeAp.sa (storeMap (fun g h x -> (g (h x))) f) s)
        }
    end in StoreAp.storeAp.StoreAp.sa f x

let rec storeSequence = function
    | []    -> Unit []
    | x::xs -> storeAp (storeMap (fun hd tl -> hd::tl) x) (storeSequence xs)

let storeTraverse f l = storeSequence (List.map f l)

let rec storeSequenceOption = function
    | None    -> Unit None
    | Some x  -> storeMap (fun y -> Some y) x

let storeTraverseOption f l = storeSequenceOption (Util.map_option f l)

(* This will work in Ocaml 3.12 
let rec transformStore : 'a . T.syntaxTransform -> 'a cartesianStore -> 'a cartesianStore = fun f x -> match x with
  | Unit a -> x
  | B (t,s) -> B (f.bT t, transformStore f s)
  | C (e,s) -> C (f.cT e, transformStore f s)
*)
let transformStore f x = 
  let module TransformStore = struct
    type ts = { ts : 'a . (T.b,T.c) syntaxTransform -> 'a cartesianStore -> 'a cartesianStore }
    let rec transformStore = { ts = fun f x -> match x with
          | Unit _ -> x
          | B (t,s) -> B (f.bT t, transformStore.ts f s)
          | C (e,s) -> C (f.cT e, transformStore.ts f s)
          }
    end in TransformStore.transformStore.TransformStore.ts f x

(* how do I make this generic over all BetterMaps? *)
let storeSequenceSM sm = let module SM = Util.StringMap in
                         SM.fold (fun k v r -> storeAp (storeMap (SM.add k) v) r) sm (Unit SM.empty)
                         
let storeTraverseSM f sm = let module SM = Util.StringMap in
                           SM.fold (fun k v r -> storeAp (storeMap (SM.add k) (f v)) r) sm (Unit SM.empty)

(* Convenience *)
let none    a = Unit a
let child_b b = B (b, Unit (fun x -> x))
let child_c c = C (c, Unit (fun x -> x))

(*
let getSelections s =
  let module GetSelections = struct
    type gs = { gs : 'a. proper list -> ('a cartesianStore) -> proper list }
    let rec getSelections = { gs = fun x -> function
          | Unit _ -> x
          | B (ty,s) -> getSelections.gs (ECType ty :: x) s
          | C (ex,s) -> getSelections.gs (ECExpr ty :: x) s
          }
    end in GetSelections.getSelections.GetSelections.gs [] s
*)

let mapChildren pl f x = storeExtract (transformStore f (pl x))
end

module ExprType = struct
  type b = type_comp
  type c = expr
end

module ETT = struct
module CS = CartStore(ExprType)

let plate_field_sig (FieldSig (f,t)) =
 CS.storeMap (fun nt -> FieldSig (f,nt)) (CS.child_b t)

let plate_type ity = match ity with
  | Type
  | TId _
  | TTheory _
  | TProof _
  | TTypeFromTheory _ -> CS.none ity
  | TApp (t1,t2) -> CS.storeAp (CS.storeMap (fun nt1 nt2 -> TApp (nt1, nt2))
                            (CS.child_b t1)) (CS.child_b t2)
  | TProd tl -> CS.storeMap (fun ntl -> TProd ntl) (CS.storeTraverse CS.child_b tl)
  | TArrow (t1,t2) -> CS.storeAp (CS.storeMap (fun nt1 nt2 -> TArrow (nt1, nt2))
                            (CS.child_b t1)) (CS.child_b t2)
  | TPower t -> CS.storeMap (fun nt -> TPower nt) (CS.child_b t)
  | TInduct (i, fsl) -> CS.storeMap (fun nfsl -> TInduct (i,nfsl))
                         (CS.storeTraverse plate_field_sig fsl)
  | TPredicate t -> CS.storeMap (fun nt -> TPredicate nt) (CS.child_b t)
  | TRecord fsl -> CS.storeMap (fun nfsl -> TRecord nfsl)
                         (CS.storeTraverse plate_field_sig fsl)
  | TDepId (i,t) -> CS.storeMap (fun nt -> TDepId (i,nt)) (CS.child_b t)
  | TLift e -> CS.storeMap (fun ne -> TLift ne) (CS.child_c e)
  | TBinder (VarSpec (il, t) ,e) -> CS.storeAp (CS.storeMap (fun nt ne -> TBinder (VarSpec (il, nt), ne))
                                      (CS.storeTraverseOption CS.child_b t)) (CS.child_b e)

let plate_expr iex = match iex with
  | Ident _ -> CS.none iex
  | BTrue | BFalse -> CS.none iex
  | Quote _ -> CS.none iex (* subexpressions of Quotes are not considered subexpressions *)
  | EqOp (e1,e2) -> CS.storeAp (CS.storeMap (fun ne1 ne2 -> EqOp (ne1, ne2))
                            (CS.child_c e1)) (CS.child_c e2)
  | In (e,t) -> CS.storeAp (CS.storeMap (fun ne nt -> In (ne, nt))
                            (CS.child_c e)) (CS.child_b t)
  | And (e1,e2) -> CS.storeAp (CS.storeMap (fun ne1 ne2 -> And (ne1, ne2))
                            (CS.child_c e1)) (CS.child_c e2)
  | Or (e1,e2) -> CS.storeAp (CS.storeMap (fun ne1 ne2 -> Or (ne1, ne2))
                            (CS.child_c e1)) (CS.child_c e2)
  | Not e -> CS.storeMap (fun ne -> Not ne) (CS.child_c e)
  | Iff (e1,e2) -> CS.storeAp (CS.storeMap (fun ne1 ne2 -> Iff (ne1, ne2))
                            (CS.child_c e1)) (CS.child_c e2)
  | Implies (e1,e2) -> CS.storeAp (CS.storeMap (fun ne1 ne2 -> Implies (ne1, ne2))
                            (CS.child_c e1)) (CS.child_c e2)
  | Appl (b,e1,e2) -> 
               CS.storeAp (CS.storeMap (fun ne1 ne2 -> Appl (b, ne1, ne2))
                            (CS.child_c e1)) (CS.child_c e2)
  | Binder (q,VarSpec (il, t) ,e) -> 
    CS.storeAp (CS.storeMap (fun nt ne -> Binder (q, VarSpec (il, nt), ne))
                            (CS.storeTraverseOption CS.child_b t)) (CS.child_c e)
  | Desc (c, i, t, e) -> CS.storeAp (CS.storeMap (fun nt ne -> Desc (c, i, nt, ne))
                          (CS.child_b t)) (CS.child_c e)
  | Tuple el -> CS.storeMap (fun nel -> Tuple nel) (CS.storeTraverse CS.child_c el)
  | Record fml -> CS.storeMap (fun nfml -> Record nfml) 
                  (CS.storeTraverse (fun (FieldMem (f,ot, e)) ->
                                  CS.storeAp (CS.storeMap (fun not ne -> FieldMem (f,not,ne))
                                           (CS.storeTraverseOption CS.child_b ot)) (CS.child_c e)
                                ) fml)
  | Selector (e, f) -> CS.storeMap (fun ne -> Selector (ne,f)) (CS.child_c e)
  | Case (e, cl) -> 
    CS.storeAp (CS.storeMap (fun ne ncl -> Case (ne, ncl)) (CS.child_c e)) 
               (CS.storeTraverse 
                   (fun (Branch (p,e1)) -> CS.storeMap (fun ne1 -> Branch (p,ne1))
                                                     (CS.child_c e1)) cl)
  | Let (i, e1, e2) -> CS.storeAp 
    (CS.storeMap (fun ne1 ne2 -> Let(i, e1, e2)) (CS.child_c e1)) (CS.child_c e2)
  | If (e1, e2, e3) -> CS.storeAp (CS.storeAp (CS.storeMap (fun ne1 ne2 ne3 -> If (ne1, ne2, ne3))
                        (CS.child_c e1)) (CS.child_c e2)) (CS.child_c e3)
  | Escape e -> CS.storeMap (fun ne -> Escape ne) (CS.child_c e)
  | Eval (e,t) -> CS.storeAp (CS.storeMap (fun ne nt -> Eval (ne,nt))
                   (CS.child_c e)) (CS.child_b t)
  | ProofObject _ -> CS.none iex

type ('b,'c) syntax = SyntaxB of 'b
                    | SyntaxC of 'c

type ('a,'b,'c) syntaxFold = ('b, 'c) syntax -> 'a -> 'a

let foldCompose f1 f2 sy b = f1 sy (f2 sy b)

(* This will work in Ocaml 3.12 
let rec foldStore : 'a 'b . 'b syntaxFold -> 'a cartesianStore -> 'b -> 'b = fun f x z -> match x with
  | Unit a -> z
  | BatteryType (t,s) -> foldStore f s (f.foldType t b)
  | BatteryExpr (e,s) -> foldStore f s (f.foldExpr e b)
*)
let foldStore f x b =
  let module FoldStore = struct
    type 'b fs = { fs : 'a . ('b,type_comp,expr) syntaxFold -> 'a CS.cartesianStore -> 'b -> 'b}
    let rec foldStore = { fs = fun f x b -> match x with
          | CS.Unit _ -> b
          | CS.B (t,s) -> foldStore.fs f s (f (SyntaxB t) b)
          | CS.C (e,s) -> foldStore.fs f s (f (SyntaxC e) b)
          }
    end in FoldStore.foldStore.FoldStore.fs f x b

let foldChildren f sy b = match sy with
                          | SyntaxB ty -> foldStore f (plate_type ty) b
                          | SyntaxC ex -> foldStore f (plate_expr ex) b

let rec foldFamily f sy b = foldCompose f (foldChildren (foldFamily f)) sy b

end

(* TODO: could be split into a generic part and a specific part *)
let mapChildrenT f = { bT = fun t -> ETT.CS.mapChildren ETT.plate_type (Lazy.force f) t;
                     ; cT = fun e -> ETT.CS.mapChildren ETT.plate_expr (Lazy.force f) e
                     }

let storeTraverseDefnKind f = function
    | NoDefn     -> ETT.CS.Unit NoDefn
    | Manifest x -> ETT.CS.storeMap (fun y -> Manifest y) (f x)
    | SubType x  -> ETT.CS.storeMap (fun y -> SubType y) (f x)

let plate_typ_decl td =
    ETT.CS.storeAp (ETT.CS.storeMap (fun nkd ndef -> {kind = nkd; defn = ndef})
        (ETT.CS.child_b (td.kind)))
        (storeTraverseDefnKind ETT.CS.child_b (td.defn))

let plate_funcdefn (pd,e) = ETT.CS.storeMap (fun ne -> (pd,ne)) (ETT.CS.child_c e)

let rec mapFamily f = composeT f (mapChildrenT (lazy (mapFamily f)))
