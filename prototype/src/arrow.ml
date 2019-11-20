open Syntax
open Library
open Subst

module SM = Util.StringMap

(* Given an arrow (encoded as a binding), return the base theory, as
 * a name.  Eventually, we might use the convention that the
 * arrow name starts with a lower case letter, while the (ground) theory is
 * the instantiation of an arrow from Empty. 
 *
 * The 'base' is actually the Codomain in Ctx
 *)
let rec base lib def = 
    let resolve x = SM.find x lib.arrows in 
    let find = function
    | AThy _ -> Bindings.emptyThyName
    | ACombine (_,ov) -> ov 
    | AMixin ((r1,_),(r2,_)) ->
        let b1 = base lib (resolve r1) and b2 = base lib (resolve r2) in
        if b1 = b2 then b1 else failwith "Mixin on different bases"
    | AExtend (src, _, _) -> src
    | AInstance(_,n,_) -> n (* TODO: might be wrong too *)
    | ArrowName n -> base lib (resolve n)
    | AParComp(r1,r2) -> 
        let b1 = base lib (resolve r1) and b2 = base lib (resolve r2) in
        if b1 = b2 then b1 else failwith "ParComp on different bases"
    | ASeqComp (x,_,_) -> base lib (resolve x)
    | ARename (n,_) -> n
    | ArrowId -> failwith "base of ArrowId"
    in find def

(* The tail of an arrow is always trivial, since that is exactly what
   we are constructing *)
let tail _ (nm,def) = nm

let id = { type_subs = []; expr_subs = []; var_subs = []}

let subst lib (nm,def) = match def with
  | AThy _ -> id
  | ACombine _ -> failwith "don't know how to compute the substitution induced by combine"
  | AMixin _ -> failwith "don't know how to compute the substitution induced by mixin"
  | AExtend(_,_,_) -> id (* because we just drop the extensions *)
  | AInstance (_,_,s) -> { type_subs = []; expr_subs = s; var_subs = []}
  | ArrowName n -> id
  | AParComp(r1,r2) -> failwith "need to figure out subs of parcomp"
  | ASeqComp(x,y,l) -> failwith "need to figure out subs of seqcomp"
  | ARename(_,s) -> { type_subs = []; expr_subs = []; var_subs = s}
  | ArrowId -> id

