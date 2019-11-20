(* check that constructions are well-typed, according
   to the categorical semantics. This only checks the
   arrow-level. *)

open Syntax
open Library

let arrow_check (nm:string) def lib = match def with
  | AThy _ -> lib
  | ACombine _ -> failwith "check: combine"
  | AExtend(src,_,dl) -> failwith "check: extend"
  | AInstance (src,_,s) -> failwith "check: instance"
  | ArrowName n -> failwith "check: synonym"
  | AParComp(r1,r2) -> failwith "check: parcomp"
  | ASeqComp(x,y,l) -> failwith "check: seqcomp"
  | ARename(a,s) -> failwith "check: rename"
  | AMixin(a,b) -> failwith "check: mixin"
  | ArrowId -> lib

(* let checklib lib = Util.StringMap.fold arrow_check lib.arrows lib *)
let checklib lib = lib

(* check that an arrow is a general extension *)
let rec genext lib = 
  let r x = genext lib (lookup_arrow lib x) in
  function
  | AThy _ -> ()
  | ACombine (l,_) -> List.iter r l
  | AExtend(src,_,dl) -> ()
  | AInstance (src,_,s) -> failwith "general extension?: instance"
  | ArrowName n -> r n
  | AParComp(n1,n2) -> r n1; r n2
  | ASeqComp(x,y,l) -> r x; r y; List.iter r l
  | ARename(a,s) -> ()
  | AMixin(_,_) -> failwith "general extension?: mixin"
  | ArrowId -> ()

