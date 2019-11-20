(* reify.ml *)

open Syntax
open Bindings
open Library

module SM = Util.StringMap

(* Take a bindings and return a syntactic version of it *)
let reify name b = 
 Log.log ("reifying "^name^"\n");
 try
  let deps = get_depends b in
  let typs = SM.fold (fun k (v,_) b -> SM.add k v b) (get_defns b) (get_symb b) in
  let names = Util.keys (get_symb b) @ Util.keys (get_defns b) in
  let mkTyp (k,v) = TypDecl(TBase(k,v)) in
  let toaxiom (a,b,c) = Axiom(Some a, b, c) in
  let addDefn k (v1,v2) l = FuncDecl(v2)::l in
  let d_types = Toposort.depth_mark_objs names (Toposort.find_with_empty deps) in
  let typdecls = List.map mkTyp (Toposort.stable_top_sort d_types typs) in
  List.concat [
    typdecls;
    (let vd = SM.fold (fun k v l -> TBase(k,mkType v)::l) (get_vars b) [] in
    if vd=[] then [] else [VarDecl(vd)]);
    SM.fold addDefn (get_defns b) [];
    SM.fold (fun k (ax,b) l -> toaxiom (k,ax,b)::l) (get_props b) []
  ]
 with Exceptions.Dependency x -> 
     failwith ("Dependency for "^x^" not found in "^name)

let bindings map = SM.fold (fun k v l -> (k,v)::l) map []

let reify_libraryH expand newlib =
    Log.log "Reifying\n";
    let arrows = newlib.arrows in
    (* let mkThy (n,v) = 
        match v with 
        | ThyTBase (_,b) -> [Assign(n, reify n b)]
        | ThyTComb (n,(ml,m)) -> [NamedArrow(n, ACombine (ml,m))]
        | Rename (m,l) -> [NamedArrow(n, ARename (m,l))] 
        | ThyTExtend (n,m,q,b) -> 
            [NamedArrow(n, AExtend (m, q, reify n (extract_bindings b)))]
        | ThyInstance(n1,n2,l) -> [NamedArrow(n, AInstance(n1,n2,l))]
        | ArrowN m -> [NamedArrow(n,ArrowName m)]
        | ParComp(a1,a2) -> [NamedArrow(n,AParComp(a1, a2))]
        | SeqComp(x,y,l) -> [NamedArrow(n,ASeqComp(x,y,l))]
        in *)
    let (rootTheories, rest) =
        (* If there is an expanded (grounded) version, use that *)
        let process k x (root, rst) = 
            try 
                (SM.add k (AThy (reify k (SM.find k newlib.theories))) root, rst)
            with Not_found -> (root, SM.add k x rst) in
        if expand then 
            SM.fold process arrows (SM.empty, SM.empty)
        else 
            (arrows, SM.empty) in
    Log.log "Finished filtering\n";
    (* deal with topologically sorting the theories and arrows *)
    let thy_deps = SM.map thy_dps_on rootTheories in
    let finder = Toposort.find_with_exception thy_deps in
    let d_thy = Toposort.depth_mark_objs (Util.keys thy_deps) finder in
    Log.log "Finished marking arrows\n";
    let thy_list = List.map (fun (a,b) -> NamedArrow(a,b) ) (Toposort.stable_top_sort d_thy rootTheories) in
    Log.log "Finished sorting (root) arrows\n";
    let keys_of_arr = Util.keys rest in
    let arr_list = List.map (fun x -> NamedArrow(x,SM.find x rest)) keys_of_arr in
    Log.log "Finished sorting arrows\n";
    thy_list @ arr_list

let reify_library = reify_libraryH false

let reify_expanded_library = reify_libraryH true
