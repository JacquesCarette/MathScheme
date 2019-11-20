(* toposort.ml *)

(* Routines to do stable topological sorting in our setting.  Use
 * 2 Maps, one from strings to 'depth' (from a depth-first walk of
 * the dependency graph), and a reverse lookup from depth to lists of
 * strings *)

module NatMap = Map.Make(Util.Nats)
module Depth = Map.Make(Util.Strings)

(* return the keys from the map, in the same order *)
let natmap_keys nm = List.rev (NatMap.fold (fun k _ l -> k :: l) nm [])

let find_with_exception tbl x =
    try Util.StringMap.find x tbl
    with Not_found -> raise (Exceptions.Dependency x)

let find_with_empty tbl x =
    try Util.StringMap.find x tbl
    with Not_found -> Util.NS.empty

(* given a list of objects (strings), use dependency map *)
(**
 * Compute (depth -> list of strings) map
 * 
 * @param objs   : List of strings
 * @param depend : A depends_on relation       
 *
 * @return       : 
 *)
let depth_mark_objs objs depend = 
    let rec mark d x = 
        if not (Depth.mem x d) then begin
            let deps = Util.NS.remove x (depend x) in
            let nd =
                if not (deps == Util.NS.empty) then 
                    Util.NS.fold (fun e info -> mark info e) deps d
                else
                    d in
            let depthx = Util.NS.fold (fun e acc -> max (Depth.find e nd)  acc) deps 0 in
            Depth.add x (depthx+1) nd end
        else
            d
        in
    let depth = List.fold_left mark Depth.empty objs in
    let addval x d nm = 
        try 
            x :: NatMap.find d nm
        with Not_found -> [x] in
    Depth.fold (fun s d nm -> if List.mem s objs then NatMap.add d (addval s d nm) nm else nm) depth NatMap.empty

(* Given a NatMap, and a lookup table, return a sorted (key,val) list *)
let stable_top_sort nm lookup =
    let keys = natmap_keys nm in
    let ss = List.map (fun x ->
            let y = List.sort compare (NatMap.find x nm) in
            List.map (fun z -> (z, find_with_exception lookup z)) y) keys in
    List.flatten ss
