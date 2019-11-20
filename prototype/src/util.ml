(* util.ml *)

(* A bunch of useful utility functions which really ought to have been
 * defined in a 'standard' library...
 *)

(* useful here and there *)
let identity = fun x -> x

module MakeBetterMap = functor(Ord: Map.OrderedType) -> struct
    module M = Map.Make(Ord)
    include M
    let assoc_list_to_map x = List.fold_left (fun s (k,v) -> add k v s) empty x
    let add_with k f m = let v = try Some (find k m) with Not_found -> None in
                         add k (f v) m
    let copy m = map identity m
end

module MakeBetterSet = functor(Ord: Set.OrderedType) -> struct
    module S = Set.Make(Ord)
    include S
    let list_to_set = List.fold_left (fun s x -> add x s) empty
    let setlist_union = List.fold_left (fun base s -> union base s) empty
end

module type BetterSet = sig
    include Set.S
    val list_to_set : elt list -> t
    val setlist_union : t list -> t
end

module Strings = struct
    type t = string
    let compare = compare
end

module StringPair = struct
    type t = string * string
    let compare = compare
end

module Nats = struct
    type t = int
    let compare = compare
end

module NS = MakeBetterSet(Strings)
module StringMap = MakeBetterMap(Strings)

let rec chain_lookup (l:('a->'b) list) (x:'a) : 'b =
    match l with
    | [] -> raise Not_found
    | [f] -> f x
    | f::fs -> 
        try f x
        with Not_found -> chain_lookup fs x

(* For name generation *)
let gen_sym root =
    let counter = ref 0 in
    let gen () =
        counter := !counter + 1;
        Printf.sprintf (root^^"%06n") !counter
    in gen

let gen_sym2 n1 n2 = Printf.sprintf ("%s_into_%s") n1 n2

let gen_thy_name : unit -> string = gen_sym "Unknown"
let gen_axiom_name : unit -> string = gen_sym "Axiom"
let gen_inject_name : string -> string -> string = gen_sym2
     
let total_rename (t:('a*'b) list) (a:'a) (b:'b) : 'b =
    try List.assoc a t with Not_found -> b

(* This should have an invariant that it only works on sorted lists,
 * but that's not expressible *)
let rec uniq : ('a list -> 'a list) = function
    | [] -> []
    | [x] -> [x]
    | x::y::xs -> if (x=y) then uniq (y::xs) else x::uniq(y::xs)

let foldi f init l =
    let rec foldi2 f acc n = function
    | [] -> acc
    | x::xs -> foldi2 f (f n x acc) (n+1) xs in
    foldi2 f init 0 l

(* fold_left2 : apply a function f to a list which accumulates 
 * context information (in a1) and result information (in a2).
 * Result information is combined via g *)
let fold_left2 (f,g) (i1,i2) l =
    let accum (a1, a2) x = let (na1, nx) = f a1 x in (na1, g nx a2) in
    List.fold_left accum (i1,i2) l

(* not sure why this is needed, but syntactically slices of :: are hard *)
let cons a b = a :: b

(* Same as mapAccumL from Haskell *)
let rec map_accum_left f e = function
    | []    -> (e,[])
    | x::xs -> let (e0, y) = f e x in
               let (e1, ys) = map_accum_left f e0 xs in
               (e1, y::ys)

(* for the maybe/option monad *)
let maybe f a = function
    | Some x -> f x
    | None   -> a
    
let map_option f = function
    | Some x -> Some (f x)
    | None   -> None

(* default function for option type *)
let default a = function
 | Some b -> b
 | None -> a

let replicate n x = 
    let rec go n l = if n <= 0 then l else go (n - 1) (x::l) in go n [] 

(* returns true when all the elements of a list are pairwise different *)
let rec unique = function 
        | [] -> true
        | (x :: xs) -> List.for_all (fun t -> t<>x) xs &&
                       unique xs

(* for maps - get a list of keys, with potential duplicates *)
let keys tbl = StringMap.fold (fun k _ l -> k :: l) tbl []

(* separate a string by using a character as a marker *)
let explode c s =
    let len = String.length s in
    let index k =
        try
           let nxt = String.index_from s k c in
           (nxt, String.sub s k (nxt-k)) 
        with Not_found -> 
            (-1, String.sub s k (len-k)) in
    let rec accum pos acc =
        let (nxt, ss) = index pos in
        if nxt == -1 then
            ss :: acc
        else 
            accum (nxt+1) (ss :: acc) in
    List.rev (accum 0 [])
