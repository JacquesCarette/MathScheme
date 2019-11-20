(* fold.ml *)

(* Folding and mapping function(s) over the syntax *)

open Syntax
open Plate

(* These only apply to the names that appear *)
module Name = struct

let map_type1 g x = match x with
  | (TId i) as x -> let res = g i in if res=i then x else TId res
  | _ -> x

let map_expr1 f x = match x with
  | Ident y -> Ident (f y)
  | _ -> x

let map f = mapFamily {bT = map_type1 f; cT = map_expr1 f} 

let map_type f = (map f).bT
let map_expr f = (map f).cT

let map_typrecord f {kind = t; defn = d} =
    {kind = map_type f t; defn = apply_to_type (map_type f) d}

let map_typedefn f = function
    | TBase (s, t) -> TBase(f s, map_typrecord f t)
    | TExtension (sl, t) -> 
        TExtension(List.map f sl, map_type f t)

(* TODO: alpha renaming *)
let map_funcdefn g (paramdecl, e) : funcdefn =
    let (f,b,ps) = getPApp paramdecl in
    (updateParam paramdecl (g f) b ps, map_expr g e)

let map_defn g (a,b) = (map_typrecord g a, map_funcdefn g b)

let map_axiom f (e,b) = (map_expr f e, b)

let map_fields = map_type

end
