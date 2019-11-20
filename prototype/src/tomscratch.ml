
type ('a,'b) staged = 
     Now of 'a 
   | PartialUnary of (('a,'b) staged->('a,'b) staged) ref * ('a,'b) staged 
   | PartialBinary of (('a,'b) staged->('a,'b) staged->('a,'b) staged) ref * ('a,'b) staged * ('a,'b) staged 
   | Later of 'a

let unary op =
  let f = ref (fun x -> failwith "Dummy unary") in
  f :=
    (function 
      | (Now x) -> Now (op x)
      | x       -> PartialUnary (f, x)
  ); f

let binary op =
  let f = ref (fun x y -> failwith "Dummy binary") in
  f := 
    (fun x y -> match (x,y) with
      | (Now x), (Now y) -> Now (op x y)
      | x, y             -> PartialBinary (f, x, y)
    ); f

module Make = struct

  let ring (zero:'a)  (one:'a) (neg:('a->'a) ref) (mult:('a->'a->'a) ref) (plus:('a->'a->'a) ref) =
    let negone = !neg one in
    let k = !mult in 
    mult := 
      (fun x y ->
        match x, y with
        | x, y when x = negone -> !neg y
        | x, y when y = negone -> !neg x
        | _ -> k x y
      )
end

let rec printStaged = function
  | Now x -> "(Now "^(string_of_int x)^")"
  | PartialUnary (f,x) -> "P("^(printStaged x)^")"
  | PartialBinary (f,x,y) -> "P("^(printStaged x)^","^(printStaged y)^")"
  | Later x -> "(Later "^(string_of_int x)^")"

type t = (int, int) staged

let mult : (t->t->t) ref = binary ( * )
let plus : (t->t->t) ref = binary ( + )
let neg : (t->t) ref = unary ((-) 0)
let _ = Make.ring (Now 0) (Now 1) neg mult plus

let print_line x = print_string x; print_string "\n"

let _ =
  print_line (printStaged (!mult (Later (-1)) (Later 3)));
  print_line (printStaged (!mult (Now (-1)) (Later 3)));
  print_line (printStaged (!mult (Now (-1)) (Now 3)))
