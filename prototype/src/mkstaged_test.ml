open Mkstaged_output

let rec printStaged = function
  | Now x -> "(Now "^(string_of_int x)^")"
  | PartialUnary (f,x) -> "P("^(printStaged x)^")"
  | PartialBinary (f,x,y) -> "P("^(printStaged x)^","^(printStaged y)^")"
  | Later x -> "(Later "^(string_of_int x)^")"

(* Note spec's second type parameter will change when Later is code. *)
type t = (int, int) staged

let mult : (t->t->t) ref = binary ( * )
let plus : (t->t->t) ref = binary ( + )
let neg : (t->t) ref = unary ((-) 0)
let _ = Make.defineCommutativeRing mult plus neg (Now 0) (Now 1)   

let print_line x = print_string x; print_string "\n"

let _ =
  print_line (printStaged (!plus (Later (-3)) (Later 3)));
  print_line (printStaged (!mult (!neg (Later (1))) (Later 3)));
  print_line (printStaged (!plus (!neg (Later (3))) (Later 3)));
  print_line (printStaged (!plus (Now (-3)) (Now 3)));
  print_line (printStaged (!neg (!neg (Later 3))))
