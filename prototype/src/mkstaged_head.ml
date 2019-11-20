type ('a,'b) staged = 
     Now of 'a 
   | PartialUnary of (('a,'b) staged->('a,'b) staged) ref * ('a,'b) staged 
   | PartialBinary of (('a,'b) staged->('a,'b) staged->('a,'b) staged) ref * ('a,'b) staged * ('a,'b) staged 
   | Later of 'a

module StringSet = Set.Make(String)

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

