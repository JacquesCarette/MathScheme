(* For failures in computing depencies *)
exception Dependency of string

(* For various kinds of things being multiply defined *)
exception MultiplyDefined of string * string * string

(* Property called with wrong # of arguments *)
exception PropLength of int * int * string

(* Searching for something failed *)
exception Searching of string * string * string

(* When looking into an empty library *)
exception EmptyArrows of string

(* Looking for a name for something which doesn't have one *)
exception Unnamed of string
