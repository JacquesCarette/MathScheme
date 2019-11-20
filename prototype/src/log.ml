(* Handle logging *)

let verbose = ref false  (* spit out what we are doing? *)
let log s = if !verbose then Printf.eprintf "%s" s; flush stderr
