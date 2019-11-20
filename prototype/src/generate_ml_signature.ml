(* File: generate.ml *)
(* This file reads expanded theories resulting from reify_expanded_library function and generate ML expressions for them *) 

open Syntax
open Bindings 
(* ------------------------------------------------------------- *) 
(* ---------------------- Helper Functions --------------------- *) 
let alphabet = ["'a";"'b";"'c";"'d";"'e";"'f";"'g";"'h";"'i";"'j";"'k";"'l";"'m";"'n";"'o";"'p";"'q";"'r";"'s";"'t";"'u";"'v";"'w";"'x";"'y";"'z"]
let numbers = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"]
let numbers_ext = ["0'"; "1'"; "2'"; "3'"; "4'"; "5'"; "6'"; "7'"; "8'"; "9'"]
let sp_sym = ["/\\";"\\/"; "\\"; "#"]
let is_num str =  if List.mem str numbers then "_" ^ str else if List.mem str numbers_ext then "_" ^ str else str
let is_and_or str = 
    if str = "/\\" then "and_" 
    else if str = "\\/" then  "or_" 
    else if str = "\\" then "diff_" 
    else if str = "#" then "@"
    else str
let rec sub_list len l = 
    if len = 0 then [] else (List.hd l) :: (sub_list (len-1) (List.tl l))
(* Partition typ_def StringMap to have the type fields first then the value fields *) 
let criteria key td = 
    match td.kind with 
    | Type -> true 
    | TArrow (_, Type) -> true 
    | _ -> false 
let partition td_SM = Util.StringMap.partition criteria td_SM
(* Functions for pretty printing *) 
let fix_quot str = 
    let len = String.length str in 
    let substring = (String.sub str 0 (len-1)) in 
    if String.get str (len - 1) == '\'' then (if Syntax.is_oper substring then substring ^ "~" else substring ^ "\'") else str 
let fix_string str = 
   let len = String.length str in 
   let s = fix_quot (is_and_or str) in 
   if (List.mem str numbers || List.mem str numbers_ext) 
   then  "_" ^ str
   else if (Syntax.is_oper s) then "( " ^ str ^ " )" else s

(* ------------------------------------------------------------- *) 
(* ------------------------- Input ----------------------------- *) 

(* reades the input file and generates the library *)
(* The library type (bindings) includes:
   - lname : String
   - arrows : arrow SM.t
   - theories : bindings SM.t 
   - subst : subst list SM.t *)  
let library = 
    let file = Sys.argv.(1) in
    let expr = Library.read file  in
    let lib = Track.create_lib "top" expr in
    let lib = Checkthy.checklib lib in
    let lib = Flattener.expand_top lib in
    Reducer.reducer lib

(* ------------------------------------------------------------- *) 
(* ----------------- Type of ML Signature ---------------------- *) 

type ml_val_comp = 
   | Type_ID of string 
   | Func_Operands of ml_val_comp list
   | Func_Type of ml_val_comp * ml_val_comp 
   | Error_Str of string

(* The ML Signature Type *) 
and ml_comp = 
    | MLVal of string * ml_val_comp  (* identifier * type_name *) 
    | MLComment of string (* Comment on cases that are not handled *)   
(* String or tuple of strings or list of strings representing the function signature *) 

(* The signature of the theory having its name and a StringMap of the ml_comp *) 
and ml_signature = string * ml_comp Util.StringMap.t

and ml_signature_sep = (string * (ml_comp Util.StringMap.t * ml_comp Util.StringMap.t))

(* Type to describe if a theory can be expanded or not because any of the fields are non expandable *) 
type check = 
    | Expand 
    | Error of string 

(* ------------------------------------------------------------ *) 
(* ----------------- Generating ML Signature ------------------ *) 

(* A function that scans a type component and returns a check *) 
let rec scan_type_comp tc = match tc with 
    | Type -> Expand
    | TId id -> Expand 
    | TProd tc_list -> check_tc_list tc_list
    | TArrow (tc1, tc2) -> let tc1_scan = scan_type_comp tc1 in let tc2_scan = scan_type_comp tc2 in if tc1_scan <> Expand then  tc1_scan else if (tc2_scan <> Expand) then tc2_scan else Expand 
    | TPredicate tc1 -> scan_type_comp tc1
    | TInduct (id, field_sig_list) -> Error "Future Work" 
    | TRecord field_sig_list -> Error "Future Work. " 
    | TApp (tc1, tc2) -> Error  "Cannot process theories having TApp. "
    | TPower tc1 -> Error "Cannot process theories with power-set types TPower. " 
    | TDepId (str, tc1) -> Error "Cannot process theories with dependent types TDepId. "
    | TLift exp -> Error "Cannot process theories with expressions lifted as types TTheory. " 
    | TTheory str -> Error  "Cannot process theories reflected as inductive type TTheory. "
    | TTypeFromTheory str -> Error "Cannot process theories deriving a type from a theory TTypeFromTheory. "
    | TProof exp -> Error "Cannot process theories have proof types TProof. "
    | TBinder (varsp, tc1) -> Error "Cannot process theories with type-level lambda TBinder."

(* works on TProd tc_list *) 
and check_tc_list tc_list = 
  try 
    let member = (List.find (function | Error _ -> true | _ -> false) (List.map scan_type_comp tc_list)) 
    in (if member <> Expand then member  else Expand) 
  with 
    Not_found -> Expand

(* Scans the theory to decide if any of the fields cannot be expandable 
   Input: ml_comp StringMap (signature of one expanded theory) 
   Output: string (expand or the error message) *) 
let scan_thy_sig ml_comp_SM = 
  try
   let ml_comp_list = Util.StringMap.bindings ml_comp_SM in 
   let comment = List.find (function | (_, MLComment _) -> true | _ -> false) ml_comp_list in 
   match comment with 
   | (_, MLComment x) -> x 
  with 
    Not_found -> "expand" 

(* returns a list of strings *) 
let rec expand_type_comp tc = match tc with 
    | Type -> Type_ID "type"
    | TId id -> Type_ID id  
    | TProd tc_list -> Func_Operands (List.map expand_type_comp tc_list)
    | TArrow (tc1, tc2) -> expand_TArrow tc1 tc2 
    | TPredicate tc1 -> Func_Type ((expand_type_comp tc1), Type_ID "bool")
    | TInduct (id, field_sig_list) -> Error_Str "Future Work. " 
    | TRecord field_sig_list -> Error_Str "Future Work. " 
    | TApp (tc1, tc2) -> Error_Str "FailureTApp"
    | TPower tc1 -> Error_Str "FailureTPower"
    | TDepId (str, tc1) -> Error_Str "FailureTDepId"
    | TLift exp -> Error_Str "FailureTList" 
    | TTheory str -> Error_Str "FailureTTheory"
    | TTypeFromTheory str -> Error_Str "FailureTTypeFromTheory"
    | TProof exp -> Error_Str "FailureTProof" 
    | TBinder (varsp, tc1) -> Error_Str "FailureTBinder "

(* checks the case of type constructor when the normal output would be "ded : u -> type", but the desired one is "type 'a ded" *) 
and expand_TArrow tc1 tc2 = 
   let exp_tc2 = expand_type_comp tc2 in 
   if exp_tc2 <> Type_ID "type"
   then Func_Type ((expand_type_comp tc1) , (expand_type_comp tc2))
   else match tc1 with 
    | TId _ -> Type_ID "'a"
    | TProd tc_list -> Type_ID (String.concat " , " (sub_list (List.length tc_list) alphabet))

let expand_typ_decl_H key td =  
   let kind_expanded = expand_type_comp td.kind in 
   let symbol_defn = td.defn in 
   match symbol_defn with 
   | NoDefn -> MLVal ((String.lowercase (is_num (fix_string key))), kind_expanded)
   | Manifest n -> MLVal ((String.lowercase (is_num (fix_string key))), kind_expanded)
   | SubType _ ->  MLComment "Cannot process theories with subtypes."
(* (String.lowercase (is_num (fix_string key))) *) 

(* Input is a key and a symbol of type typ_decl, Output is ml_comp *) 
let expand_typ_decl key td = 
  let symbol_defn = td.defn in 
  match symbol_defn with 
   | SubType _ ->  MLComment "Cannot process theories with subtypes."
   | _ -> 
  let scan_result = scan_type_comp td.kind in (* scan to check if any of the fields cannot be expanded *) 
  match scan_result with 
   | Error str -> MLComment str 
   | Expand -> expand_typ_decl_H key td
  
(* ---- Working on the theories.symbols ---- *) 
(* Symbols of a theory has the type "typ_decl Util.StringMap.t" *)
(* The function returns a StringMap of ml_comp *) 
let expand_symbols thy_symbols = 
   Util.StringMap.mapi expand_typ_decl thy_symbols

let expand_theory key thry = (key, expand_symbols thry.symbols)

let expand_theory_sep key thry = 
    let (part1, part2) = partition (thry.symbols) in 
    (key, (expand_symbols part1, expand_symbols part2))

(* ------------------------------------------------------------ *) 
(* -------------- Printing the Signature ---------------------- *) 

(* ------------------------------------------- *) 
(* Printing the Signatures *) 

let rec from_ml_val_comp_to_string mvc = match mvc with 
    | Type_ID s -> s 
    | Func_Operands mvc_list -> "( " ^ (String.concat " * " (List.map from_ml_val_comp_to_string mvc_list)) ^ " )" 
    | Func_Type (mvc1, mvc2) -> (from_ml_val_comp_to_string mvc1) ^ " -> " ^ (from_ml_val_comp_to_string mvc2) 
    | Error_Str err -> err 

let print_ML_Val s1 ss2 bc = 
    let s2 = from_ml_val_comp_to_string ss2 in 
    if (s2 = "type") 
    then (bc ^ "type " ^ (String.lowercase s1) ^ "\n") 
    else if (String.get s2 0 = '\'') then (bc ^ "type (" ^ s2 ^ ") " ^ s1 ^ "\n")
    else (bc ^ "val " ^ (String.lowercase (is_num (fix_string s1))) ^ " : " ^ (String.lowercase s2) ^ "\n")

let print_ML_Comp key mlcomp bc = match mlcomp with 
    | MLVal (s1, s2) -> print_ML_Val s1 s2 bc 
    | MLComment str -> bc ^ str ^ "\n"

(* Print the fields of the theory signature 
   Input: key, ml_comp StringMap (expanded symbols), buffer 
   Output: Buffer  *) 
let print_thy_sigH key exp_sym buff = 
   let one_thy_str = Util.StringMap.fold print_ML_Comp exp_sym "" in 
   let new_buff = Buffer.add_string buff one_thy_str in 
   buff 

(* Print the error message scan *) 
let print_thy_sigH2 key scan buff = 
    let new_buff = Buffer.add_string buff ( "(* " ^ scan ^ " *)\n")  in 
    buff

let print_end_line buff = 
   let new_buff = Buffer.add_string buff "end \n(* --------------------------- *)\n" in 
   buff 

let print_type_sig key type_part buff = 
   let exp_sym = expand_symbols type_part in 
   let scan = scan_thy_sig exp_sym in 
   if scan <> "expand" then print_thy_sigH2 key scan buff else print_thy_sigH key exp_sym buff 

(* Prints the signature of one theory
   Input: key, bindings StringMap, Buffer
   Output: Buffer  *) 
let print_thy_sig key one_thy buff = 
   let (part1, part2) = partition (one_thy.symbols) in (* Partition to be able to print the type fields before the val fields *)
   let (exp_sym1, exp_sym2) = (expand_symbols part1, expand_symbols part2) in  (* expands every part independently *) 
   let new_buff = Buffer.add_string buff  ("module type " ^ key ^ " = sig \n") in (* add the first line of the signature to the library *) 
   let scan1 = scan_thy_sig exp_sym1 in 
   let scan2 = scan_thy_sig exp_sym2 in (* scan to check if a signature for the theory can be generated or not *) 
   if scan1 <> "expand" then  print_end_line (print_thy_sigH2 key scan1 buff) else if scan2 = "expand" then print_end_line (print_thy_sigH key exp_sym2 (print_thy_sigH key exp_sym1 buff)) else print_end_line (print_thy_sigH2 key scan2 buff) 
   (*Printing by sending the buffers of every step as input to the other step *) 
   
(* Main Function *) 

let() = 
  let library_signatures_buffer = Util.StringMap.fold print_thy_sig library.theories (Buffer.create 100) in 
  Printf.printf "%s" (Buffer.contents (library_signatures_buffer))

(* ------------------------------------------- *) 



