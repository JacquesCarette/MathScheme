
(* File: Generate_expr_lang 
   Generates the language of expressions of single-sorted theories without type constructors *) 
open Syntax 
open Generate_ml_signature

(* ToDo: 
1. Get the list of theory signatures for those theories without errors 
2. Get the list having the type first 
*) 

(* --------------------------------------------------------------------------- *) 
(* -------------------------- Helper Functions ------------------------------ *) 

let rec extract_scnd pairs_list = match pairs_list with 
    | [] -> [] 
    | (fst, snd) :: lst -> snd :: (extract_scnd lst) 

let concat_strings str1 str2 = str1 ^ str2 

(* ---------------------------------------------------------------------------- *) 
(* ------------------------- Getting the input ---------------------------------*) 

let theories = (* The theories library *) 
    let file = Sys.argv.(1) in
    let expr = Library.read file  in
    let lib = Track.create_lib "top" expr in
    let lib = Checkthy.checklib lib in
    let lib = Flattener.expand_top lib in
    let lib = Reducer.reducer lib in 
    lib.theories (* Theories of the library: bindings StringMap *) 

(* ML Signatures of theories of the library. Type: "(string * ml_comp StringMap) StringMap" *) 
let signatures = Util.StringMap.mapi expand_theory theories 

let lang_list = [] 

(* --------------------------------------------------------------------------- *) 
(* ----------------------- The type for the language ------------------------- *) 

type thry_name_type = {mutable name : string}
type renaming_type = {mutable new_names : string Util.StringMap.t} 

type component = 
    | Symbol of string 
    | Operands of component list 
    | Operation  of string * component * component 
    | None

(* The string list is a list of non-terminal symbols (defined by keyword type in the signature) 
   The component StringMap is a mapping of the non-terminal symbol with its components (terminals and operations) *) 
type lang = string list * (string * component) list  


(* --------------------------------------------------------------------------- *) 
(* ---------------------- Extract the language ------------------------------- *) 

let curr_thry_name = {name = ""} 

(* The input is of type ml_comp | The output is of type string list *) 
let find_type_IDs mc = match mc with 
    | MLComment _ -> []
    | MLVal (_, Type_ID str) -> if str = "type" then [] else [str] 
    | MLVal (_, _) -> [] 

(* The input is ml_comp StringMap of a signature 
   The output is a string list having the non-terminals of the signature *) 
let find_non_terminals sign =
   let signSM = (Util.StringMap.map find_type_IDs sign) in 
   let bindings_list = Util.StringMap.bindings signSM in 
   let l = extract_scnd bindings_list in 
   List.flatten l 

(* Input: String ml_val_comp | Output : component *) 
let rec generateFuncExpr func_name mvc = match mvc with 
    | Type_ID symbol_name -> Symbol (curr_thry_name.name ^ "Lang")
    | Func_Operands operands_list -> Operands (generateFuncExpr_H func_name operands_list) 
    | Func_Type (mvc1, mvc2) -> Operation (func_name, (generateFuncExpr func_name mvc1), (generateFuncExpr func_name mvc2)) 
    | Error_Str str -> None

and generateFuncExpr_H func_name mvc_list = match mvc_list with 
    | [] -> [] 
    | x :: xs -> (generateFuncExpr func_name x) :: (generateFuncExpr_H func_name xs) 

let generateExprType mc = match mc with 
    | MLVal (symbol_name, Type_ID str2) -> if ((find_type_IDs (MLVal (symbol_name, Type_ID str2))) <> []) then (Symbol symbol_name) else None
    | MLVal (func_name, mvc) -> generateFuncExpr func_name mvc
    | _ -> None

(* Input: ml_comp StringMap representing the theory | Output: component SM *) 
let generate_thry_lang_H thry = 
   let non_term_list = find_non_terminals thry in 
   if (List.length non_term_list <> 1) 
   then Util.StringMap.empty 
   else Util.StringMap.map generateExprType thry 


(* Input: (string, ml_comp SM) 
   Output: (string, component SM) *) 
let generate_thry_lang (thry_name, thry) = 
  let flag = Generate_ml_signature.scan_thy_sig thry in  
  if (flag <> "expand") 
  then (thry_name , Util.StringMap.empty) 
  else 
   begin
    curr_thry_name.name <- ((String.lowercase (String.sub thry_name 0 1)) ^ (String.sub thry_name 1 ((String.length thry_name)- 1))) ; 
    (thry_name , (generate_thry_lang_H thry)) ; 
   end 

(* --------------------------------------------------------------------------- *) 
(* ------------------------- Renaming Convention ----------------------------- *) 

let file = "renaming_conv.txt"

let renames = {new_names = Util.StringMap.empty}

let rec read_H m ic = 
  try
    let line = input_line ic in  (* read line from in_channel and discard \n *)
    let space = String.rindex line ' '  in 
    let m' = Util.StringMap.add (String.sub line 0 space) (String.sub line (space + 1) ((String.length line) - space - 1)) m in
    read_H m' ic
  with 
     e -> begin close_in ic ; m end 

let read = 
    let ic = open_in file in 
    let l = read_H (Util.StringMap.empty) ic in 
    l 

(* --------------------------------------------------------------------------- *) 
(* ----------------------- Printing the language ----------------------------- *) 

let ren = read 

let rec print_comp_H2 comp = 
  match comp with 
    | Symbol str -> str
    | Operands comp_list -> "( " ^ String.concat " * " (List.map print_comp_H2 comp_list) ^ " )"
    | Operation (str, comp1, comp2) -> (if Util.StringMap.mem str ren then Util.StringMap.find str ren else ((String.uppercase (String.sub str 0 1)) ^ (String.sub str 1 ((String.length str) - 1)))) ^ " of " ^ (print_comp_H2 comp1) 
    | None -> "" 

let print_comp_H comp = 
  match comp with 
    | Symbol str -> if Util.StringMap.mem str ren then Util.StringMap.find str ren else ((String.uppercase (String.sub str 0 1)) ^ (String.sub str 1 ((String.length str) - 1)))
    | _ -> print_comp_H2 comp 

let print_comp comp = 
    let p = (print_comp_H comp) in 
    if (p <> "") then (" | " ^ p ^ "\n") else ""

(* Input: String , (string, component SM) Buffer | Output: Buffer *) 
let print_thy_language key (thry_name, thry_lang) buff = 
 if (thry_lang <> Util.StringMap.empty) 
 then 
   (let header = "type " ^ ((String.lowercase (String.sub thry_name 0 1)) ^ (String.sub thry_name 1 ((String.length thry_name)- 1))) ^ "Lang = \n" in (* string *) 
   let variants = Util.StringMap.map  print_comp thry_lang (* string SM *) in 
   let variants_list = extract_scnd (Util.StringMap.bindings variants) in 
   let final_str = List.fold_left concat_strings header variants_list ^ "\n(* ----------------------------------------------- *) \n" in
   let new_buff = Buffer.add_string buff final_str  in 
   buff)   
 else buff 

(* Input: (string, ml_comp SM) 
   Output: string *) 
let print_thy_language_2 key (thry_name, thry_sig) buff = 
  let (name , thry_lang) = generate_thry_lang (thry_name, thry_sig) in (* component SM *) 
  print_thy_language key (thry_name, thry_lang) buff 
(*
let () = 
   let buff = Util.StringMap.fold print_thy_language_2 signatures (Buffer.create 100) in 
   Printf.printf "%s" (Buffer.contents buff) 
*)
 


