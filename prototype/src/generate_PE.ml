(* File: Generate_PE.ml *) 
(* This files read ml expressions of the theories and generates the partial evaluator based on the staged type: "type 'a staged = Now of 'a | Later of 'a code" *) 

open Generate_ml_signature 

(* ------------------------------------------------------------- *) 
(* ---------------------- Helper Functions --------------------- *) 

(* replace all occurences of char1 in atr with char2 *) 
let rec replace_all str char1 char2 = 
  try 
   let i = String.index str char1 in 
   (String.sub str 0 i) ^ (String.make 1 char2) ^ (replace_all (String.sub str (i+1) ((String.length str) - i - 1)) char1 char2)
  with 
   Not_found -> str 

(* for the case "val hom : ('a, 'b)", we use this function to add the brackets and the star *) 
let fix_if_tuple str = 
  if (String.contains str ',') 
  then 
    "( " ^ (replace_all str ',' '*') ^ " )" 
  else str ^ "st" 


(* ------------------------------------------------------------- *) 
(* ------------------------- Input ----------------------------- *) 
let theories = (* The theories library *) 
    let file = Sys.argv.(1) in
    let expr = Library.read file  in
    let lib = Track.create_lib "top" expr in
    let lib = Checkthy.checklib lib in
    let lib = Flattener.expand_top lib in
    let lib = Reducer.reducer lib in 
    lib.theories (* Theories of the library: bindings StringMap *) 

(* ML Signatures of theories of the library. Type: "(string * (ml_comp StringMap * ml_comp StringMap)) StringMap" *) 
(* The string represents the name of the theory 
   The first ml_comp StringMap represents the type components of the ML signature 
   The second ml_comp StringMap represents the val components of the ML sginature *) 
let signatures = Util.StringMap.mapi expand_theory_sep theories 

(* ------------------------------------------------------------ *) 
(* ---------------- Type for the PE --------------------------- *) 
type ml_comp_PE = 
    | Type_Name of string 
    | Type_PE of (string * string) (* For the code line "type ust : u staged" *) 
    | Func_Ops_PE of ml_comp_PE list  
    | Func_Type_PE of string * ml_comp_PE * ml_comp_PE
    | Value_Type_PE of string * ml_comp_PE (* For the case "val e : u" *) 
    | Error_PE of string 

(* ------------------------------------------------------------ *) 
(* --------------- Generating the PE -------------------------- *) 

(* Input: ml_comp , Output: ml_comp_PE *) 
let one_type_PE one_type = match one_type with 
   | MLVal (type_name, Type_ID id) -> 
          if (id = "type") 
          then Type_PE ((type_name ^ "st") , (type_name ^ " staged"))
          else Type_PE (("(" ^ id ^ ") " ^ type_name ^ "st"), ("(" ^ id ^ ") " ^ type_name ^ " staged"))
   | _ -> Error_PE "Wrong Signature. "   

(* Input: ml_comp SM , Output: ml_comp_PE SM *) 
let type_part_PE type_part = 
    let scan_result = scan_thy_sig type_part in 
    if scan_result = "expand" then Util.StringMap.map one_type_PE type_part else (Util.StringMap.add "error" (Error_PE scan_result) (Util.StringMap.empty))

(* Input: ml_val_comp , Output: ml_comp_PE *) 
let rec one_val_PE_helper str one_val = match one_val with 
    | Type_ID s ->  Type_Name (if (s = "bool") then "bool" else ((String.lowercase s) ^ "st"))
    | Func_Operands ops_list -> Func_Ops_PE (one_val_PE_helper_H str ops_list) 
    | Func_Type (c1, c2) -> Func_Type_PE (str, one_val_PE_helper str c1, one_val_PE_helper str c2)
    | Error_Str str -> Error_PE str 
    | _ -> Error_PE "Error in Processing."

(* To handle the case of the list. I cannot use map because the function has another input other than the list *)
and one_val_PE_helper_H str val_list = match val_list with 
    | [] -> [] 
    | x :: xs -> one_val_PE_helper str x :: one_val_PE_helper_H str xs 

(* Input ml_comp ,  Output: ml_comp_PE *) 
let one_val_PE one_val = 
    match one_val with 
    | MLVal (str, comp) -> (match comp with 
        | Type_ID s -> Value_Type_PE (str, Type_Name  (if (s = "bool") then "bool" else ((fix_if_tuple (String.lowercase s)))))
        | _ -> one_val_PE_helper str comp )
    | MLComment com -> Error_PE com 

(* Input: ml_comp SM , Output: ml_comp_PE SM *) 
let val_part_PE val_part = 
    let scan_result = scan_thy_sig val_part in 
    if scan_result = "expand" then Util.StringMap.map one_val_PE val_part else (Util.StringMap.add "error" (Error_PE scan_result) (Util.StringMap.empty))

(* Input: Theory, Output: PE of the theory *) 
let one_thry_PE (thry_name , (part1, part2)) = 
    let part1_PE = type_part_PE part1 in 
    let part2_PE = val_part_PE part2 in 
    (thry_name , (part1_PE, part2_PE)) 

(* ------------------------------------------------------------ *) 
(* ----------------- Printing ML Signature Code --------------- *) 

(* Prints one line of the PE. 
   Input : ml_comp_PE , Output: String *) 
let rec print_one_comp_PE_helper comp_PE = match comp_PE with 
    | Type_Name str -> str 
    | Type_PE (str1, str2) -> "type " ^ str1 ^ " = " ^ str2 ^ "\n"
    | Func_Ops_PE code_list -> "( " ^ (String.concat " * " (List.map print_one_comp_PE_helper code_list)) ^ " )"
    | Func_Type_PE (str, code1, code2) -> "val " ^ str ^ " : " ^ (print_one_comp_PE_helper code1) ^ " -> " ^ (print_one_comp_PE_helper code2) ^ "\n"
    | Value_Type_PE (str, code) -> "val " ^ str ^ " : " ^ (print_one_comp_PE_helper code) ^ "\n" 
    | Error_PE str -> "(* " ^ str ^ "*)"

let print_one_comp_PE key comp_code bc = bc ^ (print_one_comp_PE_helper comp_code) 

(* Prints the signature of the type part 
   Input : (String, (ml_comp SM, ml_comp SM)) , Output: Buffer *) 
let print_type_part (thry_name , (type_part, val_part)) = 
     print_thy_sigH thry_name type_part (Buffer.create 100)

(* A SM containing all the signatures of the type part of the theories *) 
let all_type_parts_SM = Util.StringMap.map print_type_part signatures

(* Prints the theories with error messages *) 
let print_error_message (thry_name , (part1_code, part2_code)) buff = 
   let str1 = "module type " ^ thry_name ^ "PE = sig \n" in 
   if (Util.StringMap.mem "error" part1_code) 
   then (let (Error_PE str) = Util.StringMap.find "error" part1_code in 
         let new_buff = Buffer.add_string buff  (str1 ^ "(* " ^ str ^ " *) \nend \n (* ------------------------------------- *) \n")  in 
         buff)
   else (let (Error_PE str) = Util.StringMap.find "error" part2_code in 
         let new_buff = Buffer.add_string buff (str1 ^ "(* " ^ str ^ " *) \nend \n (* ------------------------------------- *) \n") in 
         buff)
(* Prints the PE of the signatures of theories with no errors *) 
let print_signature_PE (thry_name , (part1_code, part2_code)) buff = 
   let str1 = "module type " ^ thry_name ^ "PE = sig \n" in 
   let str2 = (Buffer.contents (Util.StringMap.find thry_name all_type_parts_SM)) in
   let str3 = (Util.StringMap.fold print_one_comp_PE part1_code "") in 
   let str4 = (Util.StringMap.fold print_one_comp_PE part2_code "") in 
   let new_buffer = Buffer.add_string buff (str1 ^ str2 ^ str3 ^ str4 ^ "end \n (* ------------------------------------- *) \n") in 
   buff 


(* Input: (ml_comp_PE SM , ml_comp_PE SM) , Output: Buffer *) 
let print_one_thry_PE key (thry_name , (part1_code, part2_code)) buff = 
   if ((Util.StringMap.mem "error" part1_code) || (Util.StringMap.mem "error" part2_code))
   then print_error_message (thry_name , (part1_code, part2_code)) buff 
   else print_signature_PE (thry_name , (part1_code, part2_code)) buff 

let print_theories_PE buff = 
    let theories_PE = Util.StringMap.map one_thry_PE signatures in 
    let new_buff = Buffer.add_string buff "type \'a staged = Now of \'a | Later of \'a code \n" in 
    Util.StringMap.fold print_one_thry_PE theories_PE buff


let() = 
   Printf.printf "%s" (Buffer.contents (print_theories_PE (Buffer.create 100)))


