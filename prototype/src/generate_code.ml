(* File: Generate_code_sig.ml *) 
(* This files read ml expressions of the theories and generates the signature of the code version *) 

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

(* for the case "val hom : ('a, 'b)", we use this function to add the brackets *) 
let fix_if_tuple str = 
  if (String.contains str ',') 
  then 
    "( " ^ (replace_all str ',' '*') ^ " )" 
  else str ^ "c" 


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
(* ---------------- Type for ML Signature Code ---------------- *) 
type ml_comp_code = 
    | Type_Name_Code of string 
    | Type_Code of (string * string) (* For the code line "type uc : u code" *) 
    | Func_Ops_Code of ml_comp_code list  
    | Func_Type_Code of string * ml_comp_code * ml_comp_code 
    | Value_Type_Code of string * ml_comp_code (* For the case "val e : u" *) 
    | Error_Code of string 

(* ------------------------------------------------------------ *) 
(* --------------- Generating ML Signature Code --------------- *) 

(* Input: ml_comp , Output: ml_comp_code *) 
let one_type_code one_type = match one_type with 
   | MLVal (type_name, Type_ID id) -> if (id = "type") then Type_Code ((type_name ^ "c") , (type_name ^ " code"))
                                      else Type_Code (("(" ^ id ^ ") " ^ type_name ^ "c"), ("(" ^ id ^ ") " ^ type_name ^ " code"))
   | _ -> Error_Code "Wrong Signature. "   

(* Input: ml_comp SM , Output: ml_comp_code SM *) 
let type_part_code type_part = 
    let scan_result = scan_thy_sig type_part in 
    if scan_result = "expand" then Util.StringMap.map one_type_code type_part else (Util.StringMap.add "error" (Error_Code scan_result) (Util.StringMap.empty))

(* Input: ml_val_comp , Output: ml_comp_code *) 
let rec one_val_code_helper str one_val = match one_val with 
    | Type_ID s ->  Type_Name_Code (if (s = "bool") then "bool" else ((String.lowercase s) ^ "c"))
    | Func_Operands ops_list -> Func_Ops_Code (one_val_code_helper_H str ops_list) 
    | Func_Type (c1, c2) -> Func_Type_Code (str, one_val_code_helper str c1, one_val_code_helper str c2)
    | Error_Str str -> Error_Code str 
    | _ -> Error_Code "Error in Processing."

(* To handle the case of the list. I cannot use map because the function has another input other than the list *)
and one_val_code_helper_H str val_list = match val_list with 
    | [] -> [] 
    | x :: xs -> one_val_code_helper str x :: one_val_code_helper_H str xs 

(* Input ml_comp ,  Output: ml_comp_code *) 
let one_val_code one_val = 
    match one_val with 
    | MLVal (str, comp) -> (match comp with 
        | Type_ID s -> Value_Type_Code (str, Type_Name_Code  (if (s = "bool") then "bool" else ((fix_if_tuple (String.lowercase s)))))
        | _ -> one_val_code_helper str comp )
    | MLComment com -> Error_Code com 

(* Input: ml_comp SM , Output: ml_comp_code SM *) 
let val_part_code val_part = 
    let scan_result = scan_thy_sig val_part in 
    if scan_result = "expand" then Util.StringMap.map one_val_code val_part else (Util.StringMap.add "error" (Error_Code scan_result) (Util.StringMap.empty))

(* Input: Theory, Output: Code of the theory *) 
let one_thry_code (thry_name , (part1, part2)) = 
    let part1_code = type_part_code part1 in 
    let part2_code = val_part_code part2 in 
    (thry_name , (part1_code, part2_code)) 

(* ------------------------------------------------------------ *) 
(* ----------------- Printing ML Signature Code --------------- *) 

(* Prints one line of the signature code. 
   Input : ml_comp code , Output: String *) 
let rec print_one_comp_code_helper comp_code = match comp_code with 
    | Type_Name_Code str -> str 
    | Type_Code (str1, str2) -> "type " ^ str1 ^ " = " ^ str2 ^ "\n"
    | Func_Ops_Code code_list -> "( " ^ (String.concat " * " (List.map print_one_comp_code_helper code_list)) ^ " )"
    | Func_Type_Code (str, code1, code2) -> "val " ^ str ^ " : " ^ (print_one_comp_code_helper code1) ^ " -> " ^ (print_one_comp_code_helper code2) ^ "\n"
    | Value_Type_Code (str, code) -> "val " ^ str ^ " : " ^ (print_one_comp_code_helper code) ^ "\n" 
    | Error_Code str -> "(* " ^ str ^ "*)"

let print_one_comp_code key comp_code bc = bc ^ (print_one_comp_code_helper comp_code) 

(* Prints the signature of the type part 
   Input : (String, (ml_comp SM, ml_comp SM)) , Output: Buffer *) 
let print_type_part (thry_name , (type_part, val_part)) = 
     print_thy_sigH thry_name type_part (Buffer.create 100)

(* A SM containing all the signatures of the type part of the theories *) 
let all_type_parts_SM = Util.StringMap.map print_type_part signatures

(* Prints the theories with error messages *) 
let print_error_message (thry_name , (part1_code, part2_code)) buff = 
   let str1 = "module type " ^ thry_name ^ "Code = sig \n" in 
   if (Util.StringMap.mem "error" part1_code) 
   then (let (Error_Code str) = Util.StringMap.find "error" part1_code in 
         let new_buff = Buffer.add_string buff  (str1 ^ "(* " ^ str ^ " *) \nend \n (* ------------------------------------- *) \n")  in 
         buff)
   else (let (Error_Code str) = Util.StringMap.find "error" part2_code in 
         let new_buff = Buffer.add_string buff (str1 ^ "(* " ^ str ^ " *) \nend \n (* ------------------------------------- *) \n") in 
         buff)
(* Prints the code of the signatures of theories with no errors *) 
let print_signature_code (thry_name , (part1_code, part2_code)) buff = 
   let str1 = "module type " ^ thry_name ^ "Code = sig \n" in 
   let str2 = (Buffer.contents (Util.StringMap.find thry_name all_type_parts_SM)) in
   let str3 = (Util.StringMap.fold print_one_comp_code part1_code "") in 
   let str4 = (Util.StringMap.fold print_one_comp_code part2_code "") in 
   let new_buffer = Buffer.add_string buff (str1 ^ str2 ^ str3 ^ str4 ^ "end \n (* ------------------------------------- *) \n") in 
   buff 


(* Input: (ml_comp_code SM , ml_comp_code SM) , Output: String *) 
let print_one_thry_code key (thry_name , (part1_code, part2_code)) buff = 
   if ((Util.StringMap.mem "error" part1_code) || (Util.StringMap.mem "error" part2_code))
   then print_error_message (thry_name , (part1_code, part2_code)) buff 
   else print_signature_code (thry_name , (part1_code, part2_code)) buff 

(*
let print_one_buffer_content key buff bc = 
    let header = "module type " ^ key ^ " = sig \n" in 
    let content = (Buffer.contents buff) in 
    let tail = "\n end \n (* --------------------------------- *)" in 
    bc ^ header ^ content ^ tail 
*)
let print_theories_code = 
    let theories_code = Util.StringMap.map one_thry_code signatures in 
    Util.StringMap.fold print_one_thry_code theories_code (Buffer.create 100)

let() = 
   Printf.printf "%s" (Buffer.contents (print_theories_code))

