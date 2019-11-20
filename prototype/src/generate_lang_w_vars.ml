(* file: Thry_lang_w_vars.ml *) 
(* This file the languages of theories and generates The language of the theory parameterized with variables *) 

open Generate_ml_signature
open Generate_language

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

(* signatures of type : (string, ml_comp SM) *) 
let signatures = Util.StringMap.mapi expand_theory theories

(* languages of type : (string , component SM) SM *) 
let languages = Util.StringMap.map generate_thry_lang signatures 


(* ------------------------------------------------------------ *) 
(* ----------------- Generating the language with Vars -------- *) 

(* Input : (string , component SM) 
   Output: (string , component SM) with the "Var V.t" part added *) 
let add_var_option (thry_name , thry_lang) = 
  if (thry_lang <> Util.StringMap.empty) (* The theory does not have an error *) 
  then   
    let var_option = (Operation ("Var",(Symbol "V.t"),(Symbol ""))) in 
    (thry_name , (Util.StringMap.add "Var" var_option thry_lang)) 
  else (thry_name , Util.StringMap.empty) 

(* Input : None | Output : (string, component SM) SM *) 
let updated_languages = Util.StringMap.map add_var_option languages 

(* ------------------------------------------------------------ *) 
(* ----------------- Printing the language with Vars ---------- *) 

let header = 
    let s1 = "module type Var = sig \n type t \nend \n\n" in 
    let s2 = s1 ^ "module Generate_Langs_W_Vars (V : Var) = struct \n\n" in
    s2 

(* Output : Buffer *) 
let languages_buff = Util.StringMap.fold print_thy_language updated_languages (Buffer.create 100) 

let end_line = "\n\n end \n" 

let () = 
    begin 
    Printf.printf "%s" header ; 
    Printf.printf "%s" (Buffer.contents languages_buff)  ;  
    Printf.printf "%s" end_line ;
    end 
