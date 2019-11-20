
open Generate_ml_signature
open Generate_code
open Generate_PE

module SM = Util.StringMap

(* ------------------------------------------------------------- *) 
(* ------------------------- Functor --------------------------- *) 

(* Theory Signature Functor Types *) 

module type Thry_ML_Signature = sig (* One signature *) 
    type t = ml_signature_sep 
    val signature : t 
end 

module type Theories_ML_Signatures = sig (* SM of signatures *) 
    type t = ml_signature_sep SM.t 
    val sig_SM : t 
end 

(* Code Functor Types *) 

module type Thry_Code = sig (* One Code *) 
    type t = (string * (ml_comp_code SM.t  * ml_comp_code SM.t))
    val code : t 
    val print_code : Buffer.t 
end 

module type Theories_Codes = sig (* SM of Codes *) 
    type t = (string * (ml_comp_code SM.t  * ml_comp_code SM.t)) SM.t 
    val code_SM : t 
    val print_codes : Buffer.t 
end 

(* PE Functor Types *) 

module type Thry_PE = sig (* One PE *) 
    type t
    val pe : t 
    val print_PE : Buffer.t   
end 

module type Theories_PE = sig (* SM of PEs *) 
    type t 
    val pe_SM : t 
    val print_PEs : Buffer.t 
end


(* ------------------------------------------------------------- *) 
(* --------------  Functors From Signature To PE --------------- *) 

module Make_Thry_PE (Sig : Thry_ML_Signature) : Thry_PE = struct (* One Theory *) 
    type t = (string * (ml_comp_PE SM.t * ml_comp_PE SM.t))
    let pe = one_thry_PE Sig.signature
    let print_PE = print_one_thry_PE "" pe (Buffer.create 100) 
end 

module Make_Theories_PE (Sigs : Theories_ML_Signatures) : Theories_PE = struct (* SM of Theories *) 
    type t = (string * (ml_comp_PE SM.t * ml_comp_PE SM.t)) SM.t
    let pe_SM = Util.StringMap.map one_thry_PE Sigs.sig_SM
    let print_PEs = print_theories_PE (Buffer.create 100) 
end 

(* Run them *) 

module Random_Thry_Sig : Thry_ML_Signature = struct 
    type t = ml_signature_sep
    let (key, thry_sig) = Util.StringMap.choose signatures 
    let signature = thry_sig 
end 

module Random_Thry_PE = Make_Thry_PE(Random_Thry_Sig) (* To get one theory PE *) 

module Theories_Sig : Theories_ML_Signatures = struct 
    type t = ml_signature_sep Util.StringMap.t     
    let sig_SM = signatures 
end 

module Actual_Theories_PE = Make_Theories_PE(Theories_Sig) (* To get the PE of theories SM *) 

(* ------------------------------------------------------------- *) 
(* --------------  Functors From Signature To Code ------------- *) 

module Make_Thry_Code (Sig : Thry_ML_Signature) : Thry_Code = struct (* One Theory *) 
    type t = (string * (ml_comp_code SM.t * ml_comp_code SM.t))
    let code = one_thry_code Sig.signature
    let print_code = print_one_thry_code "" code (Buffer.create 100) 
end 

module Make_Theories_Codes (Sigs : Theories_ML_Signatures) : Theories_Codes = struct (* SM of Theories *) 
    type t = (string * (ml_comp_code SM.t * ml_comp_code SM.t)) SM.t
    let code_SM = Util.StringMap.map one_thry_code Sigs.sig_SM
    let print_codes = print_theories_code 
end 

(* Run them *) 

module Random_Thry_Code = Make_Thry_Code(Random_Thry_Sig) (* To get one theory Code *) 

module Actual_Theories_Codes = Make_Theories_Codes(Theories_Sig) (* To get the Code of theories SM *) 


(* ------------------------------------------------------------- *) 
(* --------------  Functors From Code To PE -------------------- *) 

module Convert_Code_To_PE = struct 
    let rec fix_comp code_comp = match code_comp with 
      | Type_Name_Code str -> Type_Name ((String.sub str 0 ((String.length str) - 1)) ^ "st")
      | Type_Code (str1, str2) -> Type_PE (((String.sub str1 0 ((String.length str1) - 1)) ^ "st") , ((String.sub str2 0 ((String.length str2) - 4)) ^ " staged"))
      | Func_Ops_Code code_list -> Func_Ops_PE (List.map fix_comp code_list)
      | Func_Type_Code (str, code1, code2) -> Func_Type_PE (str, fix_comp code1, fix_comp code2)
      | Value_Type_Code (str, code) -> Value_Type_PE (str, fix_comp code) 
      | Error_Code str -> Error_PE str  
    let fix_thry_code (thry_name, (code_comp_SM_1, code_comp_SM_2)) = (thry_name, (SM.map fix_comp code_comp_SM_1, SM.map fix_comp code_comp_SM_2))    
end 

module Make_Thry_PE_From_Code (Code : Thry_Code) : Thry_PE = struct 
    type t = (string * (ml_comp_PE SM.t * ml_comp_PE SM.t))
    (* function from ml_comp_code to ml_comp_PE *) 
    let (thry_name , (code1, code2)) = Code.code 
    let pe = (thry_name, (SM.map Convert_Code_To_PE.fix_comp code1, SM.map Convert_Code_To_PE.fix_comp code2))  
    let print_PE = print_one_thry_PE "" pe (Buffer.create 100) 
end 

module Make_Theories_PE_From_Code (Codes : Theories_Codes) : Theories_PE = struct
    type t = (string * (ml_comp_PE SM.t * ml_comp_PE SM.t)) SM.t
    let pe_SM = Util.StringMap.map  Convert_Code_To_PE.fix_thry_code Codes.code_SM
    let print_PEs = print_theories_PE (Buffer.create 100) 
end
(* Run them *) 
(*
module Random_Thry_Code : Thry_Code = struct (* For one theory *) 
    type t = (string * (ml_comp_code SM.t  * ml_comp_code SM.t))
    let (s, c) = SM.choose signatures
    let code = one_thry_code c
end 
*)
module Random_Thry_PE_From_Code = Make_Thry_PE_From_Code(Random_Thry_Code)

(*
module Theories_Code : Theories_Codes = struct  (* To run for a SM *) 
    type t = (string * (ml_comp_code SM.t  * ml_comp_code SM.t)) SM.t     
    let code_SM = Util.StringMap.map one_thry_code signatures 
end 
*) 
module Actual_Theories_PE_From_Code = Make_Theories_PE_From_Code(Actual_Theories_Codes) 



(* ------------------------ Main Function ------------------- *)
let() = 
 (*   let buff = (Actual_Theories_PE.print_PEs) in (* From Signatures SM to PEs SM *) 
    let buff = (Actual_Theories_Codes.print_codes) in (* From Signatures SM to Code SM *) *) 
    let buff = (Actual_Theories_PE_From_Code.print_PEs) in  (* From Code SM to PE SM *) 
    Printf.printf "%s" (Buffer.contents buff) 




