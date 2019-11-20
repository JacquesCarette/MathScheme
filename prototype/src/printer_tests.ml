open Syntax
open Printers

module C = Configuration.ASCII (* <- Change your configuration here *)
module O = Options.StdOpt (* <- Change your options here*)

module Test = Make(C)(O)(struct let f = Format.std_formatter end);;

(* Declaration of Peano Arithmetic mechanics *)

let peano_name = ThyName "Peano_Arithmetic"

(* Concepts *)
let nats = TBase ("N", {kind = Type; defn = (Manifest Type)});;
let zero = TBase ("0", {kind = TId "N"; defn = NoDefn});;
let suc = TBase("suc", {kind = TArrow (TId "N", TId "N"); defn = NoDefn});;
let mul = TBase("*", {kind = TArrow (TId "N", TArrow(TId "N", TId "N")); defn = NoDefn});;
let add = TBase("+", {kind = TArrow (TId "N", TArrow(TId "N", TId "N")); defn = NoDefn});;
let peano_concepts = Concept [nats;zero;suc;add;mul];;

(**[Quang]: Is this definition FieldSig ("suc(n1)", TId "N")] below valid ? 
 * I would use TArrow here:
 * Induct ("Nat", [FieldSig ("0", TId "N"); FieldSig ("suc", TArrow ((TId "N"), (TId "N")) ) ]   )
 *)
let peano_induct = Induct ("n", [FieldSig ("0", TId "N");FieldSig ("suc(n1)", TId "N")]);;  

(* Axioms *)
let var_spec_x = VarSpec(["x"],TId "N");;
let var_spec_xy = VarSpec(["x";"y"],TId "N");;
let add_ident = EqOp (Appl (BinOp (Ident "+", Ident "x", Ident "0")), Ident "x");;
let peano_axiom1 = (None, Binder (Forall, var_spec_x, add_ident),true);;
let peano_add1 = BinOp (Ident "+", Appl (GenApp (Ident "suc", Ident "x")), Ident "y");;
let peano_add2 = GenApp (Ident "suc", Appl (BinOp (Ident "+", Ident "x", Ident "y")));;
let peano_add = EqOp (Appl peano_add1, Appl peano_add2);;
let peano_axiom2 = (None, Binder (Forall, var_spec_xy, peano_add),true);;
let mul_nul = EqOp (Appl (BinOp (Ident "*", Ident "x", Ident "0")), Ident "0");;
let peano_axiom3 = (None, Binder (Forall, var_spec_x, mul_nul),true);;
let peano_mul1 = BinOp (Ident "*", Ident "x", Appl (GenApp (Ident "suc", Ident "y")));;
let peano_mul2 = BinOp (Ident "+", Ident "x", Appl (BinOp (Ident "*", Ident "x", Ident "y")));;
let peano_mul = EqOp (Appl peano_mul1, Appl peano_mul2);;
let peano_axiom4 = (None, Binder (Forall, var_spec_xy, peano_mul), true);; 
let peano_axioms = Fact [peano_axiom1;peano_axiom2;peano_axiom3;peano_axiom4;];;
let peano_thy = ThyExpr [peano_concepts;peano_induct;peano_axioms];;

let peano_assign = Assign ("Peano_Arithmetic",peano_thy);;
(* End of Peano Arithmetic*)

let my_test = peano_assign;; (* <- Create your own test case here *)

Test.assign peano_assign;;

let v = VarSpec (["x"], TId "R");;
let x = Binder (Forall, v, Ident "x * 1 = x");;
let h1 = Binder (Forall, v, x);;
let h2 = Binder (Forall, v, h1);;
let h3 = Binder (Forall, v, h2);;
let h4 = Binder (Forall, v, h3);;
let h5 = Binder (Forall, v, h4);;
let h6 = Binder (Forall, v, h5);;
let h7 = Binder (Forall, v, h6);;
let h8 = Binder (Forall, v, h7);;
let h9 = Binder (Forall, v, h8);;
let h10 = Binder (Forall, v, h9);;

let inverse_axiom = Binder (Forall,VarSpec(["x"],TId "R"),Binder (Exists,VarSpec(["x"],TId "R"), EqOp( Appl(BinOp( Ident "*", Ident "x", Ident "y")), Ident "1")));;

let binop_test = Appl (BinOp (Ident "*", Ident "x", Ident "x"));;
(* Declare division of reals *)
let a_b_spec = VarSpec(["a";"b"],TId "R");;
let r_q_spec = VarSpec(["r";"q"],TId "R");;
let r_lt_b = BinOp (Ident "<", Ident "r", Ident "b");;
let z_lte_r = BinOp (Ident "<=", Ident "0", Ident "r");;
let r_range = And (Appl r_lt_b, Appl z_lte_r);;
let b_mul_q = BinOp (Ident "*", Ident "b", Ident "q");;
let bq_add_r = BinOp (Ident "+", Appl b_mul_q, Ident "r");;
let a_equal_math = EqOp (Ident "a", Appl bq_add_r);;
let div_logic = And (a_equal_math, r_range);;
let div_exists = Binder (Exists,r_q_spec,div_logic);;
let div_axiom = Binder (Forall,a_b_spec,div_exists);;

let comm_axiom = Binder (Forall, VarSpec(["x";"y"],TId "R"), EqOp (Appl (BinOp (Ident "*",Ident "x", Ident "y")), Appl (BinOp (Ident "*", Ident "y", Ident "x"))));;

let xy_z = BinOp (Ident "*", Appl (BinOp ( Ident "*",Ident "x", Ident "y")), Ident "z");;
let x_yz = BinOp (Ident "*", Ident "x", Appl (BinOp ( Ident "*",Ident "y", Ident "z")));;
let assoc_axiom = Binder (Forall, VarSpec(["x";"y";"z"],TId "R"), EqOp (Appl xy_z, Appl x_yz));;

let long1 = And (assoc_axiom,comm_axiom);;
let long2 = And (inverse_axiom,div_axiom);;

let long = Iff (long1,long2);;

(*********** Start of Peano **********)

let peano_name = ThyName "Peano_Arithmetic"

(* Natural numbers declaration *)

(* Concepts *)
let nats = TBase ("N", {kind = Type; defn = (Manifest Type)});;
let zero = TBase ("0", {kind= TId "N"; defn = NoDefn});;
let suc = TBase("suc", {kind = TArrow (TId "N", TId "N"); defn = NoDefn});;
let mul = TBase("*", {kind = TArrow (TId "N", TArrow(TId "N", TId "N")); defn = NoDefn});;
let add = TBase("+", {kind = TArrow (TId "N", TArrow(TId "N", TId "N")); defn = NoDefn});;

let peano_concepts = Concept [nats;zero;suc;add;mul];;

let peano_induct = Induct ("n", [FieldSig ("0", TId "N");FieldSig ("suc(n1)", TId "N")]);;  

(* Axioms *)
let var_spec_x = VarSpec(["x"],TId "N");;
let var_spec_xy = VarSpec(["x";"y"],TId "N");;

let add_ident = EqOp (Appl (BinOp (Ident "+", Ident "x", Ident "0")), Ident "x");;
let peano_axiom1 = (None, Binder (Forall, var_spec_x, add_ident),true);;

let peano_add1 = BinOp (Ident "+", Appl (GenApp (Ident "suc", Ident "x")), Ident "y");;
let peano_add2 = GenApp (Ident "suc", Appl (BinOp (Ident "+", Ident "x", Ident "y")));;
let peano_add = EqOp (Appl peano_add1, Appl peano_add2);;
let peano_axiom2 = (None, Binder (Forall, var_spec_xy, peano_add),true);;

let mul_nul = EqOp (Appl (BinOp (Ident "*", Ident "x", Ident "0")), Ident "0");;
let peano_axiom3 = (None, Binder (Forall, var_spec_x, mul_nul),true);;

let peano_mul1 = BinOp (Ident "*", Ident "x", Appl (GenApp (Ident "suc", Ident "y")));;
let peano_mul2 = BinOp (Ident "+", Ident "x", Appl (BinOp (Ident "*", Ident "x", Ident "y")));;
let peano_mul = EqOp (Appl peano_mul1, Appl peano_mul2);;
let peano_axiom4 = (None, Binder (Forall, var_spec_xy, peano_mul), true);; 

let peano_axioms = Fact [peano_axiom1;peano_axiom2;peano_axiom3;peano_axiom4;];;

let peano_thy = ThyExpr [peano_concepts;peano_induct;peano_axioms];;

let peano_assign = Assign ("Peano_Arithmetic",peano_thy);;
(* End of Peano Basics *)

(* Distributivity *)
let var_spec_xyz = VarSpec(["x";"y";"z"],TId "N");; 
let x_mul_yz = BinOp (Ident "*", Ident "x", Appl (BinOp (Ident "+", Ident "y", Ident "z")));;
let xy_add_xz = BinOp (Ident "+", Appl (BinOp (Ident "*", Ident "x", Ident "y")), Appl (BinOp (Ident "*", Ident "x", Ident "z")));;
let distrib_axiom = EqOp (Appl x_mul_yz, Appl xy_add_xz);;
let peano_axiom5 = (None, Binder(Forall,var_spec_xyz,distrib_axiom), true);;

let ext_peano = ThyExtend (ThyName "Peano_Arithmetic", [Axiom peano_axiom5], Conservative);;
let assign_rich = Assign ("RichPeano",ext_peano);;

let semiring = ThyCombine ([ThyRename (ThyName "AbelianGroup",[("*","+")]); ThyName "Monoid"],ThyName "Carrier");;
let ring = Assign ("Ring", ThyExtend (semiring,[Axiom peano_axiom5],Conservative));;

(* Test pretty printing of TypeFrom *)
let type_of_peano = TTypeFromTheory "Peano_Arithmetic";;

(*Test.newline ();; 
Test.expr_aux long;;*)(*
Test.p "\n************ Peano Arithmetic Extend Test ************ \n";;
Test.newline ();;
Test.assign peano_assign;;
Test.newline ();;
Test.newline ();;
Test.assign assign_rich;;*)
Test.newline ();;
Test.p "\n****** Ring with Combines, Renaming and Extension ****** \n";;
Test.newline ();;
Test.assign ring;;
Test.newline ();;
Test.newline ();;
(*Test.newline ();;
Test.newline ();;*)
(*Test.expr_aux div_axiom;;*)
Test.newline ();;
Test.showTopType type_of_peano;;


