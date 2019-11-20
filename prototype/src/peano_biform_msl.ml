(** 
 * Abstract syntax of Peano arithmetic in MSL
 *
 * @author: Quang M. Tran (tranqm@mcmaster.ca)
 *
 * In MSL concrete syntax:
 *
 * Peano_Arithmetic := Theory {
 *    Concept 
 *		      N   : type; 
 *          0   : N;
 *		      suc : N -> N;
 *		 
 *	   Inductive Nat
 *		   | 0    : N            
 *		   | suc  : N -> N;									         
 *
 * [Quang]: 
 * N and Nat are indeed types. However, in the current abstract syntax of the MSL,
 * 
 * Is there any way to merge them?
 *
 * We could use the imitate Haskell's notation for defining 
 * inductive data types.
 *
 * In Haskell:
 * data Nat = Zero 
 *          | Suc Nat
 * 
 * In MSL:
 * 1) One suggestion is that we could specify only the input arguments 
 * for constructors):
 *      
 *     Inductive Nat 
 *       | 0    Nat  
 *       | suc  Nat
 * 
 * 2) Alternatively, we could specify constructors as function definitions (with
 * input and return arguments)
 *
 *     Inductive Nat 
 *       | 0   : Nat
 *       | suc : Nat -> Nat 
 * }
 *)

(** Module Syntax defines the abstract syntax of the MSL *)
open Syntax
open Printers

module C = Msl_configuration.ASCII (* < Change your configuration here *)
module O = Msl_options.StdOpt (* <- Change your options here*)

module Test = Make(C)(O)(struct let f = Format.std_formatter end);;

(** Concepts *)
let nat_type = TBase  ("N",   { kind = Type; defn = (Manifest Type) })
let zero     = TBase  ("0",   { kind = TId "N"; defn = NoDefn })
let suc      = TBase  ("suc", { kind = TArrow (TId "N", TId "N"); defn = NoDefn})
let add      = TBase  ("+",   { kind = TArrow (TId "N", (TArrow (TId "N", TId "N"))); defn = NoDefn } )

let nat_idt  = Induct ("Nat", [FieldSig ("0", TId "N"); FieldSig ("suc", TArrow ((TId "N"), (TId "N")) ) ]   )
(** The concepts of PA biform theory *)
let concepts  = Concept [nat_type; zero; suc; add]

(** Axioms *)
(** a1: Forall x : N. x + 0 = x *)
let var_spec_x = VarSpec (["x"], TId "N")
let a1 = 
	let lhs = Appl (BinOp (Ident "+", Ident "x", Ident "0")) in
	   let rhs = Ident "x" in
		    (None, Binder (Forall, var_spec_x, EqOp (lhs, rhs)), true)

(** a2: Forall x, y : N. x + suc(y) = suc(x + y) *)
let var_spec_xy = VarSpec (["x"; "y"], TId "N")
let a2 = 
	let suc_app = Appl (GenApp (Ident "suc", Ident "y")) in
	   let lhs = Appl (BinOp (Ident "+", Ident "x", suc_app)) in
		    let add_app = Appl (BinOp (Ident "+", Ident "x", Ident "y")) in
				   let rhs = Appl (GenApp (Ident "suc", add_app)) in
					    (None, Binder (Forall, var_spec_xy, EqOp (lhs, rhs)), true)
(** The facts of PA biform *)
let facts = Fact [a1; a2]

(** Inductive datatype : TODO *)
let idt = Induct ("Nat", [FieldSig ("0", TId "N"); FieldSig ("suc", TArrow ((TId "N"), (TId "N")))] )

(** Transformers: TODO *)

(** PA biform theory *)
let peano_thy = ThyExpr [concepts; idt; facts]

(** Pretty print the PA biform theory *)
let peano_assign = Assign ("Peano_Arithmetic", peano_thy);;
Test.assign peano_assign;;