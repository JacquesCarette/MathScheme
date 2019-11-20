(** 
 * Abstract syntax implementation of the MathScheme Language (MSL) 
 *)

type ident = string           (* qualified identifiers *)
type proof_script = string

type field = string           (* record field or constructor names *)
type name = string

type qual = General | Conservative

type quant = Forall | Exists | ExistsUniq | Abs
type choice = Iota | Epsilon

(** Three kinds of type declaration:
 *    1) Manifest type   : A manifest type is a definition of a type synonym (i.e. giving a name to a type) 
 *    2) No definition   : 
 *    3) Subtype         : 
 *)
type 'a defn_kind = NoDefn | Manifest of 'a | SubType of 'a

type pattern = 
  | PatNone
  | PatIdent of ident
  | PatConst of ident  (* for a constant *)
  | PatTuple of pattern list
  | PatRecord of (ident * pattern) list
  | PatApp of pattern * pattern

(** Expressions are either terms or formulas *)
type expr =
  | Ident of ident
  | BTrue
  | BFalse
  | EqOp of expr * expr
  | In of expr * type_comp
  | And of expr * expr 
  | Or of expr * expr
  | Not of expr
  | Iff of expr * expr 
  | Implies of expr * expr
  | Appl of bool * expr * expr
  | Let of ident * expr * expr
  | Binder of quant * var_spec * expr
  | Desc of choice * ident * type_comp * expr
  | Tuple of expr list
  | Record of field_member list
  | Selector of expr * field
  | Case of expr * case list
  | If of expr * expr * expr
  | Escape of expr
  | Quote of expr
  | Eval of expr * type_comp
  | ProofObject of proof_script

and case = Branch of pattern * expr

and var_spec =
  | VarSpec of ident list * type_comp option

(** Type expressions *)
and type_comp =
  | Type
  | TId of ident
  | TApp of type_comp * type_comp
  | TProd of type_comp list (* Product type *)
  | TArrow of type_comp * type_comp (* Function type *)
  | TPower of type_comp              (* power-set type *)
  (* Inductive data type, e.g. Inductive Nat = 0 | suc n *)
  | TInduct of ident * field_sig list
  | TPredicate of type_comp          (* should not appear recursively? *)
  | TRecord of field_sig list
  | TDepId of ident * type_comp
  | TLift of expr                    (* an expression lifted as a type *)
  (* below are the lifting of theories to the expression context *)
  | TTheory of ident                 (* A theory reflected as an inductive type *)
  | TTypeFromTheory of ident         (* Deriving a type from a theory *)
  | TProof of expr                   (* Type of proofs *)
  | TBinder of var_spec * type_comp  (* type-level lambda *)

(** Field_sig defines the signature of a field in an 
 *  inductive data type or record
 *)
and field_sig =
  | FieldSig of field * type_comp

and field_member = 
  | FieldMem of field * type_comp option * expr

(** Each type declaration (in Concept) has this form (= of this type) *)
type typ_decl = { kind : type_comp; defn : type_comp defn_kind }

(** Defines an entry in the Concept part. For example,
 *  In a Peano Arithmetic, we may define the following concepts
 *  as typedelc: 
 *      N   : type is defined as   TBase ("N", { kind = Type; defn = (Manifest Type) })
 *      0   : type is define as    TBase ("0", { kind = TId "N"; defn = NoDefn })
 *      suc : N -> N is defined as TBase ("suc", {kind = TArrow (TId "N", TId "N"); defn = NoDefn}     
 *)
type typedecl =
  | TBase of ident * typ_decl    (* either a typing relation or a manifest type definition *)
  | TExtension of ident list * type_comp  (* extending type declaration, like m, n, ... u, v : Int -> Int *)

type param_decl =
  | PConst of ident
  | PUniOp of ident * ident
  | PApp of ident * bool * ident list       (* pattern matching a tuple *)
      (* the bool is to indicate inline or not *)
  
type funcdefn = param_decl * expr

(** Axiom declaration has
 *     - a name of axiom (optional)
 *     - an expression 
 *     - a boolean value
 *  E.g. (None, forall x : N. x + 0 = 0, true)
 *
 *)
type axdecl = name option * expr * bool

type ren  = ident * ident                     (* simple substitution (rename) *)
type subst = Subst of ident * expr

type arr_ren = name * ren list

type declaration =
  | TypDecl of typedecl                       (* type declaration/abbr *)
  | FuncDecl of funcdefn                      (* single function declaration *)
  | VarDecl of typedecl list                  (* variable declaration *)
  | Axiom of axdecl                           (* axiom/theorem decl *)
  | Induct of ident * field_sig list          (* inductive decl *)
 
and arrow = 
  | AThy of declaration list
  | ASeqComp of name * name * name list       (* length >= 2 *)
  | AParComp of name * name
  | ArrowName of name
  | ArrowId
  | AInstance of name * name * subst list 
  | AExtend of ident * qual * declaration list
  | ACombine of ident list * ident   
  | AMixin of arr_ren * arr_ren
  | ARename of arr_ren

and assign = 
  | NamedArrow of name * arrow
  | NamedSubst of name * subst list

type toplevel_expr = assign list

let mkType t = {kind = t; defn = NoDefn}
let mkManifest t = {kind = Type; defn = Manifest t}
let mkSubtype t = {kind = Type; defn = SubType t}

let mkSeqComp = function
    | [] | [_] -> assert false
    | x::y::rest -> ASeqComp(x,y,rest)

(* utility, like opt_apply *)
let apply_to_type f = function
    | NoDefn -> NoDefn
    | Manifest t -> Manifest (f t)
    | SubType t -> SubType (f t)

(* like Util.maybe *)
let on_kind f a = function
    | NoDefn -> a
    | Manifest t -> f t
    | SubType t -> f t

let build_type typ = function
    | [t] -> TBase(t,mkType typ)
    | x   -> TExtension(x,typ)

let is_type_defn = function
    | Type -> true
    | TId _ | TApp _  | TProd _ | TArrow _ | TInduct _ | TLift _ 
    | TTheory _ | TTypeFromTheory _ | TProof _ | TPower _ 
    | TPredicate _ | TRecord _ | TDepId _ | TBinder _ -> false

let cut_first s = String.sub s 1 ((String.length s) - 1)

let is_oper n = 
    try let _ = String.index "+*<>^/\\#_@-'=|" n.[0] in true
    with Not_found -> false

let mkPApp inl f xs = match xs with
    | [x] -> PUniOp (f,x)
    | _ -> PApp (f,inl,xs)

let param_decl_name = function
    | PConst n -> n
    | PUniOp(n,_) -> n
    | PApp(n,_,_) -> n

let param_decl_params = function
    | PConst _ -> []
    | PUniOp(_,p) -> [p]
    | PApp(_,_,ps) -> ps

let getPApp = function
    | PConst n -> (n,false,[])
    | PUniOp(n,p) -> (n,false,[p])
    | PApp(n,b,ps) -> (n,b,ps)
 
let updateParam x n b ps = match x, ps with
    | PConst _, [] -> PConst n
    | PUniOp _, [p] -> PUniOp (n,p)
    | PConst _, _ | PUniOp _, _ | PApp _, _ -> PApp (n,b,ps)

let assign_name = function
    | NamedArrow(n,_) -> n
    | NamedSubst(n,_) -> n

(* "extending" a name *)
module Nameext : sig val extend : name -> (name*name) end = struct
    let base = ref 0
    let extend s =
        base := !base + 1;
        (s, s^"'"^ string_of_int !base)
end

(* For the moment we have no proof objects yet. Therefore, the universal proof object 
 * is used whenever we need a proof object. 
 *)
let u_proof = ProofObject "I am the proof for everything"

let getFieldSigName (FieldSig (n, _)) = n

let getFieldSigType (FieldSig (_, typ)) = typ

let getDepId t = match t with
    | TDepId (n,ty) -> (Some n, ty)
    | Type | TId _ | TApp _  | TProd _ | TArrow _ | TInduct _ | TLift _ 
    | TTheory _ | TTypeFromTheory _ | TProof _
    | TPower _ | TPredicate _ | TRecord _ | TBinder _ -> (None, t)   

let explode s = 
    let l = String.length s in
    let rec expl ps n =
        try
            let i = String.index_from ps n '/' in
            let len = n - i -1 in
            String.sub ps n len :: expl ps (i+1) 
        with Not_found ->
            [String.sub ps n (l - n)]
    in expl s 0
