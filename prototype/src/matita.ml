(* matita.ml *)

(** This module provides functions for a (partial) translation of mathscheme
    terms to Matita terms *)
    
(* To properly transalte record field selectors we need to look up the type of
   the record being selected.  But for now we want to do the translation without
   typechecking, so we will fail if we try to translate record selectors *)

open Syntax
open List
open Bindings
open Library

(* unicode characters we will use *)
module UChar = CamomileLibraryDefault.Camomile.UChar
module UTF8 = CamomileLibraryDefault.Camomile.UTF8

exception MatitaEncodeException of string

let singleChar c = UTF8.init 1 (fun _ -> UChar.chr c)

let bb0 = singleChar 0x1d7d8 (* blackboard bold 0 *)
let bb1 = singleChar 0x1d7d9 (* blackboard bold 1 *)
let bbI = singleChar 0x1d540 (* blockboard bold I *)
let bbK = singleChar 0x1d542 (* blockboard bold K *)
let bW = singleChar 0x1d416  (* bold-W used for W quantifier *)
let defeq = singleChar 0x225d  (* equal by definition *)
let top = singleChar 0x22a4  (* top *)
let bottom = singleChar 0x22a5  (* bottom *)
let splat = singleChar 0x2217  (* middle asterisk *)
let times = singleChar 0xd7  (* cartesian product *)
let oplus = singleChar 0x2295  (* circled plus *)
let otimes = singleChar 0x2297  (* circled times *)
let lambda = singleChar 0x03bb  (* lower case lambda *)
let sigma = singleChar 0x03c3  (* lower case sigma *)
let epsilon = singleChar 0x025b (* epsilon *)
let iota = singleChar 0x03b9 (* iota *)
let lang = singleChar 0x2329  (* left angle bracket *)
let rang = singleChar 0x232a  (* right angle bracket *)
let rarr = singleChar 0x2192  (* right arrow *)
let rArr = singleChar 0x21d2  (* right double arrow *)
let darr = singleChar 0x2193  (* down arrow *)
let harr = singleChar 0x2194  (* horizontal arrow *)
let wedge = singleChar 0x2227  (* logical and *)
let vee = singleChar 0x2228  (* logical or *)
let neg = singleChar 0xac  (* logical not *)
let forall = singleChar 0x2200 (* for all *)
let exists = singleChar 0x2203 (* there exists *)
let hellip = singleChar 0x2026 (* horizontal ellipsis *)
let arabicZero = singleChar 0x0660 (* arabic-indo digit zero *)

let bracket s = "("^s^")"

(* given a string, replace all special characters with matita-friendly names, 
   and prefix with "ms_" *)
let escape s =
  let tick = arabicZero in
  let buf = ref "" in
  let tr x = (buf := !buf^tick^x^tick) in
  let f = function
    | '+' -> tr "plus"
    | '*' -> tr "star"
    | '<' -> tr "less"
    | '>' -> tr "greater"
    | '^' -> tr "caret"
    | '/' -> tr "slash"
    | '\\' -> tr "backslash"
    | '#' -> tr "number"
    | '@' -> tr "at"
    | '-' -> tr "minus"
    | '~' -> tr "tilde"
    | '\'' -> tr "quote"
    | '=' -> tr "equal"
    | '|' -> tr "bar"
    | x -> (buf := !buf^String.make 1 x)
  in
  String.iter f s; "ms_"^(!buf)

(* The translation requires an environment of type definitions because to
   translate a constructor selector we need to look up the inductive type
   definition. *)

type env =
  { tydefn : type_comp Util.StringMap.t
  ; tydecl : type_comp Util.StringMap.t
  }

let emptyEnv =
  { tydefn = Util.StringMap.empty
  ; tydecl = Util.StringMap.empty
  }

let rec normalize ev ty = 
  match ty with
    | TId id ->
      ( try normalize ev (Util.StringMap.find id ev.tydefn) 
        with Not_found -> ty )
    | TApp (tf,TId id) ->
      (* This needs to be made to handle arbitrary beta-reduction for types *)
      let tfn = normalize ev tf in
      begin match normalize ev tf with 
        | TBinder (VarSpec ([v],Some Type), bdy) when v = id -> bdy
        | TBinder (VarSpec (v::vs,Some Type), bdy) when v = id ->
          TBinder (VarSpec (vs,Some Type), bdy)
        | _ -> TApp (tfn, TId id)
      end
    | _ -> ty

let addTypeDef (ev:env) id ty =
  {ev with tydefn = Util.StringMap.add id ty (ev.tydefn)}
let addDecl (ev:env) id ty =
  {ev with tydecl = Util.StringMap.add id ty (ev.tydecl)}

(* This is a helper function for translating inductive types and the associated
   operations
   (i.e. Case)
   Given a type variable (usually the bound variable in an inductive type)
   abstract the given type into a container F (which can be interpreted as a
   strictly positive functor) such that if X is the type variable and T is the
   given type, then the resulting functor [[F]] is such that [[F]]X ~ T.
   In addition to the container F we want to return the isomorphism between
   [[F]]X and T.
   
   Thus half of the isomorphism, phi, has type T -> [[F]]X.
   The other half of the isomorphis, psi, has type [[F]]X -> T.

   Below we make a record type for all these components
*)

type containerTranslation =
  { container : string
  ; phi : string
  ; psi : string
  }

let identityContainer =
  { container = bbI
  ; phi = bracket ("idC_isoA ?")
  ; psi = bracket ("idC_isoB ?")
  }
                        
let constantContainer i =
  { container = bracket (bbK^" "^i)
  ; phi = bracket ("constC_isoA ? ?")
  ; psi = bracket ("constC_isoB ? ?")
  }

let oneContainer =
  { container = bb1
  ; phi = bracket ("constC_isoA ? ?")
  ; psi = bracket ("constC_isoB ? ?")
  }

let prodContainer c1 c2 =
  { container = bracket (c1.container^" "^times^" "^c2.container)
  ; phi = bracket
      (lambda^"x. prodC_isoA ? ? ? (("^c1.phi^" "^times^" "^c2.phi^") x)")
  ; psi = bracket
      (lambda^"x. ("^c1.psi^" "^times^" "^c2.psi^") (prodC_isoB ? ? ? x)")
  }

let zeroContainer =
  { container = bb0
  ; phi = bracket ("constC_isoA ? ?")
  ; psi = bracket ("constC_isoB ? ?")
  }

let sumContainer c1 c2 =
  { container = bracket (c1.container^" + "^c2.container)
  ; phi = bracket (lambda^"x. sumC_isoA ? ? ? ("^c1.phi^" + "^c2.phi^") x")
  ; psi = bracket (lambda^"x. ("^c1.psi^" + "^c2.psi^") (sumC_isoB ? ? ? x)")
  }

let rec decomposeContainer i = function
  | TId x -> if i = x then identityContainer else constantContainer (escape x)
  | TProd l ->
    fold_right (fun x -> prodContainer (decomposeContainer i x)) l oneContainer
  (* :TODO: handle more sophisticated cases. *)
  | _ ->
    raise (MatitaEncodeException "TODO: complete decomposeContainer function")

let rec fieldSigContainer i = function
  | TId x ->
    if i = x then [] else failwith ("fieldSigContainer: Bad Inductive Type: "^i)
  | TArrow (ty1, ty2) -> (decomposeContainer i ty1) :: (fieldSigContainer i ty2)
  | _ -> failwith ("fieldSigContainer: Bad Inductive Type: "^i)
    
let inductiveContainer id fsl =
  let f (FieldSig (lbl,ty)) = (lbl, (fieldSigContainer id ty)) in
  map f fsl
    
let inductiveContainerType ic = 
  let f (_,l) =
    fold_right (fun c ma -> bracket (c.container^" "^times^" "^ma)) l bb1
  in
  fold_right (fun p ma -> bracket (p^" + "^ma)) (map f ic) bb0  

let rec buildBody = function
  | [] -> ("",lang^rang)
  | (c::cl) ->
    let (lam, bod)= buildBody cl in
    let var = "a"^string_of_int (length cl) in
    (lambda^" "^var^". "^lam, lang^c.phi^var^", "^bod^rang)

let rec findConstructor lbl = function
  | [] -> failwith ("findConstuctor: label "^lbl^" not found")
  | (fld, cl) :: rest ->
    if fld = lbl
    then let (lam,bod) = buildBody cl in (lam, sigma^"1 "^bod)
    else let (lam,bod) = findConstructor lbl rest in
         (lam, sigma^"2 "^bracket bod)

let rec encodeType ev t = bracket 
  (match t with
    | Type -> "Type[0]"
    | TId x -> (escape x)
    | TProd l -> fold_right
        (fun ty rest -> bracket (encodeType ev ty^" "^times^" "^rest)) l bb1
    | TArrow (TDepId (id,ty1),ty2) ->
      forall^" "^escape id^" : "^encodeType ev ty1^" . "^encodeType ev ty2
    | TArrow (ty1,ty2) -> encodeType ev ty1^" "^rarr^" "^encodeType ev ty2
    | TPredicate ty -> encodeType ev ty^" "^rarr^" Prop"
    | TInduct (id, fsl) ->
      "W "^bracket (inductiveContainerType (inductiveContainer id fsl))
    | TLift ex -> encodeExpr ev ex
    | TApp (ty1, ty2) -> encodeType ev ty1^" "^encodeType ev ty2
    | TBinder (VarSpec (vl,ty),bd) ->
      let tys = match ty with
        | Some ty -> " : "^encodeType ev ty
        | None -> ""
      in
        lambda^(String.concat " , " (map escape vl))^tys^" . "^encodeType ev bd
    | _ ->
      let module M = 
        Printers.Make(Printers.Configuration.ASCII)(Printers.Options.StdOpt)
                     (struct let f = Format.str_formatter end) in
      let _ = M.showType t in raise 
        (MatitaEncodeException
          ("encodeType: not implemented:"^Format.flush_str_formatter ())))
and encodeExpr ev e = bracket
  (match e with
    | Ident x -> (escape x) 
    | EqOp (ex1,ex2) -> encodeExpr ev ex1^" = "^encodeExpr ev ex2
    | And (ex1,ex2) -> encodeExpr ev ex1^" "^wedge^" "^encodeExpr ev ex2
    | Or (ex1,ex2) -> encodeExpr ev ex1^" "^vee^" "^encodeExpr ev ex2
    | Not ex -> neg^" "^encodeExpr ev ex
    | Iff (ex1,ex2) -> encodeExpr ev ex1^" "^harr^" "^encodeExpr ev ex2
    | Implies (ex1,ex2) -> encodeExpr ev ex1^" "^rarr^" "^encodeExpr ev ex2
    | BFalse -> "False"
    | BTrue -> "True"
    | Appl (_,exf,ex) -> encodeExpr ev exf^" "^encodeExpr ev ex
    | Binder (q,VarSpec (vl,ty),ex) ->
      let qs = match q with
        | Forall -> " "^forall^" "
        | Exists -> " "^exists^" "
        | ExistsUniq -> " "^exists^"! "
        | Abs -> " "^lambda^" " in
      let (tys, ev') = match ty with
        | Some ty -> ( " : "^encodeType ev ty
                     , fold_left (fun e i -> addDecl e i ty) ev vl)
        | None -> ("",ev)
        in
        qs^(String.concat " , " (map escape vl))^tys^" . "^encodeExpr ev' ex
    | Desc (q,i,ty,ex) ->
      let qs = match q with
        | Iota -> " "^iota^" "
        | Epsilon -> " "^epsilon^" "
      in
      qs^escape i^" : "^encodeType ev ty^" . "^encodeExpr (addDecl ev i ty) ex
    | Tuple exl ->
      fold_right
        (fun ex rest -> lang^" "^encodeExpr ev ex^" , "^ rest^" "^rang)
        exl (lang^rang)
    | If (ex1,ex2,ex3) ->
      "if "^encodeExpr ev ex1
      ^" then "^encodeExpr ev ex2
      ^" else "^encodeExpr ev ex3
    | Case (Ident id,cases) ->
      begin match cases with
        | [Branch (PatTuple pl, bdy)] ->
          let getIdent = function
            | PatIdent id -> id
            | PatNone | PatConst _ | PatApp _ | PatTuple _ | PatRecord _ -> 
              raise
                (MatitaEncodeException
                  "encodeExpr: complex patterns not supported")
          in
          bracket
            (fold_right (fun i rest ->
                "'uncurry "^bracket(lambda^" "^escape i^" ."^rest))
              (List.map getIdent pl)
              ("'point "^encodeExpr ev bdy))
          ^ bracket (encodeExpr ev (Ident id))
        | _ -> 
          match normalize ev
              (try (Util.StringMap.find id ev.tydecl) 
               with Not_found -> raise
                   (MatitaEncodeException
                     ("encodeExpr: cannot find type for case analysis on "^id)))
          with
            | TInduct (ind, fsl) ->
              let ctr = inductiveContainer ind fsl in
              let pred = "P_"^ind in
              let return f = " return "^lambda^"w. ("
                ^pred^" "^f "w"^" "^rarr^" "^pred^" s) "^rarr^" ? " in
              let ctrty = inductiveContainerType ctr in
              let header bdy = "let "^pred^" "^defeq
                ^" pos "^bracket (ctrty)^" in "
                ^"match "^bracket (encodeExpr ev (Ident id)^" : W "^ctrty)^" with "
                ^"[roll r "^rArr^" match r with [contain s f "^rArr^" "^bdy
                ^" ("^lambda^"x.x)]]" in
              let mkCase (lbl,cont) rest (bv,f) =
                let rec findLabel = function
                  | PatConst x -> x = lbl                    
                  | PatApp (l,_) -> findLabel l
                  | PatIdent _ | PatNone | PatTuple _ | PatRecord _ -> false
                in
                let Branch (p,bdy) =
                  match List.filter (fun (Branch (p,_)) -> findLabel p) cases
                  with
                    | [] -> failwith ("encodeExpr: case "^lbl^" not found")
                    | [p0] -> p0
                    | _ -> failwith ("encodeExpr: multiple case "^lbl^" found")
                in
                let mkBranch _ rest (n,f) =
                  let v = "z"^string_of_int n in
                  let f' x = f (lang^v^", "^x^rang) in
                  "match y"^return f
                    ^"with [pair "^v^" y "^rArr^" "^rest (n+1,f')^"]"
                in
                let rec content n =
                  if 0 = n
                  then sigma^"1 z"
                  else sigma^"2"^bracket (content (n-1))
                in
                let rec binds n p cont = match p, cont with
                  | PatConst _, [] -> ""
                  | PatApp (p, PatIdent bv), c::cs ->
                    "let "^escape bv^" "^defeq^" "^c.psi^" "^bracket
                      ("contain ? ? z"^string_of_int n^" "^bracket 
                        (lambda^"z. f "^bracket
                          ("cast "^bracket (content n))))
                    ^" in "^binds (n+1) p cs
                  | _ ->
                    raise
                      (MatitaEncodeException
                        ("encodeExpr: complex patterns not supported for inductive types"))
                in
                let endBranch (_,f) =
                  "match y"^return f^"with [neo "^rArr^" "
                  ^lambda^"cast. "^binds 0 p cont^" "^encodeExpr ev bdy^"]"
                in
                "match "^bv^return f^"with "^ "[ sigma1 y "^rArr^" "
                ^fold_right
                   mkBranch cont endBranch 
                   (0,fun x -> f (bracket (sigma^"1 "^x)))
                ^" "^"| sigma2 x "^rArr^" "
                ^rest ("x",fun x -> f (bracket (sigma^"2 "^x)))^"]"
              in
              let bdy = fold_right mkCase ctr (fun (bv,_) -> "[]"^bv) in
              header (bdy ("s",fun x -> x))
            | _ -> failwith ("encodeExpr: not an inductive type for "^id)
      end
    | _ -> let module M =
        Printers.Make(Printers.Configuration.ASCII)(Printers.Options.StdOpt)
                     (struct let f = Format.str_formatter end) in
      let _ = M.expr e in
      raise
        (MatitaEncodeException
          ("encodeExpr: not implemented:"^Format.flush_str_formatter ())))

(* the - in axiom- means indexing is turned off *)
let makeTypeAxiom ev id ty = "axiom- "^escape id^" : "^encodeType ev ty^"."

let makePropAxiom ev id ex = "axiom- "^escape id^" : "^encodeExpr ev ex^"."

let makeTypeDef ev id ty def =
  "definition "^escape id^(*" : "^encodeType ev ty^*)" "^defeq
  ^" "^encodeType ev def^"."

let makeExprDef ev id ty binding def =
  "definition "^escape id^" : "^encodeType ev ty^" "^defeq
  ^" "^binding (encodeExpr ev def)^"."

let rec encodeTypDecl ev = function
  | TExtension (ids, ty) ->
    (ev, String.concat "\n" (map (fun id -> makeTypeAxiom ev id ty) ids))
  | TBase (id, {kind = ty; defn = NoDefn}) -> 
    encodeTypDecl ev (TExtension ([id], ty))
  | TBase (id, {kind = ty; defn = Manifest def}) ->
    (addTypeDef ev id def, makeTypeDef ev id ty def)
  | TBase (id, {kind = ty; defn = SubType _}) ->
    raise (MatitaEncodeException
             ("encodeTypDecl: subtyping not supported. Found in "^id))

let rec encodeFuncDecl (ev : env) ty prm bdy = match prm with
  | PConst id -> makeExprDef ev id ty (fun x -> x) bdy
  | PUniOp (id,p) ->
    let ev' = match ty with 
      | TArrow (dom,_) -> addDecl ev p dom
      | TPredicate dom -> addDecl ev p dom
      | _ -> ev in
    makeExprDef ev' id ty (fun x -> x) (Binder (Abs, VarSpec ([p], None), bdy))
  | PApp (id,_,ps) ->
    let ev' = match ty with
      | TArrow (TProd tys, _) -> fold_left2 addDecl ev ps tys
      | TPredicate (TProd tys) -> fold_left2 addDecl ev ps tys
      | _ -> ev in
    let binding bdy =
      fold_right (fun p rest ->
                    "'uncurry "^bracket(lambda^" "^escape p^" ."^rest))
                 ps ("'point "^bdy) in
    makeExprDef ev' id ty binding bdy

(*   
let encodeAxiomDecl (ev : env) = function
    | (Some id, ex, _) -> makePropAxiom ev id ex
    | (None, _, _) -> failwith ("encodeAxiomDecl: requires all axioms to be named")
*)

let get_context (b:bindings) = let f k sy df =
    match sy, df with
    | None  , None       -> None
    | Some s, None       -> Some (s, None)
    | None  , Some (s,d) -> Some (s, Some d)
    | Some _, Some _     -> failwith ("context: collion in name "^k) in
  Util.StringMap.merge f (get_symb b) (get_defns b)

let encodeBindings nm (b:bindings) =
  let fn = "matita/"^nm^".ma" in
  let ctx = get_context b in
  prerr_endline ("processing: "^fn);
  try
    let deps = get_depends b in
    let d_types =
      Toposort.depth_mark_objs (Util.keys ctx) (Toposort.find_with_empty deps)
    in
    let encodeItem ev (k,(ty,df)) =
      match df with
      | Some (prm, bdy) -> (ev, encodeFuncDecl ev ty.kind prm bdy)
      | None -> encodeTypDecl ev (TBase(k,ty))
    in
    let (tydeclEnv, typdecls) = 
      let (ev,decls) =
        fold_left (fun (ev,rest) kv ->
                     let (ev',str) = encodeItem ev kv
                     in (ev',fun x -> rest (str::x)))
                  (emptyEnv,fun x -> x)
                  (Toposort.stable_top_sort d_types ctx) in
      (ev, String.concat "\n\n" (decls [])) in
    let axioms = String.concat "\n\n"
        (Util.StringMap.fold 
          (fun k (v,_) rest -> makePropAxiom tydeclEnv k v :: rest)
          (get_props b)
          []) in
    let content = String.concat "\n\n" [typdecls; axioms] in
    (* binary mode is important so that wide UF8-codes are not improperly
       translated *)
    let chan = open_out_bin fn in 
    output_string chan "include \"Prelude.ma\".\n\n";
    output_string chan content;
    close_out chan
  with
    | Exceptions.Dependency x ->
      failwith ("Dependency for "^x^" not found in "^nm)
    | MatitaEncodeException err -> prerr_endline ("Warning: "^err)

let encodeLib lib = Util.StringMap.iter encodeBindings lib.theories

let expr = Library.read Sys.argv.(1) 
let lib = Reducer.reducer (Flattener.expand_top (Track.create_lib "top" expr))
(* let reif = Reify.reify_expanded_library lib *)
let _ = encodeLib lib
