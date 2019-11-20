open Syntax
open List
open Bindings
open Library

open Format

module SM = Util.MakeBetterMap(Util.Strings)

type dfs_color = DfsWhite | DfsGrey | DfsBlack

exception DependencyCycle

let rec ppPattern = function
    | PatNone -> "<PatNone>"
    | PatIdent i -> "<PatIdent>("^i^")"
    | PatConst i -> "<PatConst>("^i^")"
    | PatTuple pl -> "<PatTuple>(???)"
    | PatRecord ipl -> "<PatRecord>(??? list)"
    | PatApp (p1, p2) -> "<PatApp>("^(ppPattern p1)^","^(ppPattern p2)^")"

let rec type_comp = function
  | Type -> "<type>"
  | TId id -> "$"^id
  | TApp (tc1, tc2) -> "<TApp>("^(type_comp tc1)^")("^(type_comp tc2)^")"
  | TProd tcs -> "["^(List.fold_left (fun s tc -> s^"("^(type_comp tc)^")") "" tcs)^"]"
  | TArrow (tc1, tc2) -> "<TArrow>("^(type_comp tc1)^")("^(type_comp tc2)^")" (* Function type *)
  | TPower tc -> "<TPower>("^type_comp tc^")" (* power-set type *)
  | TInduct (id, fs) -> "<TInduct>("^id^",???)"(* fs: field_sig list *)
  | TPredicate tc -> "<TPredicate>("^(type_comp tc) (* should not appear recursively? *)
  | _ -> "[TC ???]"
(*
  (* Inductive data type, e.g. Inductive Nat = 0 | suc n *)
  | TRecord of field_sig list
  | TDepId of ident * type_comp
  | TLift of expr                    (* an expression lifted as a type *)
  (* below are the lifting of theories to the expression context *)
  | TTheory of ident                 (* A theory reflected as an inductive type *)
  | TTypeFromTheory of ident         (* Deriving a type from a theory *)
  | TProof of expr                   (* Type of proofs *)
  | TBinder of var_spec * type_comp  (* type-level lambda *)
*)

let rec ppExpr e =     print_string (expr e)
and quant = function
    | Forall -> "forall."
    | Exists -> "exists."
    | ExistsUniq -> "exists!."
    | Abs -> "abs."
and varspec = function
    | VarSpec (ids, tcOpt) ->  (List.fold_left (fun s id -> s^" "^id) "" ids) ^ 
        match tcOpt with
        | Some tc -> " : "^(type_comp tc)
        | None -> ""
and expr = function
    | Ident ident -> "$"^ident
    | BTrue -> "<true>"
    | BFalse -> "<false>"
    | EqOp (e1, e2) -> "(" ^ (expr e1)^" = "^(expr e2) ^ ")"
    | In (e1, tc) -> "[IN]"
    | And (e1, e2) -> "(" ^ (expr e1)^" & "^(expr e2) ^ ")"
    | Or (e1, e2) -> "(" ^ (expr e1)^" | "^(expr e2) ^ ")"
    | Not e  -> "(" ^ "! "^(expr e) ^ ")"
    | Iff (e1, e2) -> "[IFF]"
    | Implies (e1, e2) -> "(" ^ (expr e1)^" => "^(expr e2) ^ ")"
    | Appl (b, e1, e2) -> "[appl."^(if b then "T" else "F")^"("^(expr e1)^")("^(expr e2)^")]"
    | Binder (q, vs, e) -> (quant q) ^ (varspec vs) ^ ". " ^ (expr e)
    | Desc (_, _, _, _) (* choice * ident * type_comp * expr *) -> "[DESC]"
    | Tuple e -> "[" ^ (List.fold_left (fun s e -> s^" ("^(expr e)^")") "" e) ^ "]"
    | Record _ (* field_member list *) -> "[RECORD]"
    | Selector (_, _) (* expr * field *) -> "[SELECTOR]"
    | Case (e, cl) (* expr * case list *) ->
        let caseToString = function
        | Branch (p, e) -> (ppPattern p)^" -> "^(expr e)
        in
        let clString = List.fold_left (fun s c -> s^" | "^(caseToString c)) "" cl in
        "CASE ("^(expr e)^")"^clString^" ENDCASE"
    | If (_, _, _) (* expr * expr * expr *) -> "[IF]"
    | Escape _ (* expr *) -> "[ESCAPE]"
    | Quote _ (* expr *) -> "[QUOTE]"
    | Eval _ (* expr * type_comp *) -> "[EVAL]"
    | ProofObject _ (* proof_script *) -> "[PROOFOBJECT]"

(* Fold in Topological order with Depth First Search *)
let arrow_dfs_fold lib f accum names =
  let dfs_arrows = ref (SM.map (fun a -> (ref DfsWhite, a) ) lib.arrows) in
  let rec fold1 accum name =
    let (color, arrow) = SM.find name !dfs_arrows in
    (match !color with
    | DfsBlack -> accum
    | DfsGrey -> raise DependencyCycle
    | DfsWhite ->
      color := DfsGrey;
      let accum =
        match arrow with
        | ThyTBase _ -> accum
        | ThyTExtend (_,n,_,_) -> fold1 accum n
        | ThyTComb (_,(nl,_)) -> List.fold_left fold1 accum nl
        | ThyInstance (_,n,_) -> fold1 accum n
        | ArrowN n -> fold1 accum n
        | ParComp (p1,p2) -> 
          let accum = fold1 accum p1 in
          fold1 accum p2
        | SeqComp (x,y,l) -> List.fold_left fold1 accum (x::y::l)
        | Rename (n, _) -> fold1 accum n
      in
      color := DfsBlack;
      f accum (name, arrow)
    )  
  in List.fold_left fold1 accum names

type 'a dfs_status = DfsReady | DfsInProgress | DfsDone of 'a

let expLength = 
  let rec f x = function
    | Ident _ -> x + 1
    | BTrue -> x + 1
    | BFalse -> x + 1
    | EqOp (e1, e2) -> f (f (x + 1) e1) e2
    (*  | In (e1, tc) -> *)
    | And (e1, e2) -> f (f (x + 1) e1) e2
    | Or (e1, e2) -> f (f (x + 1) e1) e2
    | Not e  -> f (x + 1) e
    (* | Iff (e1, e2) -> *)
    | Implies (e1, e2) -> f (f (x + 1) e1) e2
    | Appl (b, e1, e2) -> f (f (x + 1) e1) e2
    (* | Binder (q, _, e) -> *)
    (* | Desc (_, _, _, _) (* choice * ident * type_comp * expr *) -> *)
    | Tuple e -> List.fold_left f x e
    (* | Record _ (* field_member list *) -> "[RECORD]"
    | Selector (_, _) (* expr * field *) -> "[SELECTOR]"
    | Case (e, cl) (* expr * case list *) ->
        let caseToString = function
        | Branch (p, e) -> (ppPattern p)^" -> "^(expr e)
          in
        let clString = List.fold_left (fun s c -> s^" | "^(caseToString c)) "" cl in
        "CASE ("^(expr e)^")"^clString^" ENDCASE"
    | If (_, _, _) (* expr * expr * expr *) -> "[IF]"
    | Escape _ (* expr *) -> "[ESCAPE]"
    | Quote _ (* expr *) -> "[QUOTE]"
    | Eval _ (* expr * type_comp *) -> "[EVAL]"
    | ProofObject _ (* proof_script *) -> "[PROOFOBJECT]"
    *)
    | _ -> failwith "Length ARG"
  in f 0

let extract_symb k a b = match (a,b) with
  | (Some _, Some _) -> None
  | (None  , Some _) -> failwith (k^" has a definition but not type")
  | (z     , None  ) -> z

(* Fold in Topological order with Depth First Search *)
let symbol_map lib =
  let arrows = SM.map (fun a -> (ref DfsReady, a) ) lib.arrows in
  let rec getSymbols name =
    let (status, arrow) = SM.find name arrows in
    getSymbolsQuick name (status, arrow)
  and getSymbolsQuick name (status, arrow) =
    match !status with
    | DfsDone symbols -> symbols
    | DfsInProgress -> raise DependencyCycle
    | DfsReady ->
      status := DfsInProgress;
      let v = match arrow with
        | ThyTBase (_,b) -> b.symbols
        | ThyTExtend (_,n,_,pre) ->
          let symbols = SM.merge extract_symb pre.types pre.functions in
          SM.fold SM.add (getSymbols n) symbols;
        | ThyTComb (_,(nl,b)) ->
          let symbolsList = List.map getSymbols nl in          
          let overSymbols = getSymbols b in
          let a = Array.of_list symbolsList in
          let symbloc = Flattener.find_dups_in_tbl overSymbols symbolsList in
          (* Note, no handling of duplicates - just takes first *)
          List.fold_left (fun m (n,l) -> SM.add n (SM.find n a.(List.hd l)) m) overSymbols symbloc
        | ThyInstance (_,n,_) -> getSymbols n (* Is this right? *)
        | ArrowN n -> getSymbols n
        | ParComp (p1,p2) -> failwith "ParComp"
        | SeqComp (x,y,l) -> getSymbols x (* TODO, perform additional steps in sequence. *)
        | Rename (n, sub) -> List.fold_left (fun m (oldId, newId) -> try SM.remove oldId (SM.add newId (SM.find oldId m) m) with Not_found -> m ) (getSymbols n) sub
      in
      status := DfsDone v; v
  in
  SM.mapi (getSymbolsQuick) arrows

(*
let cons a b = a :: b
let arrow_dfs_list lib names = arrow_dfs_fold cons () names
*)

let newCnt i () =
  let v = !i in
  i := v+1; v

let printParameters (typeMap: char SM.t) (symbolIndex: (int * Syntax.typ_decl) SM.t) =
  let printType_decl (name : string) ((i,dec) : int * Syntax.typ_decl) = 
    let rec printType_comp = function
    | Type -> ()
    | TId id -> printf "'%c" (SM.find id typeMap)
    | TArrow (TProd ps, r) ->
        List.iter (fun p -> printType_comp p; printf "->" ) ps;
        printType_comp r;
    | TArrow (TId p, r) ->
        printType_comp (TId p); printf "->";
        printType_comp r;
    | _ -> failwith "arrg"
  in
    match dec.kind with
    | TId id -> printf "@ (f%i:'%c)" i (SM.find id typeMap);
    | kind -> (      
      printf "@ (f%i:(" i;
      printType_comp kind;
      printf ") ref)")
  in
  SM.iter printType_decl (SM.filter (fun _ (_,d) -> match d.kind with Type -> false | _ -> true) symbolIndex)

let filterOutTypeSymbols _ d = 
  match d.kind with 
  | Type -> false
  | _ -> true

let printSubDefine n lookup symbols =
  let s = SM.filter filterOutTypeSymbols symbols in
  if (SM.cardinal s) > 0 then (
    printf "@[if not (StringSet.mem \"%s\" over) then intern%s@ over" n n;
    SM.iter (fun name _ -> printf "@ f%i" (lookup name)) s;
    printf ";@]@ "
  )

let printProps fnum symbolIndex name pl =
  let rec printing = function
    | (n, vs, l, e2)::pl ->
        let opCnt = newCnt (ref 0) in
        let varCnt = newCnt (ref 0) in 
        let varName = ref (SM.map (fun (i,_) -> "f"^(string_of_int i)) symbolIndex) in
        let whenList = ref [] in
        printf "(* %s *)@ @[<2>| " n;
        (match l with
          | x::xs ->
              expPattern opCnt varCnt varName whenList x;
              List.iter (fun x -> printf ",@ "; expPattern opCnt varCnt varName whenList x) xs
          | _ -> ());
        (match !whenList with
          | x::xs -> 
            printf "@ when %s" x;
            List.iter (printf " && %s") xs
          | _ -> ());
        printf " ->@ ";
        expOutput !varName e2;
        printf "@]@ ";
        printing pl
    | [] -> ()
  and expPattern opCnt varCnt varName whenList = function
    | Ident ident ->
        let v = "v"^(string_of_int (varCnt())) in
        printf "%s" v;
        if SM.mem ident !varName then
          whenList := (v^"="^(SM.find ident !varName))::!whenList
        else
          varName := SM.add ident v !varName
    | Appl (b, Ident f, Tuple [e1; e2]) ->
        let op = "op"^(string_of_int (opCnt())) in
        whenList := (op^"==f"^(string_of_int(fst(SM.find f symbolIndex))))::!whenList;
        printf "(PartialBinary (%s," op;
        expPattern opCnt varCnt varName whenList e1;
        printf ",";
        expPattern opCnt varCnt varName whenList e2;
        printf "))"
    | Appl (b, Ident f, e) ->
        let op = "op"^(string_of_int (opCnt())) in
        whenList := (op^"==f"^(string_of_int(fst(SM.find f symbolIndex))))::!whenList;
        printf "(PartialUnary (%s," op;
        expPattern opCnt varCnt varName whenList e;
        printf "))"
    | e -> printf "%s" (expr e)
  and expOutput varName = function
    | Ident ident -> printf "%s" (SM.find ident varName)
    | Appl (b, Ident f, Tuple [e1; e2]) ->
        printf "(@[<hv 2>!f%i@ " (fst(SM.find f symbolIndex));
        expOutput varName e1;
        printf "@ ";
        expOutput varName e2;
        printf "@])"
    | Appl (b, Ident f, e) ->
        printf "(@[<hv 2>!f%i@ " (fst(SM.find f symbolIndex));
        expOutput varName e;
        printf "@])"
    | _ -> failwith "ARG2"
  and parameterString sep s = function
  | 1 -> "p1"^s
  | x when x < 1 -> failwith "parameterString < 1"
  | x -> parameterString sep (sep^"p"^(string_of_int x)^s) (x-1) 
  in
  if (List.length pl) > 0 then (
    let numParameters = (let (_, _, l, _) = (hd pl) in List.length l) in
    let commaParameters = parameterString ", " "" numParameters in
    let spaceParameters = parameterString " " "" numParameters in
    printf "let k = !f%i in@ @[<hv 2>f%i := (fun %s ->@ match %s with@ " fnum fnum spaceParameters commaParameters;
    printing pl;
    printf "(* Continuation *)@ @[<2>| _ -> k %s@]@]@,);@ " spaceParameters
  )

let collateProps symbolIndex props =
  let a = Array.make (SM.cardinal symbolIndex) [] in
  let add name (exp, eType) =
    match exp with
    | Binder (Forall, vs, EqOp (e1, e2)) ->
      let len1 = expLength e1 in
      let len2 = expLength e2 in
      if len1 != len2 then (
        let (e1, e2) = if len1 > len2 then (e1, e2) else (e2, e1) in
        match e1 with
        | Appl (b, Ident f, Tuple l) ->
          let (i,_) = SM.find f symbolIndex in
          a.(i) <- (name, vs, l, e2)::a.(i)          
        | _ -> failwith "Huh1"        
      )
    | _ -> failwith "Huh2"
  in SM.iter add props; a

let printArrow symbols _ (name, arrow) =
  let (s1,s2) = SM.partition filterOutTypeSymbols (SM.find name symbols) in
  let symbolIndex = SM.map (let cnt = newCnt (ref 0) in (fun x -> (cnt (),x))) s1 in
  let typeMap = SM.map (let cnt = newCnt (ref (Char.code 'a')) in (fun _ -> Char.chr (cnt()))) s2 in
  let printLet nm =
    printf "@,@[<v>@[<v 2>(* %s" name;
    SM.iter (fun name (i,_) -> printf "@ f%i = %s" i name) symbolIndex;
    printf "@]@ *)@,@[<hv 2>let intern%s@ over" nm;
    printParameters typeMap symbolIndex;
    printf " =@]@,  @[<v>"
  in
  let printEnd nm =
    printf "()@]@,@[<2>let define%s" nm;
    printParameters typeMap symbolIndex;
    printf " =@ @[intern%s@ StringSet.empty" nm;
    SM.iter (fun _ (i,_) -> printf "@ f%i" i) symbolIndex;
    printf "@]@]@,"
  in
  (match arrow with
  | ThyTBase (nm, b) ->
    printLet nm;
    let aProps = collateProps symbolIndex b.props in
    SM.iter (fun name (i,_) -> printProps i symbolIndex name aProps.(i)) symbolIndex;
    printEnd nm 
  | ThyTExtend (nm,n,_,pre) ->
    printLet nm;
    let lookup name = (fst (SM.find name symbolIndex)) in
    printSubDefine n lookup (SM.find n symbols);
    let aProps = collateProps symbolIndex pre.axioms in
    SM.iter (fun name (i,_) -> printProps i symbolIndex name aProps.(i)) symbolIndex;
    printEnd nm 
  | ThyTComb (nm,(nl,over)) ->
    printLet nm;
    printf "let over = StringSet.add \"%s\" over in@ " over;
    let lookup name = (fst (SM.find name symbolIndex)) in
    List.iter (fun n -> printSubDefine n lookup (SM.find n symbols)) nl;
    printEnd nm 
  | Rename (n, subs) -> 
    printLet name;
    let lookup name =
      let name = 
        try List.assoc name subs 
        with Not_found -> name 
      in (fst (SM.find name symbolIndex))
    in
    printSubDefine n lookup (SM.find n symbols);
    printEnd name 
  | _ -> failwith "Arrow")
  
let printStaged lib names =
  Format.set_margin 130;
  let symbols = symbol_map lib in
  printf "@[<v>include Mkstaged_head@ module Make = struct@,@[<v 2>";
  arrow_dfs_fold lib (printArrow symbols) () names;
  printf "@]@,@]@,end@,"

let ppTyp_decl (s: typ_decl) = 
    print_string ( "Kind="^(type_comp s.kind)^", Defn=" );
    match s.defn with
    | NoDefn -> print_string ("NoDefn")
    | Manifest c -> print_string ("Manifest "^type_comp c) 
    | SubType c -> print_string ("SubType "^type_comp c) 

let ppSymbols nm (s: typ_decl) =
    print_string ("\n    "^nm^" : ");
    ppTyp_decl s

let ppFuncdefn = function
    | (PConst i, e) ->
        print_string ("PConst "^i^". ");
        ppExpr e
    | (PUniOp (i1, i2), e) ->
        print_string ("PUniOp ("^i1^","^i2^"). ");
        ppExpr e
    | (PApp (i, _, is), e) ->
        let isString : ident = List.fold_left (fun s i -> s^" "^i) "" is in
        print_string ("PApp ("^i^","^isString^"). ");
        ppExpr e         

let ppDefns nm (d: typ_decl * funcdefn) =
    print_string ( "\n    "^nm^" : " );
    print_string ( type_comp (fst d).kind );
    print_string ( " = " );
    ppFuncdefn (snd d)
    
let ppVars nm (c:type_comp) = print_string ( " "^nm )

let rec propGood = function
    | EqOp (e1, e2) -> true
    | Appl (true, f, Tuple e) -> true
    | Implies (e1, e2) -> true
    | Binder (Forall, vs2, e) -> propGood e
    | _ -> false

let ppProps nm (e, eType) =
    print_string ( "\n    " );
    if not (propGood e) then print_string "BAD ";
    print_string (if eType then "AXIOM " else "THEORY ");
    print_string ( nm^" : " );
    ppExpr e
        
let ppBindings nm (b:bindings) =
    print_string ( "  SYMBOLS:" );
    Util.StringMap.iter ppSymbols b.symbols;
    print_string ( "\n" );
    print_string ( "  DEFNS:" );
    Util.StringMap.iter ppDefns b.defns;
    print_string ( "\n" );
    print_string ( "  VARS:" );
    Util.StringMap.iter ppVars b.vars;
    print_string ( "\n" );
    print_string ( "  PROPS:" );
    Util.StringMap.iter ppProps b.props;
    print_string ( "\n" )

let ppLib lib = Util.StringMap.iter ppBindings lib.theories

let ppArrow _ (name, arrow) =
  match arrow with
  | ThyTBase (nm, b) -> print_string ( "#BASE# "^name^"\n" )
    (* ppBindings nm b *)
  | ThyTExtend (_, nm, _, pre_b) ->
    print_string ( "#EXTEND# "^nm^" => "^name^"\n" )
    (* ppBindings nm (extract_bindings pre_b) *)
  | ThyTComb (_, (nl, over)) ->
    print_string ( "#COMBINE# "^name^"\n" );
    List.iter (fun nm -> (print_string (nm^" "))) nl;
    print_string ("OVER "^over^"\n")
  | ThyInstance _ -> print_string ( "#INSTANCE# "^name^"\n" )
  | ArrowN _ -> print_string ( "#ARROW# "^name^"\n" )
  | ParComp _ -> print_string ( "#PARCOMP# "^name^"\n" )
  | SeqComp _ -> print_string ( "#SEQCOMP# "^name^"\n" )
  | Rename _ -> print_string ( "#RENAME# "^name^"\n" )

let expr = Library.read "../../../doc/biform-theories/Algebra/Base.msl"
let lib = Track.create_lib "top" expr
let _ = printStaged lib ["CommutativeRing"]
let _ = print_newline
(* 
let _ = arrow_dfs_fold lib ppArrow () ["Ring"]
let lib = Flattener.expand_top lib
let lib = Reducer.reducer lib
let _ = ppLib lib
*)
