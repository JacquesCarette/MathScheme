module S = Syntax
module B = Bindings
module M = Mmt_syntax

(* convenient short-hands *)
let s x = [x]
let shortname x = M.ModId(None, s x)

(* this is for the MathScheme meta-theory, so say so: *)
let ms_uri = M.DocId "http://mathscheme.cas.mcmaster.ca/language"
let kernel = M.ModId (Some ms_uri, s "Chiron")
let skernel = shortname "Chiron"
let meta = Some kernel

let build x = M.Const(skernel, s x)
let buildloc m x = M.Const(m, s x)

(* Set of MathScheme constants which are in the meta-theory *)
module MS = struct
    (* for the terms *)
    let equal = build "="
    let setin = build "in"
    let band = build "and"
    let bor = build "or"
    let bnot = build "not"
    let biff = build "iff"
    let bimplies = build "implies"
    let constrsel = build "constr-select"
    let record = build "record"
    let patternmatch = build "pattern-match"
    let case = build "case"
    let tuple = build "(,)"
    let btrue = build "true"
    let bfalse = build "false"
    let if_ = build "if"

    (* quantifiers *)
    let forall = build "forall"
    let exists = build "exists"
    let existsuniq = build "existsuniq"
    let abs = build "lambda"

    let iota = build "iota"
    let epsilon = build "epsilon"

    (* for the types *)
    let ttype = build "type"
    let arrow = build "->"
    let product = build "type-prod"
    let typplus = build "type-plus"
    let mu = build "mu" (* least-fixed-point, aka inductive *)
    let recordtype = build "recordtype"
    let predicate = build "predicate"
    let subtype = build "subtype"
    let languageof = build "languageof"
    let depid = build "depid"
    let tbinder = build "type-lambda"

    (* patterns *)
    let patapp = build "pat-app"
    let patconst = build "pat-const"
    let pattuple = build "pat-tuple"

    (* for the axioms *)
    let axiom = build "ded" 
    let theorem = build "ded" 
end

let rec expr me = function
    | S.Ident i -> buildloc me i
    | S.BTrue -> MS.btrue
    | S.BFalse -> MS.bfalse
    | S.EqOp (a,b) -> M.App (MS.equal, [expr me a; expr me b])
    | S.In (a,b) -> M.App (MS.setin, [expr me a; typec me b])
    | S.And (a,b) -> M.App (MS.band, [expr me a; expr me b])
    | S.Or (a,b) -> M.App (MS.bor, [expr me a; expr me b])
    | S.Iff (a,b) -> M.App (MS.biff, [expr me a; expr me b])
    | S.Implies (a,b) -> M.App (MS.bimplies, [expr me a; expr me b])
    | S.Not a -> M.App (MS.bnot, [expr me a])
    | S.Appl ((_,a,b)) -> M.App (expr me a, [expr me b])
    | S.Binder (q, vs, e) -> M.Bind (quant q, varspec me vs, expr me e)
    | S.Desc (ch,i,ty,e) -> M.Bind(choice ch, varspec me (S.VarSpec ([i],Some ty)), expr me e)
    | S.Tuple el -> M.App(MS.tuple, List.map (expr me) el)
    | S.Record fml -> M.App(MS.record, List.map (fieldmem me) fml)
    | S.Selector _ -> failwith "selector not yet translated"
    | S.Case (e,cl) -> M.App(MS.patternmatch, expr me e :: List.map (cases me) cl)
    | S.If (b,tb,eb) -> M.App(MS.if_, [expr me b; expr me tb; expr me eb])
    | S.Let _ -> failwith "let not yet translated"
    | S.Escape _ -> failwith "escape not yet translated"
    | S.Quote _ -> failwith "quote not yet translated"
    | S.Eval _ -> failwith "eval not yet translated"
    | S.ProofObject _ -> failwith "ProofObjects not yet translated"
and typec me = function
    | S.Type -> MS.ttype
    | S.TId i -> buildloc me i
    | S.TApp (t1, t2) -> M.App(typec me t1, [typec me t2])
    | S.TProd l -> M.App (MS.product, List.map (typec me) l)
    | S.TArrow (a,b) -> M.App (MS.arrow, [typec me a; typec me b])
    | S.TPower _ -> failwith "power-set type not yet translated"
    | S.TInduct (i, fl) -> M.Bind (MS.mu, [(i,None,None)], 
        M.App(MS.typplus, List.map (fields me) fl))
    | S.TPredicate t -> M.App(MS.predicate, [typec me t])
    | S.TRecord fsl -> M.App(MS.recordtype, List.map (fields me) fsl)
    | S.TDepId (a,b) -> M.App(MS.depid, [buildloc me a; typec me b])
    | S.TLift e -> expr me e (* lift is an artifact *)
    | S.TTheory n -> M.App(MS.languageof, [buildloc me n])
    | S.TTypeFromTheory _ -> failwith "deriving types from theories not yet translated"
    | S.TProof _ -> failwith "proof types not yet translated"
    | S.TBinder (vs, ty) -> M.Bind(MS.tbinder, varspec me vs, typec me ty)
and cases me (S.Branch(pat,e)) = M.App(MS.case, [pattern me pat; expr me e])
and pattern me = function
    | S.PatNone -> failwith "fail-pattern not translated"
    | S.PatConst i -> M.App(MS.patconst, [buildloc me i])
    | S.PatIdent i -> buildloc me i
    | S.PatTuple l -> M.App(MS.pattuple, List.map (pattern me) l)
    | S.PatRecord _ -> failwith "record-pattern not translated"
    | S.PatApp (p1, p2) -> M.App(MS.patapp, [pattern me p1; pattern me p2]);
and fields me (S.FieldSig(f,t)) = M.App(buildloc me f, [typec me t])
and fieldmem me (S.FieldMem(f,t,e)) = 
    let r = match t with 
      | Some s -> [typec me s; expr me e]
      | None   -> [            expr me e] in
    M.App(buildloc me f, r)
and quant = function
    | S.Forall -> MS.forall
    | S.Exists -> MS.exists
    | S.ExistsUniq -> MS.existsuniq
    | S.Abs -> MS.abs
and choice = function
    | S.Iota -> MS.iota
    | S.Epsilon -> MS.epsilon
and varspec me (S.VarSpec (il, t)) = 
    let t = Util.map_option (typec me) t in
    let f i r = (i, t, None)::r in
    List.fold_right f il []

let funcdefn me (param, e) = match param with
    | S.PConst _ -> expr me e
    | S.PUniOp (_,j) -> M.Bind(quant S.Abs, [(j, None, None)], expr me e)
    | S.PApp (_, _, il) -> M.Bind(quant S.Abs, List.map (fun x -> (x, None, None)) il, expr me e)

let symbdecl me (i, {S.kind=k; S.defn=d}) = 
    let f = function
    | S.NoDefn -> M.TypedConstDecl(s i, typec me k)
    | S.SubType u -> M.TypedConstDecl(s i, M.App(MS.subtype, [typec me u]))
    | S.Manifest d -> M.ConstDefn(s i, typec me d) in
    f d

let defnsdecl me i ({S.kind=k; S.defn=_},fd) = 
    M.TypedConstDefn(s i, typec me k, funcdefn me fd)

let axdecl me (nm,e,b) = match nm with
    | Some n -> 
        if b then
            M.TypedConstDecl(s n, M.App (MS.axiom, [expr me e]))
        else
            M.TypedConstDefn(s n, M.App (MS.theorem, [expr me e]), M.Top)
    | None   -> failwith "encountered nameless axiom"

let gen = Util.gen_sym "i"
let gen_struct = fun nm -> M.ThyStructure(M.ThyStruct([gen ()],
    shortname nm, [], None))

let base_bindings me b =
    (* we need to borrow some code from Reify *)
    let deps = B.get_depends b in
    let d_types = Toposort.depth_mark_objs (Util.keys (B.get_symb b)) (Toposort.find_with_empty deps) in
    let symbs = Toposort.stable_top_sort d_types (B.get_symb b) in
    if not (Util.StringMap.is_empty (B.get_vars b)) then
        failwith "don't know how to translate variables" ;
    let body = List.concat [
      List.map (symbdecl me) symbs;
      Util.StringMap.fold (fun k v l -> defnsdecl me k v :: l) (B.get_defns b) [];
      Util.StringMap.fold (fun k (ax,b) l -> axdecl me (Some k,ax,b)::l) (B.get_props b) []
    ] in
    List.map (fun x -> M.ThyConst x) body

let rec thy_decl me n = function
    | S.AThy dl -> 
        let e = B.empty_pre_bindings () and eb = B.empty_bindings () in
        let b = B.add_pre_into_bindings (Track.tr_decl n e dl) eb in
        M.ThyDef ([n], base_bindings me b, meta)
    | S.AExtend (base, _, dl) ->
        let e = B.empty_pre_bindings () and eb = B.empty_bindings () in
        let b = B.add_pre_into_bindings (Track.tr_decl n e dl) eb in
        let body = base_bindings me b in
        M.ThyDef([n],
            M.ThyInclude (M.ThyName (shortname base)) :: body, meta)
    | S.ACombine (nl, over) ->
        M.ThyDef([n], 
            gen_struct over :: List.map gen_struct nl,
            (* aliases go here, with opens *)
            meta)
    | S.ARename (n2, []) -> M.ThyExpr (M.ThyName (shortname n2))
    | S.ARename (n2, sl) -> 
        M.ThyDef([n2], [M.ThyInclude (M.ThyName (shortname n2));
                        M.ThyAlias sl], meta)
    | S.AInstance _ -> failwith "instance - should not happen?"
    | S.ArrowName n -> M.ThyExpr( M.ThyName (shortname n))
    | S.AParComp _ -> failwith "arrow ParComp not done"
    | S.ASeqComp _ -> failwith "arrow SeqComp not done"
    | S.ArrowId -> failwith "identity arrow?"
    | S.AMixin (_,_) -> failwith "mixin"

let theory k v = M.Thy (thy_decl (shortname k) k v)

let translate _ lib = 
    let accum k v l = theory k v :: l in
    Util.StringMap.fold accum lib.Library.arrows []
