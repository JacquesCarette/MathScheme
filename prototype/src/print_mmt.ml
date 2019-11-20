(* pretty-printer, of sorts, for MMT *)

open Mmt_syntax

(* convenience *)
let tag ns n = (ns,n), []
let atag ns (n,l) = (ns,n), l
let attrib (n:string) (v:string) = (("",n),v)
let nameattrib = attrib "name"
let cdattrib = attrib "cd"
let locid l = String.concat "/" l
let docid (DocId u) = u
let modid (ModId(d,l)) = match d with 
  | Some di -> (docid di)^"?"^(locid l)
  | None -> locid l
let metaattrib = function
    | Some m -> attrib "meta" (modid m)
    | None   -> failwith "no meta-logic present in input"

(* internal names for tags *)
let omdocns = ""
let omns = "om"
let omdocnshttp = "http://omdoc.org/ns"
let omnshttp = "http://www.openmath.org/OpenMath"
let omdoc (uri,loc) = ("omdoc", 
  [((Xmlm.ns_xmlns, "om"), omnshttp); 
   ((Xmlm.ns_xmlns, "xmlns"), omdocnshttp);
   (("","base"), uri^"/"^(locid loc))])

let ns_resolve (s:string) = match s with
  | "om" -> Some omns
  | "omdoc" -> Some omdocns
  | _ -> None

(* for XMLM itself: *)
let o = Xmlm.make_output ~nl:true ~indent:(Some 4) ~ns_prefix:ns_resolve (`Channel stdout)
let out = Xmlm.output o

(* abstract out begin/out *)
let bracket ns s p e =
    out (`El_start (tag ns s));
    p e;
    out `El_end

let abracket ns at p e =
    out (`El_start (atag ns at));
    p e;
    out `El_end

let aempty ns at = 
    out (`El_start (atag ns at));
    out `El_end

let oms s1 s2 = aempty omns ("OMS",[nameattrib s1; cdattrib s2])
let omv s = aempty omns ("OMV", [nameattrib s])

let morphism _ = failwith "morphism"

let rec taggedvar (nm, typ, def) =
   let pr (t, d) =
       (match t with None -> () | Some y -> oms "type" "MMT"; term y);
       (match d with None -> () | Some y -> oms "value" "MMT"; term y) in
   let pr2 x = 
       bracket omns "OMATP" pr x;
       omv nm in
   match (typ,def) with
   | (None, None) -> omv nm
   | _ -> bracket omns "OMATTR" pr2 (typ, def)
and context cl = bracket omns "OMBVAR" (List.iter taggedvar) cl

and term = 
    let pr (m,t) = 
        oms "morphism-application" "MMT";
        term t;
        morphism m in
    let prapp (func, args) = 
        term func;
        List.iter term args in
    let prbind (bind, ctx, t) =
        term bind;
        context ctx;
        term t in
    function
    | Top -> oms "top" "MMT"
    | Const (m,l) -> oms (locid l) (modid m)
    | Var l -> omv l
    | MorApp (m,t) -> bracket omns "OMA" pr (m,t)
    | App (func, args) -> bracket omns "OMA" prapp (func, args)
    | Bind (binder, ctx, t) -> bracket omns "OMBIND" prbind (binder, ctx, t)

let thyconst = 
    let xx l p e = abracket omdocns ("constant", [nameattrib (locid l)]) p e in
    let typ t = bracket omdocns "type" term t in
    let def t = bracket omdocns "definition" term t in
    let typdef (t1,t2) = typ t1; def t2 in
    function
    | TypedConstDefn (l, t1, t2) -> xx l typdef (t1,t2)
    | TypedConstDecl (l, t1) -> xx l typ t1
    | ConstDefn (l, t2) -> xx l def t2
    | ConstTerm l -> xx l (fun _ -> ()) ()

let assigns = function
    | StructAssign (l,m) -> 
        abracket omdocns ("strass", [nameattrib (locid l)]) morphism m
    | ConstAssign (l,t) ->
        abracket omdocns ("conass", [nameattrib (locid l)]) term t

let get_thyexpr_name = function
    | ThyName l -> Some l
    | ThyCoProduct _ | ThyPush _ -> None

let rec thystruct = function
    | ThyStruct (l, m, lb, mor) -> 
        let pr (lb, mor) = 
            (match mor with | None -> () | Some m ->
                abracket omdocns ("include",[]) morphism m);
            List.iter assigns lb in
        abracket omdocns ("structure", [nameattrib (locid l);
            attrib "name" (modid m)]) pr (lb, mor)
    | MorStruct _ -> failwith "morphism structures not translated"

and thyexpr = function
    | ThyName m -> oms (modid m) "MMT"
    | ThyCoProduct (t1,t2) -> 
        let pr (t1, t2) = thyexpr t1; thyexpr t2 in
        abracket omdocns ("theory-union",[]) pr (t1,t2)
    | ThyPush (t1, t2, m) ->
        let pr (t1, t2, m) = thyexpr t1; thyexpr t2; morphism m in
        abracket omdocns ("theory-push-along-with",[]) pr (t1,t2,m)
and thybody = function
    | ThyConst t -> thyconst t
    | ThyStructure s -> thystruct s
    | ThyInclude inc -> (match (get_thyexpr_name inc) with
        | Some n -> aempty omdocns ("include",[attrib "from" (modid n)])
        | None -> abracket omdocns ("include",[]) thyexpr inc)
    | ThyAlias l -> abracket omdocns ("open",[]) (fun x -> x) l

and thybodylist l = List.map thybody l

let thy = function
    | ThyDef(m, tl, meta) ->
        abracket omdocns ("theory", [nameattrib (locid m); metaattrib meta]) thybodylist tl
    | ThyExpr te -> thyexpr te

let thy_or_view = function
    | Thy t -> thy t
    | View _ -> failwith "can't output views"

let thy_graph e = List.iter thy_or_view e

let print md e = 
    out (`Dtd None);
    abracket omdocns (omdoc md) thy_graph e
