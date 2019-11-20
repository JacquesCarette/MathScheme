(* Takes a library (given mostly as a set of arrow definitions) and "expands" 
 * these definitions to make the underlying theories explicit.
 *
 * This is really sanity-checking code, to ensure that we can have a 
 * reasonable semantics for our syntax.
 *
 *)

open Syntax
open Bindings
open Library

module SM = Util.StringMap

type ground = Grounded of bindings | Ungrounded of arrow_def

(* local function for dealing with exceptional case of expanding a 
 * theory which 'depends' on a sub-theory which is in fact an ungrounded
 * arrow.  It is expected that as the data-structures evolve, this function
 * will become obsolete.  *)
let check = function
  | Grounded t -> t
  | Ungrounded _ -> failwith "Got an ungrounded theory in expansion"

(* Combine -- implements 'combine ___ along _ ' functionality.
 * This assumes that all input theories are expanded.
 * Algorithm:
     * 1. compute the set of 'along' name declarations (easy)
     * (1.5 find all the arrows from 'along' into each of the theories)
     * 2. create the set of all names in the theories to combine
     *      do not insert any of the 'along' stuff
     * 3. iterate over all found, renaming as needed
     *
     * The axioms and types are the only
     * things we need to worry about.
     *
     * Have to be careful to first figure out all that needs to be done
     * (i.e. renamed) before inserting anything, as some of the 'unique'
     * names may depend on items that need renaming.
*)

(* Find the 'duplicates' over 'over' in list 'lst' of bindings. *)
let find_dups_in_tbl over lst =
    (* the 'along' bindings *)
    let a = Array.of_list lst in
    let rest = Hashtbl.create (10*(List.length lst)) in
    let insert i x = if not (SM.mem x over) then Hashtbl.add rest x i in
    let treat_tbl i h = SM.iter (fun k _ -> insert i k) h in
    Array.iteri treat_tbl a;
    let syms = Hashtbl.fold (fun k _ l -> k::l) rest [] in
    let syms = Util.uniq (List.sort compare syms) in
    let symb_loc = List.map (fun x -> (x, Hashtbl.find_all rest x)) syms in
    symb_loc

(* remember substitutions *)
let rememb (a:(name*name) list array) (d:name) (indices:int list) : unit =
    let ren = Nameext.extend in
    List.iter (fun i -> a.(i) <- ren d :: a.(i)) indices

(* create some 'object' to deal with types and expressions uniformly 
 * 'a is the bundle type, 'b is the raw type/expression *)
type 'a ast = { find : bindings -> name -> 'a;
                 ren : Subst.substitution -> 'a -> 'a;
              }

let symb_ast = 
  {find = (fun x y -> SM.find y (get_symb x)); 
   ren = Subst.ren_typrecord }

let var_ast = 
  {find = (fun x y -> SM.find y (get_vars x)); 
   ren = Subst.ren_type}

let defn_ast = 
  {find = (fun x y -> SM.find y (get_defns x)); 
   ren = Subst.ren_defn}

let prop_ast = 
  {find = (fun x y -> SM.find y (get_props x)); 
   ren = Subst.ren_axiom}

let fields_ast =
  {find = (fun x y -> SM.find y (get_fields x)); 
   ren = Subst.ren_fields}

(* This is 'almost' List.partition, but it applies an unwrapping
 * on the left list *)
let split_singletons l = 
    let rec doit (others,singles) = function
    | []    -> (others, singles)
    | (_,[])::_ -> failwith "defined local with no source location"
    | (a,[x])::xs -> doit (others, (a,x)::singles) xs
    | (a,y)::xs -> doit ((a,y)::others, singles) xs in
    doit ([],[]) l

(* combine all of bl (over 'along') into b, taking care of ren and dup *)
let combine lib (along:bindings) (bl:bindings list) name =
    let dups get = find_dups_in_tbl (get along) (List.map get bl) in
    let symbloc = dups get_symb in
    let varloc = dups get_vars in
    let defnloc = dups get_defns in
    let proploc = dups get_props in
    let fieldsloc = dups get_fields in
    let (defn_subst, defn_copy) = split_singletons symbloc in
    let (var_subst, var_copy) = split_singletons varloc in
    let (func_subst, func_copy) = split_singletons defnloc in
    let (prop_subst, prop_copy) = split_singletons proploc in
    let (fields_subst, fields_copy) = split_singletons fieldsloc in
    (* figure out all the needed renamings, and remember them *)
    let name_arr = Array.make (List.length bl) [] in
    List.iter (fun (d,l) -> rememb name_arr d l) defn_subst;
    List.iter (fun (d,l) -> rememb name_arr d l) var_subst;
    List.iter (fun (d,l) -> rememb name_arr d l) prop_subst;
    (* No need to do this for functions as they are already treated above
     * as all functions should get declared-before-use
     * List.iter (fun (d,l) -> rememb name_arr d l) func_subst; *)
    let subst_arr = Array.init (List.length bl) 
                    (fun i -> Subst.from_namelist name_arr.(i)) in
    let b = along in
    (* conditionally merge bl into b, taking care of renaming along the way *)
    let a = Array.of_list bl in
    (* the copies might need to be renamed too! *)
    let copy ast (x,i) tbl =
        let nx = Subst.rename_name subst_arr.(i) x in
        let nt = ast.ren subst_arr.(i) (ast.find (a.(i)) x) in
        map_add name nx nt tbl in
    let nt = List.fold_right (copy symb_ast) defn_copy b.symbols in
    let nv = List.fold_right (copy var_ast) var_copy b.vars in
    let nf = List.fold_right (copy defn_ast) func_copy b.defns in
    let na = List.fold_right (copy prop_ast) prop_copy b.props in
    let ni = List.fold_right (copy fields_ast) fields_copy b.fields in
    (* this adds renamed versions of the items that needed duplicating *)
    let rename ast (x,l) t = List.fold_right ( fun i tbl -> 
        let nx = (Subst.rename_name subst_arr.(i) x) in
        let nt = ast.ren subst_arr.(i) (ast.find a.(i) x) in
        (map_add name nx nt tbl)) l t in
    let nt2 = List.fold_right (rename symb_ast) defn_subst nt in
    let nv2 = List.fold_right (rename var_ast) var_subst nv in
    let nf2 = List.fold_right (rename defn_ast) func_subst nf in
    let na2 = List.fold_right (rename prop_ast) prop_subst na in
    let ni2 = List.fold_right (rename fields_ast) fields_subst ni in
    (lib, Grounded {symbols = nt2; vars = nv2; defns = nf2; 
                    props = na2; fields = ni2})

(**
 * Look up a theory binding in the theories part of a library
 * 
 * @param lib :  A library
 * @param nm  :  The name of theory binding to fetch               
 * @return    : The name of the theory binding if found,
 *              otherwise None.  
 *)
let fetch lib nm = 
    try
        Some (SM.find nm lib.theories)
    with 
    | Exceptions.Unnamed _ -> None
    | Not_found -> None

let add_expanded lib k v =
    Log.log (Printf.sprintf "%s expanded (into lib %s)\n" k lib.lname);
    {lib with theories = SM.add k v lib.theories}

(**
 * Expands a theory combination
 * 
 * @param lib  : The library
 * @param name : The name of the theory (on the lhs) 
 * @param el   : The list of theory to combine                
 * @param e    : The theory to substract over
 * 
 * @return     : An updated library
 *)
(* This does the actual expansion, relying on some tables being
 * pre-populated.  Gives a new library as result *)
let rec expand_combine lib name (el,e) =
    let check_cons x = Util.cons (check x) in
    let (nl, along) = expand_myself lib e in
    let (nl2, thys) = Util.fold_left2 (expand_myself, check_cons) (nl,[]) el in
    combine nl2 (check along) thys name
and expand_named targ lib n = expand_bindings lib targ (lookup_arrow lib n)
and expand_myself lib n = expand_named n lib n

(* pullback of a||b where 'base' is pre-computed *)
and pullback lib nam a b base = 
    Log.log ("doing pullback "^nam^"\n");
    let (nl, eb) = expand_myself lib base in
    (* (TODO) we should check that a and b do not interfere *)
    let aa = lookup_arrow lib a and bb = lookup_arrow lib b in
    match eb with
    | Grounded t -> 
      ( let t1 = perform lib (a,aa) t in
        let t2 = perform lib (b,bb) t1 in
        (nl, Grounded t2) )
    | Ungrounded _ -> failwith "cannot do pullback over ungrounded theory"

and unravel lib nam x xs = 
    Log.log ("unraveling sequence "^nam^"\n");
    let (nl, start) = expand_myself lib x in
    match start with
    | Grounded thy -> 
         (nl, Grounded (List.fold_right (perform_named lib) xs thy))
    | Ungrounded _ -> failwith "cannot unravel ungrounded seq."
and perform_named lib nam base : bindings = 
    perform lib (nam,SM.find nam lib.arrows) base
(* 'perform's an extension.  This should check that the extension can
 * indeed be done onto the given 'base' (TODO).  Note that this is not
 * a recursive process. *)
and perform lib (name,ext) (base:bindings) = match ext with
  | AThy _ -> failwith ("Cannot 'perform' a base Theory "^name)
  | ACombine _ -> failwith "Cannot 'perform' a combine"
  | AMixin _ -> failwith "Cannot 'perform' a mixin"
  | ARename (_,ren) ->  (* TODO this is not right *)
      (* Does the actual renaming *)
      Subst.thy_rename (Subst.from_substlist ren) (copy_bindings base)
  (* Expand a theory extension *)
  | AExtend ( _, _, ext) ->
       let e = empty_pre_bindings () in
       add_pre_into_bindings (Track.tr_decl name e ext) base
  | AInstance _ -> failwith "How to 'perform' an instance?"
  (* Expand a theory application *)
  | ArrowName _ -> failwith "perfom a named arrow?"
  | AParComp _ -> failwith "perform a parallel composition?"
  | ASeqComp (_,y,l) -> (* for now, assume base == x,
    typechecking will catch problems 'later' anyways *)
      let nb = perform_named lib y base in
      List.fold_right (fun y -> perform_named lib y) l nb
  | ArrowId -> failwith "perform identity?"

(**
 * Takes a 'binding' (name will surely change), and for the ones which
 * correspond to theories, 'expand' them.  Expanding really means that
 * theories are 'flattened' (thus the name of the module) into what would
 * normally be done in a first-order setting.
 * 
 * @param lib :  A library
 * @param nam :  A target name
 * @param bb  :  A theory binding              
 *
 * @return    : 
 *)   
(* returns a copy as necessary *)
and expand_bindings lib nam (bb:arrow) : library * ground =
  (* If the theory binding is already expanded, don't need to do anything, just return it*)
  match fetch lib nam with | Some t -> (lib, Grounded t) | None ->  
  (let (nl,result) = (match bb with
  (* We don't have to expand a base binding *)
  | AThy dl -> let r =  Track.tr_decl nam (empty_pre_bindings ()) dl in
               (lib, Grounded(expand_base r))
  (* Expand a theory combination *)
  | ACombine (lst,over) -> 
      Log.log ("Expanding combination "^nam^"\n");
      expand_combine lib nam (lst,over)
  | AMixin (r1,r2) ->
      Log.log ("Expanding mixin "^nam^"\n");
      cartesian_lift lib r1 [r2]
  (* Expand a theory extension *)
  | AExtend (orig, _, _) ->
      Log.log ("Extending from "^orig^" into "^nam^"\n");
      let (nl, res) = expand_myself lib orig in
      let exp_r = check res in
      (nl, Grounded (perform lib (nam,bb) exp_r )
           (* {name = name;
            types = SM.fold SM.add ext.types exp_r.types;
            functions = SM.fold SM.add ext.functions exp_r.functions;
            variables = SM.fold SM.add ext.variables exp_r.variables;
            axioms = SM.fold SM.add ext.axioms exp_r.axioms;
            }*))
  | AInstance _ -> (lib, Ungrounded (nam,bb))
  | ArrowName nnn -> 
      Log.log ("Expanding named arrow "^nnn^"\n");
      expand_myself lib nnn
  (* Expand a theory renaming -- should be an arrow transformer *)
  | ARename (nnn,ren) -> 
      Log.log ("Renaming from "^nnn^" into "^nam^"\n");
      (* Look up the theory in the library and expand it *)
      let (nl, res) = expand_myself lib nnn in
      (* Does the actual renaming *)
      let newr = copy_bindings (check res) in
      (nl, Grounded(Subst.thy_rename (Subst.from_substlist ren) newr))
  | ArrowId -> (lib, Grounded (empty_bindings ()))
  | ASeqComp (x,y,l) -> unravel lib nam x (y::l)
  | AParComp (a,b) -> let base = Arrow.base lib bb in pullback lib nam a b base) in
  match result with
  | Grounded nb  -> (add_expanded nl nam nb, result)
  | Ungrounded _ -> 
    (Log.log ("Result of performing arrow "^nam^" was ungrounded\n"); (nl, result)) )

and expand_named_bindings nam (bb:arrow) lib = fst (expand_bindings lib nam bb)

(* expand_base just goes from pre-bindings to bindings *)
and expand_base r = extract_bindings r

and ren_then_perform lib ((name,ren),arr) base =
    let b1 = perform lib (name,ARename(name,ren)) base in
             perform lib (name,arr) b1
(* Cartesian Lift takes a view (which can be an extension),
   and a list of general extensions. *)
and cartesian_lift lib view_nam ext_nams =
    let arrows = List.map (fun x -> (x,lookup_arrow lib (fst x))) ext_nams in
    let view_arr = lookup_arrow lib (fst view_nam) in
    List.iter (fun (_,y) -> Checkthy.genext lib y) arrows; 
    let base = Arrow.base lib view_arr in
    let view = perform lib (base, lookup_arrow lib base) (empty_bindings ()) in
    let b = List.fold_right (fun arr b -> ren_then_perform lib arr b) arrows view in
    (* TODO: not memoized, will slow things down *)
    (lib, Grounded b)
(**
 * Expands a library (i.e. concretize arrows)
 * @param lib : The input library               
 * @return    : The expanded library
 *)
let expand_top lib = SM.fold expand_named_bindings lib.arrows lib

