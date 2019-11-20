(* printers.ml *)

(* A collection of pretty-printers *)
open Syntax
module Configuration = Msl_configuration
module Options       = Msl_options


(* create judicious abstractions for common printing functions *)
module type Fmt = 
  sig 
    val f : Format.formatter 
  end

(* The rest is wrapped in a Functor, as we'll want to instantiate multiple
 * times *)

module Make(C : Configuration.Configuration)(O : Options.Options)(F : Fmt) = struct

let semi = C.semi
let equal = C.equal
let colonequal = C.colonequal
let colon = C.colon
let lbrace = C.lbrace
let rbrace = C.rbrace
let lparen = C.lparen
let rparen = C.rparen
let lbracket = C.lbracket
let rbracket = C.rbracket
let questionmark = C.questionmark
let lnumbrak = C.lnumbrak
let rnumbrak = C.rnumbrak
let tick = C.tick
let lquote = C.lquote
let rquote = C.rquote
let lescape = C.lescape
let rescape = C.rescape
let underscore = C.underscore
let leval = C.leval
let revalat = C.revalat 

let wrap_keyword s = (fst C.keyword_wrap) ^ s ^ (snd C.keyword_wrap)
let wrap_binder s  = (fst C.binder_wrap) ^ s ^ (snd C.binder_wrap)
let wrap_symbol s  = (fst C.symbol_wrap) ^ s ^ (snd C.symbol_wrap)
let wrap_format s  = (fst C.format_wrap) ^ s ^ (snd C.format_wrap)
let wrap_filename s = (fst C.string_wrap) ^ s ^ (snd C.string_wrap)
    
let needs_parens = function
  | Ident x -> is_oper x
  | Tuple _ | Record _ | Escape _ | Quote _ | Eval _ 
  | BTrue | BFalse | Let _ -> false
  | Appl _ | EqOp _ | And _ | Or _ | Not _ | Implies _ | Iff _ 
  | Selector _ | In _ | Binder _ | Desc _ | Case _ | If _ | ProofObject _ -> true

let app_lhs_parens = function
  | Appl _ -> false
  | x -> needs_parens x

let kwdquant = function
  | Forall -> C.forall 
  | Exists -> C.exists 
  | ExistsUniq -> C.exists_uniq 
  | Abs -> C.abs

let kwdchoice = function
  | Iota -> C.iota | Epsilon -> C.epsilon 

(* short-hands to use here *)
let open_box n = Format.pp_open_box F.f n
let open_hovbox n = Format.pp_open_hovbox F.f n
let open_hvbox n = Format.pp_open_hvbox F.f n
let open_vbox n = Format.pp_open_vbox F.f n
let open_hbox () = Format.pp_open_hbox F.f ()
let close_box = Format.pp_close_box F.f
let print_break = Format.pp_print_break F.f
let print_cut = Format.pp_print_cut F.f
let set_max_indent = Format.pp_set_max_indent F.f
let set_margin = Format.pp_set_margin F.f
let newline = Format.pp_print_newline F.f

let box_indent = O.box_indent

let open_list_box = function
    | Options.Reg -> open_box 0
    | Options.HoV -> open_hovbox 0
    | Options.HV -> open_hvbox 0
    | Options.V -> open_vbox 0
    | Options.H -> open_hbox ()
    
(* useful short form *)
let p = Format.pp_print_string F.f

let p_usr s = p (fst C.usr_wrap); p (C.alter_undscr s); p (snd C.usr_wrap)
 
(* Print wrapped identifier *)
let p_ident str = p (fst C.ident_wrap); p str; p (snd C.ident_wrap)
let p_keyword str = p (wrap_keyword str)
let p_binder str = p (wrap_binder str)
let p_symbol str = p (wrap_symbol str)
let p_format str = p (wrap_format str)
let p_oper = p 
 
let abs_option_match s opt = match opt with
    | Options.OBoth -> Configuration.Both s
    | Options.OLeft -> Configuration.Left s
    | Options.ORight -> Configuration.Right s
    | Options.ONeither -> Configuration.Neither s 
 
let mathrel_opt s = abs_option_match s O.mathrel
let mathop_opt s = abs_option_match s O.mathop
let mathleft_opt s = abs_option_match s O.mathleft
let mathright_opt s = abs_option_match s O.mathright 
 
let p_config = function
    | Configuration.MathRel s -> p_format (C.print_spacing (mathrel_opt s))
    | Configuration.MathOp s -> p_format (C.print_spacing (mathop_opt s))
    | Configuration.MathLeft s -> p_format (C.print_spacing (mathleft_opt s))
    | Configuration.MathRight s -> p_format (C.print_spacing (mathright_opt s))
    | Configuration.Void s -> p_format s
     
(* The following functions contains what the format uses for newlines and indents *)
type fof = { outf : (string -> int -> int -> unit) ; 
             flushf : (unit -> unit) ;
             newlinef : (unit -> unit) ;
             spacesf : (int -> unit) }
let fof = 
    let (a,b,c,d) = Format.get_all_formatter_output_functions () in
    { outf = a; flushf = b; newlinef = c; spacesf = d}

let iter_string n s1 = 
    let s2 = ref "" in
    for i = 0 to (n-1) do
        s2 := !s2 ^ s1
    done;
    !s2

let fof_newline () = 
    fof.outf C.newline 0 (String.length C.newline)
    
let fof_spaces n =
    fof.outf (iter_string n C.space) 0 (n * (String.length C.space))

let init = 
    Format.set_all_formatter_output_functions ~out:fof.outf ~flush:fof.flushf ~newline:fof_newline ~spaces:fof_spaces;; 

(* Neither of these are quite right, but it's a start *)
(* Print row
   @param pf wrap symbol function
   @param l left wrap (left bracket, quote etc)
   @param r right wrap
   @param f print function 
   @param arg print function arguments *)
let create_row pf l r f arg = 
    p (fst C.row_wrap); pf l; f arg; pf r; p (snd C.row_wrap)
let create_row2 pf l r f1 arg1 f2 arg2 = 
    p (fst C.row_wrap); pf l; f1 arg1; pf r; p (snd C.row_wrap); f2 arg2
 
(* build a common pattern to print seperators and data types *)
let p_com_list (printer:'a->unit) sep _ (y:'a list) : unit =
  let rec pl = function
    | [] -> ()
    | [x]  -> printer x
    | x::xs -> printer x; p_config sep; print_break 1 0; pl xs
  in pl y

(* A special case for theory bodies *)
let p_thy_list printer sep y =
  let rec pl = function
    | [] -> ()
    | [x]  -> printer x
    | x::xs -> printer x; p_symbol sep; print_break 1 0; pl xs
  in open_list_box Options.HV; pl y; close_box ()

(* bp = between parens *)
let bp pr s = p (fst C.row_wrap); p_symbol lparen; pr s; p_symbol rparen; p (snd C.row_wrap)

(* Inline box *)
let inbox1 pr e = open_hvbox 2; pr e; close_box ()
let inbox0 pr e = open_hbox (); pr e; close_box ()

let p_name = p

(* Return wrapped operation prefixed with ` symbol
 * @param s operation to wrap
 *) 
let showInline s = 
    let t = if is_oper s then "" else tick in
    (fst C.op_wrap) ^ t ^ s ^ (snd C.op_wrap)

let rec expr_aux e = expr e; newline ()
    
(* Build a string representation of an AST, using the standard Format module *)
and expr (e:expr) : unit = match e with
  | Ident s -> p_ident s
  | BTrue -> p_usr C.btrue
  | BFalse -> p_usr C.bfalse
  | Appl (b,f,arg) -> apply (b,f,arg) (* print binary or general application  *)
  | EqOp (e1, e2) -> inlineop C.equal e1 e2
  | In (e1, e2) -> p_atom e1; p_config C.is_in; showType e2
  | And (e1, e2) -> inlineop C.and_val e1 e2
  | Or (e1, e2) -> inlineop C.or_val e1 e2
  | Implies (e1, e2) -> inlineop C.implies e1 e2
  | Iff (e1, e2) -> inlineop C.iff e1 e2
  | Not (e) -> p_config C.not_val; expr e
  | Binder (b, v, s) -> gen_p_quali (kwdquant b) v s (* print binder Qxs *)
  | Desc (b, v, t, s) -> gen_p_quali (kwdchoice b) (VarSpec([v],Some t)) s
  | Tuple l -> if List.length l < 2 then failwith "No syntax to generate one or zero tuples exist"
               else create_row p_symbol lparen rparen p_expr_list l 
  | Record l -> create_row p_symbol lbrace rbrace p_record_list l
  | Selector (e, n) -> expr e; p_config C.dot; p_fieldname n 
  | Case (e,l) -> 
     p_keyword C.case; expr e; p_keyword C.of_val; 
     p_symbol lbrace; 
     (* must hand-print first separator, this case causes trouble for mathml *)
     print_break 0 0; p_config C.case_sep; print_break 1 0;
     case_list l; 
     p_symbol rbrace 
  | Let (i,e1,e2) -> 
    p_keyword C.let_; p_ident i; p_config equal; expr e1; p_keyword C.in_; expr e2
  | Quote e -> create_row p_symbol lquote rquote expr e 
  | Escape e -> create_row p_symbol lescape rescape expr e 
  | Eval (e,t) -> create_row2 p_symbol leval revalat expr e showType t
  | If(b, e1, e2) -> p_config C.ifs; expr b; p_config C.thens; expr e1; 
      p_config C.elses; p_atom e2; 
  | ProofObject script -> p script;
    
(* this needs to learn about operator precedence! *)
and inlineop op e1 e2 = 
    open_hbox ();
    bp expr e1; 
    p_config op; 
    print_break 0 2;
    bp expr e2;
    close_box ();
    
(* Print binder 
 @param v list of bound variables 
 @param s MathScheme type*)
and gen_p_quali quali_s (VarSpec(v,s)) e =
    open_hovbox box_indent;
    p_binder quali_s;
    p_var_list v;
    begin match s with 
    | None    -> ()
    | Some s0 -> p_config C.quali_sep1; showType s0
    end;
    p_config C.quali_sep2; print_break 0 0;
    expr e;
    close_box()
           
(* generic printer for ExprApp; need a thunk to prevent evaluation *)
and gen_p_app e pr = p_name e; print_break 1 0; pr ()
      
and p_atom e = if (needs_parens e) then bp expr e else expr e
and p_app_lhs e = if (app_lhs_parens e) then bp expr e else expr e

and apply = function
  | (b,Ident(o),Tuple(e)) when b -> begin
      match e with
      | [e1;e2] ->
          open_box 2; p_atom e1; print_break 1 0; 
          p (showInline o); print_break 1 0; 
          p_atom e2; close_box ()
      | _ -> failwith "Inline BinOp should have 2 args"
      end
  | (_,a,e) ->
      open_hbox (); p_app_lhs a; print_break 1 2; p_atom e; close_box ()

(* Print apply for parameters declaration *)
and gapply e = 
   let pr = function PConst e1 -> p_name e1
           | PUniOp(f,e) -> (p_name f;  bp p_var_list [e])
           | PApp(e1,b,e2) -> 
               let l = List.length e2 in
               if l < 2 then failwith "No syntax to generate one or zero tuple parameter functions exist"
               else (if b && (l == 2) then
                   (p_ident (List.hd e2); print_break 1 0; 
                    p_ident (showInline e1); print_break 1 0; 
                    p_ident (List.hd (List.tl e2)))
               else (p_name e1; bp p_var_list e2))
           in
    inbox1 pr e

and p_case (Branch(f, e)) =
    p_pat f; p_config C.arrow2; expr e
(* Print pattern *)
and p_pat = function
    | PatNone -> p_symbol underscore
    | PatIdent i -> p_name i
    | PatConst i -> p_name i
    | PatTuple t -> create_row p_symbol lparen rparen p_pat_list t
    | PatRecord r -> create_row p_symbol lbrace rbrace p_pat_record_list r 
    | PatApp(p1, p2) -> p_pat p1; print_break 1 0; p_pat p2
and p_record (FieldMem (i, oty, e)) = 
    p_fieldname i;
    begin match oty with
    | None -> ()
    | Some ty -> p_config C.colon; showType ty
    end;
    p_config C.equal; expr e
    
and p_var_list vl = p_com_list p_ident C.list_sep O.default vl
and p_expr_list x = p_com_list p_atom C.list_sep O.exprs x
and p_pat_list x = p_com_list p_pat C.list_sep O.exprs x
and p_ren_list x = 
    p_com_list (fun (e1,e2) -> p_ident e1; p_config C.arrow1; p_ident e2) C.list_sep O.default x
and p_subst_list x =
    p_com_list (fun (Subst(e1,e2)) -> p_ident e1; p_config C.arrow1; expr e2) C.list_sep O.default x
and p_type_list tl = p_com_list showType C.list_sep O.types tl
and showThyIdentList tl = p_com_list (fun (x,y) -> p x; p_config C.colon; p y) C.list_sep O.default tl
and p_record_list rl = p_com_list p_record C.list_sep O.default rl
and case_list l = p_com_list p_case C.case_sep O.default l
(* @param e pattern *)
and p_pat_record (i, e) = p_name i; p_config C.equal; p_pat e
and p_pat_record_list rl = p_com_list p_pat_record C.list_sep O.default rl

and showConstrList tl = p_com_list p_field_sig C.bar O.default tl
and showTRecordList tl = p_com_list p_field_sig C.list_sep O.default tl
and p_field_sig (FieldSig(name, type_expr)) = 
    open_hbox ();
    p_fieldname name; p_config C.colon; showType type_expr;
    close_box ()

and showType = function
    | Type -> p_keyword C.type_val1
    | TId  i -> p_usr i
    | TLift x -> bp (fun () -> p_config C.lift; p_atom x) () (* print expression lifted as a type  *)
    | TDepId (i,t) -> bp (fun (ii, tt) -> p_usr ii; p_config colon; showType tt) (i,t)
    | TApp (x,y) -> inbox0 (fun () -> showType x; print_break 1 0; bp showType y) ()
    | TProd t -> inbox0 (bp p_type_list) t
    | TArrow (t1,t2) ->
      (* To properly display expressions such as U -> (U -> V) -> U *)
      let showArrowType tc = (match tc with
      | TArrow (_,_) | TInduct _ | TLift _ | TBinder _ | TPredicate _ -> create_row p_symbol lparen rparen showType tc
      | Type | TId _ | TApp (_,_) | TProd _ | TDepId _ 
      | TTheory _ | TTypeFromTheory _ | TProof _ 
      | TPower _ | TRecord _ -> showType tc)
      in
      open_box 2;
      showArrowType t1;
      p_config C.arrow2;
      print_break 0 0;
      showArrowType t2;
      close_box ()
    | TInduct (v,t) ->
        bp (fun vv -> open_hovbox box_indent; 
                      p_keyword C.data; p_usr vv; p " ."; print_break 1 0;
                      showConstrList t; close_box ()) v
    | TTheory i -> p_symbol C.ampersand; p_usr i
    | TTypeFromTheory t -> p_symbol C.type_from; p_symbol lparen; p_usr  t; p_symbol rparen
		| TProof fm -> p_symbol "ProofOf"; p_symbol lparen; (expr fm);  p_symbol rparen
    | TPredicate t -> 
        (* To properly display unary predicates *)
        (match t with
        | TProd _ | TDepId _ -> p_symbol lparen; showType t; p_symbol questionmark; p_symbol rparen
        | Type | TArrow (_,_) | TId _ | TApp (_,_) | TTheory _
        | TPower _ | TInduct _ | TPredicate _ | TRecord _ | TTypeFromTheory _ | TProof _ 
        | TLift _ | TBinder _ -> 
            create_row p_symbol lparen rparen showType t; p_symbol questionmark)
    | TPower t -> p_keyword C.power; (match t with
        | Type | TId _ | TDepId _ -> showType t
        | TArrow (_,_) |  TApp (_,_) | TProd _ | TTheory _
        | TPower _ | TInduct _ | TPredicate _ | TRecord _ | TTypeFromTheory _ 
        | TProof _ | TLift _ | TBinder _ -> 
            create_row p_symbol lparen rparen showType t)
    | TRecord l -> create_row p_symbol lbrace rbrace showTRecordList l
    | TBinder (vs, tp) -> p_tbinder vs tp
    
and p_tbinder (VarSpec(v,s)) t =
    p_binder "Lambda ";
    p_var_list v;
    begin match s with 
    | None    -> ()
    | Some s0 -> p_config C.quali_sep1; showType s0
    end;
    p_config C.quali_sep2;
    showType t;
           
and showTIdent t :unit = match t with
  | TBase (s,{kind=t; defn = NoDefn}) -> gen_p_type (fun () -> p_name s) t
  | TBase (s,{kind=_; defn = SubType t}) -> 
      open_box 0; p_name s; p_config C.colon_lt; showType t; close_box()
  | TBase (s,{kind=_; defn = Manifest t}) -> 
      open_box 0; p_keyword C.type_val2; p_name s; p_config C.equal; showType t; close_box()
  | TExtension (s,t) -> gen_p_type (fun () -> p_var_list s) t
and showTIdentList tl = p_com_list showTIdent C.list_semi O.concepts tl
and showTIdentList2 tl = p_com_list showTIdent C.list_sep O.variables tl

(* Generic printer for type declaration *)
and gen_p_type pr t = inbox1 (fun x -> pr (); p_config colon; showType x) t
         
and p_funcdefn f = inbox1 (fun x -> gapply (fst x); p_config C.equal; p_atom (snd x)) f
and p_funcdefn_list l = p_com_list p_funcdefn C.list_semi O.functions l

and p_fieldname = p

(* printer for pseudo_app, which is just a list of names *)
and p_pseudo_app = function
  | []   -> ()
  | x::xs -> p x; List.iter (fun y -> p_symbol "/"; p y) xs

let rec decl (e:declaration) :unit = match e with
  | TypDecl t -> inbox1 showTIdent t
  | FuncDecl t -> p_funcdefn t
  | Axiom x -> gen_p_axiom x
  | VarDecl vl -> 
      open_hovbox box_indent; 
      p_keyword C.variable; 
      showTIdentList2 vl; 
      close_box()
   | Induct (v, t) ->
      p_keyword C.inductive; p_usr v; p_config C.bar; inbox1 showConstrList t

and thy_list (tl:declaration list) = p_thy_list decl semi tl

(* Generic printer for axiom declaration *)
and gen_p_axiom (id,e,b) =
    open_hvbox box_indent;
    p_keyword (if b then C.axiom else C.theorem);
    (match id with
    | Some x -> p_name x
    | None   -> () );
    p_config C.colon;
    print_break 0 0;
    expr e;
    close_box()

and p_ax_list l = p_com_list gen_p_axiom C.list_semi O.facts l
(* Generic printer for theory declaration *)
and gen_p_thy e =
    p_keyword C.theory;
    p (fst C.row_wrap);
    p_symbol lbrace;
    print_break 1 0;
    thy_list e;
    print_break 1 0;
    p_symbol rbrace;
    p (snd C.row_wrap);

and theory_expr_list l = p_com_list gen_p_thy C.list_sep O.theory_exprs l

and aseq l = p_com_list p_usr C.list_semi O.default l
and arrow = function
  | ArrowName n -> p_usr n
  | ArrowId -> p " Id "
  | ASeqComp (x,y,l) -> bp aseq (x::y::l)
  | AParComp (a1,a2) -> p_usr a1; p " || "; p_usr a2
  | AInstance(a,b,v) -> p_keyword C.instance;
      p_usr a; p_keyword C.of_val; p_usr b; 
      p_keyword C.via; create_row p_symbol lbracket rbracket p_subst_list v
  | AExtend (init,flag,t) ->
    open_hbox ();
    p_usr init;
    print_break 1 0;
    p_keyword (match flag with General -> C.ext_by 
                             | Conservative -> C.ext_con_by);
    p (fst C.row_wrap);                  
    p_symbol lbrace;
    close_box ();
    print_cut ();
    thy_list t;
    p_symbol rbrace;
    p (snd C.row_wrap);
  | ACombine (e, e2) ->
    open_hvbox 2;
    p_keyword C.combine;
    p_var_list e;
    print_break 1 0;
    p_keyword C.along;
    p_usr e2;
    close_box()
  | ARename(e1, sl) -> p_rename (e1,sl)
    (* open_hovbox 2;
    p_usr e1;
    if (not (sl == [])) then (fun sl -> create_row p_symbol lbracket rbracket p_ren_list sl) sl;
    close_box() *)
  | AThy t -> gen_p_thy t
  | AMixin (a,b) ->
    open_hvbox 2;
    p_keyword C.mixin;
    p_com_list p_rename C.list_sep O.default [a;b];
    close_box()

and p_rename (e, sl) = 
    open_hovbox 2;
    p_usr e;
    if (not (sl == [])) then (fun sl -> create_row p_symbol lbracket rbracket p_ren_list sl) sl;
    close_box()

and assign = function 
  | NamedArrow(n,a) ->
      open_hvbox box_indent; p_usr n; p_config colonequal; arrow a; close_box()
  | NamedSubst(n,s) ->
      open_hvbox box_indent; p_usr n; p_config colonequal; 
      create_row p_symbol lbracket rbracket p_subst_list s;
      close_box()

let p_top (e:toplevel_expr) m =
  let rec pr = function
    | [] -> ()
    | [x]  -> assign x; 
    | x::xs -> assign x; print_break 1 0; pr xs
  in
    set_margin m;
    set_max_indent (6*4); 
    open_vbox 0;
    pr e;  
    close_box ()

end

module Direct = struct
    module M = Make(Configuration.ASCII)(Options.StdOpt)
                   (struct let f = Format.std_formatter end)
    let print e = (M.p_top e 79; Format.pp_print_flush Format.std_formatter () )
end
    
module String = struct
    module M = Make(Configuration.ASCII)(Options.StdOpt)
                   (struct let f = Format.str_formatter end)
    let print e = (M.p_top e 79; Format.flush_str_formatter () )
end ;;
