open Syntax
open Printers

let rename x =
  x ^ x
;;

let rec conflict x = function
  |Ident y -> y=x
  |BTrue -> false
  |BFalse -> false
  |EqOp (e1,e2) -> (conflict x e1)||(conflict x e2)
  |In (e1,comp) -> conflict x e1
  |And (e1,e2) -> (conflict x e1)||(conflict x e2)
  |Or (e1,e2) -> (conflict x e1)||(conflict x e2)
  |Not e1 -> conflict x e1
  |Iff (e1,e2) -> (conflict x e1)||(conflict x e2)
  |Implies (e1,e2) -> (conflict x e1)||(conflict x e2)
  |Appl (b,e1,e2) -> (conflict x e1)||(conflict x e2)
  |Let (y,e1,e2) -> y<>x && ((conflict x e1) || (conflict x e2))
  |Binder (q,VarSpec ((z::zs), comp_opt),e1) -> 
      z <> x && conflict x e1
  |Binder (q,VarSpec ([], comp_opt),e1) -> conflict x e1
  |Desc (c,id,comp,e) -> id=x || conflict x e
  |Tuple l -> List.exists (conflict x) l 
  |Record l -> 
    let check_fieldMem_conflict = function
      |FieldMem (f,comp_opt,e) -> if (conflict x e) then true else false
    in List.exists (check_fieldMem_conflict) l
  |Selector (e,f) -> conflict x e
  |Case (e,l) -> conflict x e
  |If (e1,e2,e3) -> (conflict x e1) || (conflict x e2) || (conflict x e3)
  |Escape e -> conflict x e
  |Quote e -> conflict x e
  |Eval (e,comp) -> conflict x e
  |ProofObject s -> false
;;

let rec alpha x = function
  |Ident y -> if y = x then Ident (rename y) else Ident y
  |BTrue -> BTrue
  |BFalse -> BFalse
  |EqOp (e1,e2) -> EqOp ((alpha x e1),(alpha x e2))
  |In (e1,comp) -> In ((alpha x e1),comp)
  |And (e1,e2) -> And ((alpha x e1),(alpha x e2))
  |Or (e1,e2) -> Or ((alpha x e1),(alpha x e2))
  |Not e1 -> Not (alpha x e1)
  |Iff (e1,e2) -> Iff ((alpha x e1),(alpha x e2))
  |Implies (e1,e2) -> Implies ((alpha x e1),(alpha x e2))
  |Appl (b,e1,e2) -> Appl (b,(alpha x e1),(alpha x e2))
  |Let (y,e1,e2) ->
    if y = x then Let ((rename y),(alpha y e1),(alpha y e2))
    else Let (y,(alpha x e1),(alpha x e2))
  |Binder (q,VarSpec (l, comp_opt),e1) -> 
    let alpha_id_list y = if y = x then rename y else y in 
    let new_spec = VarSpec ((List.map alpha_id_list l),comp_opt) in
    Binder (q,new_spec,(alpha x e1))
  |Desc (c,id,comp,e) -> 
    if id = x then Desc (c,(rename id),comp,(alpha x e))
    else Desc (c,id,comp,(alpha x e)) 
  |Tuple l -> Tuple (List.map (alpha x) l)
  |Record l -> 
    let alpha_fieldMem = function
      |FieldMem (f,comp_opt,e) -> FieldMem (f,comp_opt,(alpha x e)) 
    in Record (List.map alpha_fieldMem l)
  |Selector (e,f) -> Selector ((alpha x e),f)
  |Case (e,l) -> Case ((alpha x e),l)
  |If (e1,e2,e3) -> If ((alpha x e1),(alpha x e2),(alpha x e3))
  |Escape e -> Escape (alpha x e)
  |Quote e -> Quote (alpha x e)
  |Eval (e,comp) -> Eval ((alpha x e),comp)
  |ProofObject s -> ProofObject s
;;

let rec subst x e = function
  |Ident y -> if y = x then e else Ident y
  |BTrue -> BTrue
  |BFalse -> BFalse
  |EqOp (e1,e2) -> EqOp ((subst x e e1),(subst x e e2))
  |In (e1,comp) -> In ((subst x e e1),comp)
  |And (e1,e2) -> And ((subst x e e1),(subst x e e2))
  |Or (e1,e2) -> Or ((subst x e e1),(subst x e e2))
  |Not e1 -> Not (subst x e e1)
  |Iff (e1,e2) -> Iff ((subst x e e1),(subst x e e2))
  |Implies (e1,e2) -> Implies ((subst x e e1),(subst x e e2))
  |Appl (b,e1,e2) -> Appl (b,(subst x e e1),(subst x e e2))
  |Let (y,e1,e2) -> 
      let exp1 = subst x e e1 in
      if y = x then let newExp = alpha y e2 in Let ((rename y), exp1, newExp) 
      (* if y =x, newExp will not include x *)
      else let exp2 = subst x e e2 in Let (y, exp1, exp2)
  |Binder (q,VarSpec (l, comp_opt),e1) ->  
    let subst_id y = 
      if y=x then y 
      else begin
        if (conflict y e) then rename y else y (* alpha y e1 *)
      end
    in let new_list = List.map subst_id l in 

    let rec alpha_e1 = function
    |[] -> Binder (q,VarSpec(new_list,comp_opt), (subst x e e1))
    |y::tail -> 
      if y=x then Binder (q,VarSpec(new_list,comp_opt), (subst x e e1))
      else begin
        if (conflict y e) then 
          let newExpr = alpha y e1 in 
          Binder (q,VarSpec(new_list,comp_opt),(subst x e newExpr))
        else alpha_e1 tail
      end
    in alpha_e1 l
  |Desc (c,id,comp,e1) -> Desc (c,id,comp,(subst x e e1))
  |Tuple l -> Tuple (List.map (subst x e) l)
  |Record l -> 
    let subst_fieldMem = function
    |FieldMem (f,comp_opt,e1) -> FieldMem (f,comp_opt,(subst x e e1)) 
    in Record (List.map subst_fieldMem l)
  |Selector (e1,f) -> Selector ((subst x e e1),f)
  |Case (e1,l) ->                      
    let rec matchExpr = function
    |[] -> []
    |Branch(p,e1)::tail -> Branch(p,subst x e e1)::(matchExpr tail)
  in Case((subst x e e1), matchExpr l)
  |If (e1,e2,e3) -> If ((subst x e e1),(subst x e e2),(subst x e e3))
  |Escape e1 -> Escape (subst x e e1)
  |Quote e1 -> Quote (subst x e e1)
  |Eval (e1,comp) -> Eval ((subst x e e1),comp)
  |ProofObject s -> ProofObject s
;;

let isExprInPattern env e p = 
  match e,p with
  |_,PatNone -> false
  |_,PatIdent x -> true
  |Ident id, PatConst x -> if (id = x) then true else false 
  |Tuple l1, PatTuple l2 -> true
  |Record l1, PatRecord l2 -> true
  |Appl (b,e1,e2), PatApp (p1,p2) -> true
  |_,_ -> false
;;

let rec record_field_selector f = function
  |[] -> failwith "the field does not exist"
  | FieldMem (f2,comp_opt,e)  :: tail -> 
      if f = f2 then e
      else record_field_selector f tail 
;;

let rec conflict_comp x = function
  |Type -> false
  |TId y -> y=x
  |TApp (comp1,comp2) -> (conflict_comp x comp1)||(conflict_comp x comp2)
  |TProd l -> List.exists (conflict_comp x) l
  |TArrow (comp1,comp2) -> (conflict_comp x comp1)||(conflict_comp x comp2)
  |TPower comp1 -> conflict_comp x comp1
  |TInduct (s,l) -> 
    let conflict_induct = function
      |FieldSig(f,comp1) -> (conflict_comp x comp1)
    in List.exists conflict_induct l
  |TPredicate comp1 -> conflict_comp x comp1
  |TRecord l -> 
    let conflict_trecord = function
    |FieldSig(f,comp1) -> conflict_comp x comp1
    in List.exists conflict_trecord l
  |TDepId (s,comp1) -> conflict_comp x comp1
  |TLift e -> false
  |TTheory s -> false
  |TTypeFromTheory s -> false
  |TProof e -> false
  |TBinder(VarSpec((z::zs),comp_opt),comp1) -> z<>x && conflict_comp x comp1
  |TBinder(VarSpec([],comp_opt),comp1) -> conflict_comp x comp1

;;
let rec alpha_comp x = function
  |Type -> Type
  |TId y -> if y = x then TId (rename y) else TId y
  |TApp (comp1,comp2) -> TApp ((alpha_comp x comp1),(alpha_comp x comp2))
  |TProd l -> TProd (List.map (alpha_comp x) l)
  |TArrow (comp1,comp2) -> TApp ((alpha_comp x comp1),(alpha_comp x comp2))
  |TPower comp1 -> TPower (alpha_comp x comp1)
  |TInduct (s,l) -> 
    let alpha_induct = function
      |FieldSig(f,comp1) -> FieldSig(f,(alpha_comp x comp1))
    in TInduct (s,(List.map alpha_induct l))
  |TPredicate comp1 -> TPower (alpha_comp x comp1)
  |TRecord l -> 
    let alpha_trecord = function
    |FieldSig(f,comp1) -> FieldSig(f,(alpha_comp x comp1))
    in TRecord (List.map alpha_trecord l)
  |TDepId (s,comp1) -> TDepId (s,(alpha_comp x comp1))
  |TLift e -> TLift e
  |TTheory s -> TTheory s
  |TTypeFromTheory s -> TTypeFromTheory s
  |TProof e -> TProof e
  |TBinder(VarSpec(l,comp_opt),comp1) -> 
    let alpha_id_list y = if y = x then rename y else y in 
    let new_spec = VarSpec ((List.map alpha_id_list l),comp_opt) in
    TBinder (new_spec,(alpha_comp x comp1))
;;

let rec subst_comp x comp = function
  |Type -> Type
  |TId y -> if y = x then comp else begin
    if (conflict_comp y comp) then TId (rename y) (* rename Var y*)
    else TId y
  end 
  |TApp (comp1,comp2) -> TApp ((subst_comp x comp comp1),(subst_comp x comp comp2))
  |TProd l -> TProd (List.map (subst_comp x comp) l)
  |TArrow (comp1,comp2) -> TApp ((subst_comp x comp comp1),(subst_comp x comp comp2))
  |TPower comp1 -> TPower (subst_comp x comp comp1)
  |TInduct (s,l) -> 
    let subst_induct = function
      |FieldSig(f,comp1) -> FieldSig(f,(subst_comp x comp comp1))
    in TInduct (s,(List.map subst_induct l))
  |TPredicate comp1 -> TPredicate (subst_comp x comp comp1)
  |TRecord l -> 
    let subst_trecord = function
    |FieldSig(f,comp1) -> FieldSig(f,(subst_comp x comp comp1))
    in TRecord (List.map subst_trecord l)
  |TDepId (x,comp1) -> TDepId (x,(subst_comp x comp comp1))
  |TLift e -> TLift e
  |TTheory s -> TTheory s
  |TTypeFromTheory s -> TTypeFromTheory s
  |TProof e -> TProof e
  |TBinder(VarSpec(l,comp_opt),comp1) -> 
    let subst_id y = 
      if y=x then y 
      else begin
        if (conflict_comp y comp) then rename y else y 
      end
    in let new_list = List.map subst_id l in 
    let rec alpha_comp1 = function
    |[] -> TBinder (VarSpec(new_list,comp_opt), (subst_comp x comp comp1))
    |y::tail -> 
      if y=x then TBinder (VarSpec(new_list,comp_opt), (subst_comp x comp comp1))
      else begin
        if (conflict_comp y comp) then 
          let newExpr = alpha_comp y comp1 in 
          TBinder (VarSpec(new_list,comp_opt),(subst_comp x comp newExpr))
        else alpha_comp1 tail
      end
    in alpha_comp1 l
;;

 
let rec eval env expr =
  let ev = eval env in (* partial application *)
  match expr with
  |Ident str -> check_environ env (Ident str)
  |BTrue -> BTrue
  |BFalse -> BFalse
  |EqOp (e1,e2) -> 
    let t1 = ev e1 in 
    let t2 = ev e2 in
    if t1 = t2 then BTrue else BFalse
  |In (e,comp) -> failwith "do this at last"
  |And (e1,e2) -> begin
    let t1 = ev e1 in
    let t2 = ev e2 in
    match (t1,t2) with
    |(BTrue,BTrue) -> BTrue
    |(BFalse,BFalse) -> BFalse
    |(BTrue,BFalse) -> BFalse
    |(BFalse,BTrue) -> BFalse
    | _ -> failwith "invalid arguments"
  end
  |Or (e1,e2) -> begin
    let t1 = ev e1 in
    let t2 = ev e2 in
    match (t1,t2) with
    |(BTrue,BTrue) -> BTrue
    |(BFalse,BFalse) -> BFalse
    |(BTrue,BFalse) -> BTrue
    |(BFalse,BTrue) -> BTrue
    | _ -> failwith "invalid arguments"
  end
  |Not e -> begin
    let t = ev e in
    match t with
    |BTrue -> BFalse
    |BFalse -> BTrue
    | _ -> failwith "invalid arguments"
  end 
  |Iff (e1,e2) -> begin
    let t1 = ev e1 in
    let t2 = ev e2 in
    match (t1,t2) with
    |(BTrue,BTrue) -> BTrue
    |(BFalse,BFalse) -> BTrue
    |(BTrue,BFalse) -> BFalse
    |(BFalse,BTrue) -> BFalse
    | _ -> failwith "invalid arguments"
  end
  |Implies (e1,e2) -> begin
    let t1 = ev e1 in
    let t2 = ev e2 in
    match (t1,t2) with
    |(BTrue,BTrue) -> BTrue
    |(BFalse,BFalse) -> BTrue
    |(BTrue,BFalse) -> BFalse
    |(BFalse,BTrue) -> BTrue
    | _ -> failwith "invalid argument"
  end
  |Appl (b,e1,e2) -> begin
    match e1 with
    |Binder(q,VarSpec(l,comp_opt),e) -> begin
      match q with (*get the first identifier in spec, then substitute it in e with e2*)
      |Abs -> ev (subst (List.hd l) e2 e)
      | _ -> Appl (b,(ev e1),(ev e2))
    end
    |Ident x -> begin 
      (* environment lookup to find corresponding function's definition *)
      try 
        let (_,(b1,e)) = Util.StringMap.find x (Bindings.get_defns env) in
        match b1 with
        |PConst id -> begin
          match e with
          |Binder (_,VarSpec(idList,_),e3) -> 
          ev (Subst.expr_sub (create_substitution env idList (ev e2)) e3)
          |_ -> failwith "In eval, Appl-Ident-PConst, not a Binder - not handled"
        end
        |PUniOp (id1,id2) -> ev (Subst.expr_sub (create_substitution env [id2] e2) e)
        |PApp (_,_,idList) -> ev (Subst.expr_sub (create_substitution env idList e2) e)
      with Not_found ->
        try
          let _ = (Util.StringMap.find x (Bindings.get_fields env)) in
          Appl(b,e1,e2)
        with
        | Not_found -> failwith ("Appl branch of eval, looking for "^ x ^" but did not find it.")
    end
    | _ -> failwith "invalid_argument using Appl"
  end 
  |Let (x,e1,e2) -> ev (subst x e1 e2) (* use e1 to replace the x in e2 *)
  |Binder (q,spec,e) -> Binder (q,spec,e) (* don't eval under binders *)
  |Desc (c,id,comp,e) -> Desc (c,id,comp,e) (* it has no reduction rules *)
  
  |Tuple l -> Tuple (List.map ev l)
  |Record l -> Record (List.map (eval_field_member env) l)

  |Selector (e,f) -> begin
    match e with
    |Record r -> ev (record_field_selector f r)
    | _ -> failwith "invalid_argument using Selector"
  end

  |Case (e,l) ->
    let e = ev (check_environ env e) in
    let rec matchExpr = function
    |[] -> failwith "expression match in Case not found"
    |Branch(p,e1)::tail -> 
      if (isExprInPattern env e p) then begin
        match e,p with
        |Appl(_,_,arg),PatApp(_,PatIdent(placeholderId)) -> ev (Subst.expr_sub (create_substitution env [placeholderId] arg) e1)
        |_ -> ev e1
      end
      else matchExpr tail
    in matchExpr l 

  |If (e1,e2,e3) -> begin
    let t1 = ev e1 in
    match t1 with
    |BTrue -> ev e2
    |BFalse -> ev e3
    | _ -> failwith "invalid_argument using If"
  end

  |Escape e -> failwith "escape creates a 'hole' in a piece of syntax where you can insert another piece of syntax"
  |Quote e -> failwith "Quote takes an expression and turns it into 'syntax'"
  |Eval (e,comp) -> failwith "eval does the opposite"
  |ProofObject s -> ProofObject s

and create_substitution env idList = function
  |Tuple exprList -> Subst.from_exprlist(List.map2 (fun id expr -> (id,check_environ env expr)) idList exprList)
  |expr -> if List.length idList <> 1 then failwith "The number of formal parameters and actual parameters do not match"
          else Subst.simpleExprSub (List.hd idList) expr

and check_environ env = function
  |Ident name -> begin
    try
      match (Util.StringMap.find name (Bindings.get_defns env)) with
      |(_,(params,expr)) -> begin
        match params with
        |PConst _ -> check_environ env (Subst.expr_sub (create_substitution env [name] expr) (Ident name))
        |PUniOp _ -> failwith "puniop unhandled"
        |PApp _ -> failwith "papp unhandled"
      end
    with Not_found -> Ident name
  end
  |x -> x

and eval_case env = function
  |Branch (p,e) -> Branch (p,(eval env e))

and eval_var_spec = function
  |VarSpec (l, comp_opt) -> VarSpec (l, comp_opt)

and eval_comp env tcomp =
  let evcomp = eval_comp env in
  match tcomp with
  |Type -> Type
  |TId s -> TId s
  |TApp (TBinder(VarSpec ((z::zs), comp_opt),comp1),comp2) -> evcomp (subst_comp z comp2 comp1)
  |TApp (comp1,comp2) -> TApp ((evcomp comp1),(evcomp comp2))
  |TProd l -> TProd (List.map evcomp l)
  |TArrow (comp1,comp2) -> TArrow ((evcomp comp1),(evcomp comp2))
  |TPower comp -> TPower (evcomp comp)
  |TInduct (s,l) -> TInduct (s,(List.map (eval_field_sig env) l))
  |TPredicate comp -> failwith "shold not apper recursively?"
  |TRecord l -> TRecord (List.map (eval_field_sig env) l)
  |TDepId (s,comp) -> TDepId (s,(evcomp comp))
  |TLift e -> TLift e (* don't evaluate inside lift *)
  |TTheory s -> TTheory s
  |TTypeFromTheory s -> TTypeFromTheory s
  |TProof e -> TProof (eval env e)
  |TBinder (spec,comp) -> TBinder (spec,(evcomp comp)) 

and eval_field_sig env = function
  |FieldSig (f,comp) -> FieldSig (f, (eval_comp env comp))

and eval_field_member env = function
  |FieldMem (f,comp_opt,e) -> FieldMem (f,comp_opt,(eval env e))

;;
