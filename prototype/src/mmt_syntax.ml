(* Definition of an AST which corresponds 'directly' to MMT (aka
 * OMDOC 1.6) *)

(* Since this is code rather than a nice formal definition, we need to
 * define things bottom-up rather than top-down.  [else it would be one
 * giant mutually-recursive case, which seems pointless].  So this
 * corresponds to Figure 4 (the MMT grammar) read from the bottom up. *)

type locid = string list (* implicit / between things.  should be len >= 2 *)
type name  = string (* should be non-empty *)
type uri   = string (* has internal structure which we ignore for now *)

type symid = SymId of modid * locid
and  modid = ModId of docid option * locid
and  docid = DocId of uri

type term = 
  | Top
  | Const of modid * locid
  | Var of name
  | MorApp of morphism * term
  | App of term * term list
  | Bind of term * context * term
and context = taggedvar list
and taggedvar = name * term option * term option

and morphism = 
  | IdMor of modid
  | LinkMor of modid
  | AppMor of morphism * morphism
  | CoProdMor of morphism * morphism * morphism option
  | PushForwardMor of morphism * thyexpr

and thyexpr =
  | ThyName of modid
  | ThyCoProduct of thyexpr * thyexpr
  | ThyPush of thyexpr * thyexpr * morphism

type assigns = 
  | StructAssign of locid * morphism
  | ConstAssign of locid * term

type linkbody = assigns list
type structure = 
  | ThyStruct of locid * modid * linkbody * morphism option
  | MorStruct of locid * modid * morphism
type thyconst = 
  | TypedConstDefn of locid * term * term
  | TypedConstDecl of locid * term
  | ConstDefn      of locid * term
  | ConstTerm      of locid

type thybody = 
  | ThyConst of thyconst
  | ThyStructure of structure
  | ThyInclude of thyexpr
  | ThyAlias of (uri * uri) list

type meta  = modid option
type thy = 
  | ThyDef of locid * thybody list * meta
  | ThyExpr of thyexpr
type view = ThyLink of modid * modid
type thy_or_view = Thy of thy | View of view
type thy_graph = thy_or_view list

type doc = Doc of uri * thy_graph
