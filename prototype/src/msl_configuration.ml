
type prints = 
    | MathRel of string
    | MathOp of string
    | MathLeft of string
    | MathRight of string
    | Void of string

type spacing =
    | Both of string
    | Left of string
    | Right of string
    | Neither of string


module type Configuration = sig 
    
    val usr_wrap         : string * string
    val op_wrap          : string * string
    val ident_wrap       : string * string
    val keyword_wrap     : string * string
    val binder_wrap      : string * string
    val symbol_wrap      : string * string
    val row_wrap         : string * string
    val format_wrap      : string * string
    val string_wrap      : string * string 
    
    val semi             : string
    val lbrace           : string
    val rbrace           : string
    val lparen           : string
    val rparen           : string
    val lbracket         : string
    val rbracket         : string
    val questionmark     : string
    val lnumbrak         : string
    val rnumbrak         : string
    val tick             : string
    val lquote           : string
    val rquote           : string
    val lescape          : string
    val rescape          : string
    val leval            : string
    val revalat          : string
    val ampersand        : string
    val underscore       : string
    
    val forall           : string
    val exists           : string
    val exists_uniq      : string
    val abs              : string
    val iota             : string
    val epsilon          : string
    val btrue            : string
    val bfalse           : string
    
    val dot              : prints
    val equal            : prints
    val colonequal       : prints
    val colon            : prints
    val arrow1           : prints
    val arrow2           : prints
    val colon_lt         : prints
    val lift             : prints
    
    val equal_op         : prints
    val is_in            : prints
    val bar              : prints
    val and_val          : prints
    val or_val           : prints
    val implies          : prints
    val iff              : prints
    val not_val          : prints
    val ifs              : prints
    
    val quali_sep1       : prints
    val quali_sep2       : prints
    
    val list_sep         : prints
    val list_semi        : prints
    
    val case_sep         : prints

    val type_val1        : string
    val type_val2        : string
    val type_plus        : string
    val data             : string
    val power            : string  
    val case             : string
    val concept          : string
    val definition       : string
    val fact             : string
    val variable         : string
    val inductive        : string
    val type_from        : string
    val thens            : prints
    val elses            : prints
    val let_             : string
    val in_              : string
    
    val axiom            : string
    val theorem          : string
    val theory           : string
    val ext_by           : string
    val ext_con_by       : string
    val combine          : string
    val along            : string
    val mixin            : string
    val inject           : string
    val into             : string
    val via              : string
    val instance         : string
    val of_val           : string
    
    val newline : string
    val space   : string
    
    val alter_undscr     : string -> string
    
    val print_spacing    : spacing -> string

end;;

module ASCII : Configuration =
struct 

    let usr_wrap         = ("","")
    let op_wrap          = ("","")
    let ident_wrap       = ("","")
    let keyword_wrap     = ("","")
    let binder_wrap      = ("","")
    let symbol_wrap      = ("","")
    let row_wrap         = ("","")
    let format_wrap      = ("","")
    let string_wrap      = ("\"","\"")

    let semi             = ";"
    let lbrace           = "{"
    let rbrace           = "} "
    let lparen           = "("
    let rparen           = ")"
    let lbracket         = " [ "
    let rbracket         = " ]"
    let questionmark     = "?"
    let lnumbrak         = "[# "
    let rnumbrak         = " #]"
    let tick             = "`"
    let lquote           = "&("
    let rquote           = ")"
    let lescape          = "|_"
    let rescape          = "_|"
    let leval            = "[["
    let revalat          = "]]_"
    let ampersand        = "&"
    let underscore       = "_"
    
    let forall           = "forall "
    let exists           = "exists "
    let exists_uniq      = "exists! "
    let abs              = "lambda "
    let iota             = "iota "
    let epsilon          = "epsilon "
    let btrue            = "%true "
    let bfalse           = "%false "
    
    let dot              = Void "."
    let bar              = MathRel "|"
    let arrow1           = MathRel "|->"
    let arrow2           = MathRel "->"
    let colon_lt         = MathRel ":<"
    let equal            = MathRel "="
    let colonequal       = MathRel ":="
    let colon            = MathRel ":"
    
    let equal_op         = MathRel "="
    let is_in            = MathRel "`in"
    let and_val          = MathRel "and"
    let or_val           = MathRel "or"
    let implies          = MathRel "implies"
    let iff              = MathRel "iff"
    let not_val          = MathRight "not"
    let lift             = MathRight "lift"
    let ifs              = MathRight "if"
    
    let quali_sep1       = MathRel ":"
    let quali_sep2       = MathRight "."
    
    let list_sep         = Void ","
    let list_semi        = MathRight ";"
    
    let case_sep         = MathLeft "|"

    let type_val1        = "type"
    let type_val2        = "type "
    let type_plus        = "type_plus"
    let data             = "data "
    let power            = "power " 
    let case             = "case "
    let concept          = "Concept "
    let definition       = "Definition "
    let fact             = "Fact "
    let variable         = "variable "
    let inductive        = "Inductive "
    let type_from        = "TypeFrom "
    let thens            = MathRel "then"
    let elses            = MathRel "else"
    let let_             = "let"
    let in_              = "in"
    
    let axiom            = "axiom "
    let theorem          = "theorem " 
    let theory           = "Theory "
    let ext_by           = "extended by "
    let ext_con_by       = "extended conservatively by "
    let combine          = "combine "
    let along            = "over "
    let mixin            = "mixin "
    let inject           = "inject "
    let into             = " into "
    let via              = " via "
    let instance         = "instance "
    let of_val           = " of "
    
    let newline = "\n"
    let space   = " "
    
    let alter_undscr s   = s
    
    let print_spacing = function
        | Both s -> space^s^space
        | Left s -> space^s
        | Right s -> s^space
        | Neither s -> s
        
end;;

module Compact : Configuration =
struct 

    let usr_wrap         = ("\\R{","}")
    let op_wrap          = ("","")
    let ident_wrap       = ("","")
    let keyword_wrap     = ("$","$")
    let binder_wrap      = ("$","$")
    let symbol_wrap      = ("$","$")
    let row_wrap         = ("","")
    let format_wrap      = ("$","$")
    let string_wrap      = ("\"","\"")

    let semi             = ";"
    let equal            = Void ("\\K{=}")
    let colonequal       = Void ("\\K{:=}")
    let colon            = Void ("\\K{:}")
    let lbrace           = "\\{"
    let rbrace           = "\\}"
    let lparen           = "("
    let rparen           = ")"
    let lbracket         = "["
    let rbracket         = "]"
    let questionmark     = "\\K{?}"
    let dot              = Void ("\\K{.}")
    let lnumbrak         = "\\K{[#}"
    let rnumbrak         = "\\K{#]}"

    let tick             = "\\K{`}"
    let lquote           = "\\lceil"
    let rquote           = "\\rceil"
    let lescape          = "\\lfloor"
    let rescape          = "\\rfloor"
    let underscore       = "\\_"
    let leval            = "\\llbracket"
    let revalat          = "\\rrbracket\\_"
    let ampersand        = "&"

    let bar              = Void ("\\K{\\mid}")
    let arrow1           = Void ("\\K{\\BR}")
    let arrow2           = Void ("\\K{\\rA}")
    let colon_lt         = Void ("\\K{:<}")
    
    let forall           = "\\F"
    let exists           = "\\E"
    let exists_uniq      = "\\U"
    let abs              = "\\K{\\lm}"
    let iota             = "\\K{\\I}"
    let epsilon          = "\\K{\\e}"
    let btrue            = "\\K{t} "
    let bfalse           = "\\K{f} "
    
    let equal_op         = Void ("\\K{=}")
    let is_in            = Void ("\\K{in}")
    let and_val          = Void ("\\K{\\vee}")
    let or_val           = Void ("\\K{\\wedge}")
    let implies          = Void ("\\K{\\RA}")
    let iff              = Void ("\\K{\\LRA}")
    let not_val          = Void ("\\K{\\neg}")
    let lift             = Void ("\\K{lift}")
    let ifs              = Void ("\\K{if}")
    
    let quali_sep1       = Void ("\\K{\\zz}")
    let quali_sep2       = Void ("\\K{\\K}")
    
    let list_sep         = Void ("\\K{,}")
    let list_semi        = Void ("\\K{;}")
    
    let case_sep         = Void ("\\K{|}")

    let type_val1        = "\\ty"
    let type_val2        = "\\ts"
    let type_plus        = "type_plus" (* <- A mistake by Fil? *)
    let data             = "\\K{data}"
    let power            = "\\K{power}"
    let case             = "\\K{case}"
    let concept          = "\\Con"
    let definition       = "\\Def"
    let fact             = "\\Fac"
    let variable         = "\\Var"
    let inductive        = "\\Ind"
    let type_from        = "\\TypeFrom"
    let thens            = MathRel "\\Then"
    let elses            = MathRel "\\Else"
    let let_             = "\\Let"
    let in_              = "\\In"
    
    let axiom            = "\\ax"
    let theorem          = "\\K{theorem}"
    let theory           = "\\Thy"
    let ext_by           = "\\extend"
    let ext_con_by       = "\\extendCons"
    let combine          = "\\comb"
    let along            = "\\alg"
    let mixin            = "\\mixin"
    let inject           = "\\K{inject}"
    let into             = "\\K{into}"
    let via              = "\\K{via}"
    let instance         = "\\K{instance}"
    let of_val           = "\\K{of}"
    
    let newline = "$\\\\$"
    let space   = "$\\s$"
    
    let rec alter_undscr s = 
    if String.contains s '_' then
        let i = String.index s '_' in
        (String.sub s 0 i) ^ "\\_" ^ alter_undscr (String.sub s (i+1) (String.length s - (i + 1)))
    else s 
    
    let print_spacing = function
        | Both s -> s
        | Left s -> s
        | Right s -> s
        | Neither s -> s
end;;

module MathML : Configuration =
struct 

    let usr_wrap         = ("<mi>","</mi>")
    let op_wrap          = ("<mo>","</mo>")
    let ident_wrap       = ("<mi>","</mi>")
    let keyword_wrap     = ("<mi>","</mi>")
    let binder_wrap      = ("<mo>","</mo>")
    let symbol_wrap      = ("<mo>","</mo>")
    let row_wrap         = ("<mrow>","</mrow>")
    let format_wrap      = ("<mo>","</mo>")
    let string_wrap      = ("\"","\"")

    let semi             = ";"
    let lbrace           = "{"
    let rbrace           = "}"
    let lparen           = "("
    let rparen           = ")"
    let lbracket         = "[ "
    let rbracket         = " ]"
    let questionmark     = "?"
    let lnumbrak         = "[# "
    let rnumbrak         = " #]"
    let space            = " "
    let tick             = "`"
    let lquote           = "&lceil;"
    let rquote           = "&rceil;"
    let lescape          = "&lfloor;"
    let rescape          = "&rfloor;"
    let underscore       = "_"
    let leval            = "&#x27e6;"
    let revalat          = "&#x27e7;_"
    let ampersand        = "&amp;"
    
    let forall           = "&#x2200;"
    let exists           = "&#x2203;"
    let exists_uniq      = "exists!"
    let abs              = "&#x03BB;"
    let iota             = "&#x0269;"
    let epsilon          = "&#x03F5;"
    let btrue            = "t"
    let bfalse           = "f"
    
    let dot              = MathRel "."
    let bar              = MathRel "|"
    let arrow1           = MathRel "|->"
    let arrow2           = MathRel "->"
    let colon_lt         = MathRel ":<"
    let equal            = MathRel "="
    let colonequal       = MathRel ":="
    let colon            = MathRel ":"
    let lift             = MathRel "lift"
    
    let equal_op         = MathRight "="
    let is_in            = MathRight "in"
    let and_val          = MathRight "and"
    let or_val           = MathRight "or"
    let implies          = MathRight "implies"
    let iff              = MathRight "iff"
    let not_val          = MathRight "not"
    let ifs              = MathRight "if"
    
    let quali_sep1       = MathRel ":"
    let quali_sep2       = MathRel "."
    
    let list_sep         = MathRight ","
    let list_semi        = MathRight ";"
    
    let case_sep         = MathRight "|"

    let type_val1        = "type"
    let type_val2        = "type "
    let type_plus        = "type_plus"
    let data             = "data "
    let power            = "power " 
    let case             = "case " 
    let concept          = "Concept "
    let definition       = "Definition "
    let fact             = "Fact "
    let variable         = "Variable "
    let inductive        = "Inductive "
    let type_from        = "TypeFrom "
    let thens            = MathRel "then"
    let elses            = MathRel "else"
    let let_             = "let"
    let in_              = "in"
    
    let axiom            = "axiom "
    let theorem          = "theorem " 
    let theory           = "Theory "
    let ext_by           = "extended by "
    let ext_con_by       = "extended conservatively by "
    let combine          = "combine "
    let along            = "over "
    let mixin            = "mixin "
    let inject           = "inject "
    let into             = " into "
    let via              = " via "
    let instance         = "instance "
    let of_val           = " of "
    
    let newline = "\n"
    let space   = " "
    
    let alter_undscr s      = s
    
    let print_spacing = function
        | Both s -> s
        | Left s -> s
        | Right s -> s
        | Neither s -> s
    
end;;
