type box = HoV | V | H | HV | Reg 
type space_opt = OBoth | OLeft | ORight | ONeither

module type Options =
sig 
    val concepts         : box
    val facts            : box
    val thys             : box
    val variables        : box
    val functions        : box
    val exprs            : box
    val types            : box
    val theory_exprs     : box
    val default          : box
    
    val box_indent       : int
    
    val compact_struct   : bool
    
    val mathrel          : space_opt
    val mathop           : space_opt
    val mathleft         : space_opt
    val mathright        : space_opt
end

(* Recomended Settings
 *
 * For ASCII and Compact
 * let concepts         = V
 * let facts            = V
 * let thys             = HV
 * let variables        = HV
 * let functions        = V
 * let exprs            = HV
 * let types            = Reg
 * let theory_exprs     = HV   
 * let default          = Reg
 *
 * For MathML set all box options to V
 *)

module StdOpt = 
struct 
    let concepts         = V
    let facts            = V
    let thys             = HV
    let variables        = HV
    let functions        = V
    let exprs            = HV
    let types            = Reg
    let theory_exprs     = HV 
    let default          = Reg
    
    let box_indent       = 2
    
    let compact_struct   = false
    
    let mathrel          = OBoth
    let mathop           = ONeither
    let mathleft         = OLeft
    let mathright        = ORight
end
