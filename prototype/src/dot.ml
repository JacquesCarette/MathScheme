open Library
open Buffer

(* Should really use Format, but that's overkill for now *)
let dotTextFromDeps deps file =
    let b = create 10000 in
    let p = add_string b and pc = add_char b in
    let nl () = pc '\n' and quote () = pc '"' in
    let quoted s = (quote (); p s; quote ()) in
    let dotOneDep k s = 
        let doit n = (p "    "; quoted k; p " -> "; quoted n; nl ()) in
        Util.NS.iter doit s in
    p "digraph "; quoted file; p " {"; nl ();
        p "label = "; quoted file; nl (); nl ();
        Util.StringMap.iter dotOneDep deps;
    pc '}'; nl ();
    let h = open_out (file ^ ".gv") in
    output_buffer h b; close_out h

let output lib f = 
    let file = Filename.chop_extension f in
    let deps = Util.StringMap.map Bindings.thy_dps_on lib.arrows in
    dotTextFromDeps deps file
