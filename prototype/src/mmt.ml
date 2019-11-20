(* File: mmt.ml *)
(* Read test file, handle errors, translate to mmt *)

let usage = "usage: " ^ Sys.argv.(0) ^ " file.v"
let file =
    let fileref = ref "" in
    let speclist = [] in
    Arg.parse speclist (fun s -> fileref := s) usage; !fileref

let main() = begin
    try begin
        let expr = Library.read file in
        let lib = Track.create_lib "top" expr in
        let uri = "http://mathscheme.cas.mcmaster.ca/library" in
        let modid = (uri, [Filename.chop_extension file]) in
        let mmt_test = To_mmt.translate uri lib in
        Print_mmt.print modid mmt_test
    end with
      | Typechecker.TypeExceptionAt errs ->
        let f (place,err) = 
          Printf.eprintf "type error at %s\n" place;
          flush stderr;
          Printf.eprintf "%s\n" (Typechecker.printTypeExceptionData err);
          exit 1
        in List.iter f errs
   end
     
let _ = main()
