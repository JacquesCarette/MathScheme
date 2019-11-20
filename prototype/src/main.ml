(* File: main.ml *)
(* Read test file and handle errors, produce output the same as input *)

type workLevel = Parsing | Binding | Flattening | Reducing | TypeChecking

let usage = "usage: " ^ Sys.argv.(0) ^ " [-level <lvl>] [-log] [-dot] file.msl"
let readLevel = function
    | s when s = "parse" -> Parsing
    | s when s = "bind" -> Binding
    | s when s = "flatten" -> Flattening
    | s when s = "reduce" -> Reducing
    | s when s = "typecheck" -> TypeChecking
    | s -> failwith ("unknown level: " ^ s)

let output_dot = ref false

let (level,file) =
    let levelref = ref TypeChecking in
    let fileref = ref "" in
    let level_spec = ("-level", Arg.Symbol (["parse"; "bind"; "flatten";
    "reduce"; "typecheck"],
                     fun s -> levelref := readLevel s),
                    ": how far to process the file") in
    let log_spec = ("-log", Arg.Set Log.verbose, ": set verbose logging") in
    let dot_spec = ("-dot", Arg.Set output_dot, ": set dot output") in
    let speclist = [level_spec; log_spec; dot_spec] in
    Arg.parse speclist (fun s -> fileref := s) usage; (!levelref,!fileref)

let main() = begin
    try begin
        let expr = Library.read file in
        let result = 
          if level = Parsing then expr
          else let lib = Track.create_lib "top" expr in
            (* do some light type-checking *)
            let lib = Checkthy.checklib lib in
            if !output_dot then Dot.output lib file;
            if level = Binding then Reify.reify_library lib 
            else let lib = Flattener.expand_top lib in
              if level = Flattening then Reify.reify_expanded_library lib 
              else let lib = Reducer.reducer lib in
                Reify.reify_expanded_library lib
         in
         if level = TypeChecking then Typechecker.typecheck_toplevel result
                                 else Printers.Direct.print result
    end with
      | Typechecker.TypeExceptionAt errs ->
        let f (place,err) =
          Printf.eprintf "type error at %s\n" place;
          flush stderr;
          Printf.eprintf "%s\n" (Typechecker.printTypeExceptionData err);
        in List.iter f errs;
           exit 1
   end
     
let _ = main()
