open Structure
open Location
open Located
open Expr
open TypedStructure

let execute lexbuf verbose = 
  try
  	(* Build the data structure *)
    let l = Parser.structure_tree nexttoken lexbuf in

      if verbose then begin 
        (* Print a string-ed version of our data structure *)
        print_string (string_of_structure_tree l);
        print_newline();
      end;

      let t_l = Typer.type_structure_tree l in

        if verbose then begin 
    	    print_endline ("Type :");
    	    print_string (string_of_expr_types (type_of_structure_tree t_l));
    	   	print_newline();
        end;

        let classes_descriptor, methods_table = Compile.compile t_l in
        let evaluation = Eval.eval t_l classes_descriptor methods_table in

          print_newline();
          print_endline ("Eval :");
          Eval.print_evaluated_list evaluation;

  	      exit 0
  with Errors.PError (e, t) ->
  	(* Handle any kind of error *)
  	Location.print t;
  	print_endline (Errors.string_of_error e);
    print_endline (Lexing.lexeme lexbuf);
    exit (-1)