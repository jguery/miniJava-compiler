open Structure
open Location
open Located
open Expr
open TypedStructure

let execute lexbuf verbose = 
  try
  	(* Build the data structure *)
    let l = Parser.structure_tree nexttoken lexbuf in
    let t_l = Typer.type_structure_tree l in
    let classes_descriptor = Compile.compile t_l in
    let evaluation = Eval.eval t_l classes_descriptor in
    	(*if verbose then begin
	    	print_structure_tree l;
	    	print_newline();
	    end; *)
		
		  (* Print a string-ed version of our data structure *)
	    print_string (string_of_structure_tree l);

	    print_endline ("Type :");
	    print_string (string_of_expr_types (type_of_structure_tree t_l));
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