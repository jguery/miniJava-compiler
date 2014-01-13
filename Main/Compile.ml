open Parser
open Structure
open Errors
open Location
open Located
open Expr
open Typer

let execute lexbuf verbose = 
  try
  	(* Build the data structure *)
    let l = structure_tree nexttoken lexbuf in
    	(*if verbose then begin
	    	print_structure_tree l;
	    	print_newline();
	    end; *)
		
		(* Print a string-ed version of our data structure *)
	    print_string (string_of_structure_tree l);

	    print_endline ("Type :");
	    print_string (string_of_expr_types (type_of_structure_tree (type_structure_tree l)));
	   	print_newline();

	    exit 0
  with PError (e, t) ->
  	(* Handle any kind of error *)
  	Location.print t;
  	print_endline (Errors.string_of_error e);
    print_endline (Lexing.lexeme lexbuf);
    exit (-1)