open Parser
open Types
open Expr

let string_of_classname = function
	| Classname cn -> cn

let rec string_of_expr = function
	| Int i -> string_of_int i
	| Boolean b -> string_of_bool b
	| String s -> s
	| Null -> "null"
	| This -> "this"

let rec string_of_attr_or_methods = function
	| [] -> ""
	| t::q -> match t with 
		| Attr(cn, s) ->  ("Type: " ^ (string_of_classname cn) ^", name: " ^ s ^"\n") 
			^ (string_of_attr_or_methods q)
		| AttrWithValue(cn, s, e) -> ("Type: " ^ (string_of_classname cn) ^", name: " 
			^ s ^", value: " ^ (string_of_expr e) ^"\n") 
			^ (string_of_attr_or_methods q)

let rec print_compile_list l = match l with 
	| [] -> ()
	| t::q -> match t with 
			| Classdef(n,l) -> print_string ("Classname: " ^ n )
			| ClassdefWithParent(n,p,l) -> print_string ("Classname: " ^n^ " parent: " 
				^ (string_of_classname p) ^ ", attr: \n" ^ (string_of_attr_or_methods l));
		print_compile_list q


let execute lexbuf verbose = 
  try
    let l = compile_list nexttoken lexbuf in
	    print_compile_list l;
	    print_newline();
	    (* D'autres opérations *)
	    exit 0
  with Parser.Error ->
  	(* Handle syntax errors *)
  	print_endline "Syntax Error :";
  	Location.print (Location.curr lexbuf);
    print_endline (Lexing.lexeme lexbuf);
    exit (-1)