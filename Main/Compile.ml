open Parser
open Types
open Errors
open Location
open Located
open Expr

let string_of_unop u = match u with
	| Udiff -> "not "
	| Uminus -> "minus "

let string_of_bop b = match b with
	| Bptvirg -> "; "
	| Binf -> " INF "
	| BinfEq -> " INFEQ "
	| Bsup -> " SUP "
	| Bsupeq -> " SUPEQ "
	| Bdiff -> " DIFF "
	| Beq -> " EQ "
  	| Badd -> " ADD "
  	| Bsub -> " SUB "
  	| Bmul -> " MUL "
  	| Bdiv -> " DIV "
  	| Bmod -> " MOD "
  	| Band -> " AND "
  	| Bor -> " OR "

let string_of_classname = function
	| Classname cn -> Located.elem_of cn

let rec string_of_expr = function
	| Int i -> string_of_int (Located.elem_of i)
	| Boolean b -> string_of_bool (Located.elem_of b)
	| String s -> Located.elem_of s
	| Null -> "null"
	| This -> "this"
	| Unop(u, e) -> (string_of_unop (Located.elem_of u)) ^ (string_of_expr (Located.elem_of e))
	| Binop(b, e1, e2) -> (string_of_expr (Located.elem_of e1)) ^ (string_of_bop (Located.elem_of b)) ^ 
		(string_of_expr (Located.elem_of e2))
	| Instance(t, n, e1, e2) -> ("Type: " ^ (string_of_classname (Located.elem_of t)) ^", name: " 
			^ (Located.elem_of n) ^", value: " ^ (string_of_expr (Located.elem_of e1)) ^ " in " 
			^ (string_of_expr (Located.elem_of e2))) 

let rec string_of_attr_or_methods = function
	| [] -> ""
	| t::q -> match Located.elem_of t with 
		| Attr(cn, s) ->  ("Type: " ^ (string_of_classname (Located.elem_of cn)) ^", name: " 
			^ (Located.elem_of s) ^"\n") ^ (string_of_attr_or_methods q)
		| AttrWithValue(cn, s, e) -> ("Type: " ^ (string_of_classname (Located.elem_of cn)) ^", name: " 
			^ (Located.elem_of s) ^", value: " ^ (string_of_expr (Located.elem_of e)) ^"\n") 
			^ (string_of_attr_or_methods q)

let rec print_compile_list l = match l with 
	| [] -> ()
	| t::q -> let matching = match Located.elem_of t with 
			| Classdef(n,l) -> print_string ("Classname: " ^ (Located.elem_of n) )
			| ClassdefWithParent(n,p,l) -> print_string ("Classname: " ^(Located.elem_of n)^ " parent: " 
				^ (string_of_classname (Located.elem_of p)) ^ ", attr: \n" ^ (string_of_attr_or_methods l))
			| Expr e -> print_string (string_of_expr (Located.elem_of e))
		in
		matching;
		print_endline "";
		print_compile_list q


let execute lexbuf verbose = 
  try
    let l = compile_list nexttoken lexbuf in
	    print_compile_list l;
	    print_newline();
	    (* D'autres opérations *)
	    exit 0
  with PError (e, t) ->
  	(* Handle errors errors *)
  	Location.print t;
  	print_endline (Errors.string_of_error e);
    print_endline (Lexing.lexeme lexbuf);
    exit (-1)