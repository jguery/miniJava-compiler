open Parser
open Structure
open Errors
open Location
open Located
open Expr

let string_of_unop u = match u with
	| Udiff -> "not "
	| Uminus -> "minus "

let string_of_bop b = match b with
	| Bsemicol -> " SEMICOL "
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

let rec string_of_expr exp = 
	let rec string_of_exprs = function 
		| [] -> ""
		| t::q -> "Expr {" ^ (string_of_expr (Located.elem_of t)) ^ "}, " ^ (string_of_exprs q)
	in 
	match exp with 
	| Int i -> string_of_int (Located.elem_of i)
	| Boolean b -> "Bool(" ^ string_of_bool (Located.elem_of b) ^ ")"
	| String s -> "Str(" ^ Located.elem_of s ^ ")"
	| Var v -> Located.elem_of v
	| Null -> "null"
	| This -> "this"
	| AttrAffect(a, e) -> "AttrName: " ^ (Located.elem_of a) ^ ", value: Expr {"
		^ (string_of_expr (Located.elem_of e)) ^ "}"
	| Unop(u, e) -> (string_of_unop (Located.elem_of u)) ^ "Expr {" 
		^ (string_of_expr (Located.elem_of e)) ^ "}"
	| Binop(b, e1, e2) -> "Expr {" ^ (string_of_expr (Located.elem_of e1)) ^ "}" 
		^ (string_of_bop (Located.elem_of b)) ^ "Expr {" ^ (string_of_expr (Located.elem_of e2)) ^ "}"
	| Local(t, n, e1, e2) -> ("Type: " ^ (string_of_classname (Located.elem_of t)) ^", name: " 
			^ (Located.elem_of n) ^", value: " ^ "Expr {" ^ (string_of_expr (Located.elem_of e1)) ^ "} in " 
			^ "Expr {" ^ (string_of_expr (Located.elem_of e2)) ^ "}") 
	| Condition(e1, e2, e3) -> ("IF Expr {" ^ (string_of_expr (Located.elem_of e1)) ^ "} DO Expr {"
			^ (string_of_expr (Located.elem_of e2)) ^ "} ELSE Expr {" ^ (string_of_expr (Located.elem_of e3)) ^ "}")
	| MethodCall(e, s, args) -> ("CALL Object: Expr {" ^ (string_of_expr (Located.elem_of e)) ^ "}, name: " 
			^ (Located.elem_of s) ^ ", args: (" ^  (string_of_exprs args) ^ ")")
	| StaticMethodCall(t, s, args) -> ("STATIC CALL Type: " ^ (string_of_classname (Located.elem_of t)) 
			^ "}, name: " ^ (Located.elem_of s) ^ ", args: (" ^  (string_of_exprs args) ^ ")")
	| Instance(t) -> ("INSTANCE Type: " ^ (string_of_classname (Located.elem_of t)))
	| Cast(t, e) -> ("CAST To: " ^ (string_of_classname (Located.elem_of t)) ^ ", of Expr{"
			^ (string_of_expr (Located.elem_of e)) ^ "}")
	| Instanceof(e, t) -> ("ISINSTANCE? Type: " ^ (string_of_classname (Located.elem_of t)) ^ ", of Expr{"
			^ (string_of_expr (Located.elem_of e)) ^ "}")

let rec string_of_params = function
	| [] -> ""
	| t::q -> match Located.elem_of t with 
		| Param(cn, s) -> ("Param " ^ (string_of_classname (Located.elem_of cn)) ^ " " ^ (Located.elem_of s))
			^ ", " ^ (string_of_params q)

let rec string_of_attr_or_methods = function
	| [] -> ""
	| t::q -> match Located.elem_of t with 
		| Attr(cn, s) ->  ("ATTR Type: " ^ (string_of_classname (Located.elem_of cn)) ^", name: " 
			^ (Located.elem_of s) ^ "\n") ^ (string_of_attr_or_methods q)
		| AttrWithValue(cn, s, e) -> ("ATTR Type: " ^ (string_of_classname (Located.elem_of cn)) ^", name: " 
			^ (Located.elem_of s) ^", value: Expr {" ^ (string_of_expr (Located.elem_of e)) ^ "}\n") 
			^ (string_of_attr_or_methods q)
		| Method(cn, s, p, e) -> ("METHOD Return Type: " ^ (string_of_classname (Located.elem_of cn)) ^", name: " 
			^ (Located.elem_of s) ^ ", params: (" ^ (string_of_params p) ^ "), Expr {" 
			^ (string_of_expr (Located.elem_of e)) ^ "}\n") ^ (string_of_attr_or_methods q)
		| StaticAttr(cn, s) ->  ("STATIC ATTR Type: " ^ (string_of_classname (Located.elem_of cn)) ^", name: " 
			^ (Located.elem_of s) ^ "\n") ^ (string_of_attr_or_methods q)
		| StaticAttrWithValue(cn, s, e) -> ("STATIC ATTR Type: " ^ (string_of_classname (Located.elem_of cn)) 
			^", name: " ^ (Located.elem_of s) ^", value: Expr {" ^ (string_of_expr (Located.elem_of e)) ^ "}\n") 
			^ (string_of_attr_or_methods q)
		| StaticMethod(cn, s, p, e) -> ("STATIC METHOD Return Type: " ^ (string_of_classname (Located.elem_of cn)) 
			^", name: " ^ (Located.elem_of s) ^ ", params: (" ^ (string_of_params p) ^ "), Expr {" 
			^ (string_of_expr (Located.elem_of e)) ^ "}\n") ^ (string_of_attr_or_methods q)

let rec print_structure_tree l = match l with 
	| [] -> ()
	| t::q -> let matching = match Located.elem_of t with 
			| Classdef(n,l) -> print_string ("Classname: " ^ (Located.elem_of n) 
				^ ", attr: \n" ^ (string_of_attr_or_methods l))
			| ClassdefWithParent(n,p,l) -> print_string ("Classname: " ^(Located.elem_of n)^ " parent: " 
				^ (string_of_classname (Located.elem_of p)) ^ ", attr: \n" ^ (string_of_attr_or_methods l))
			| Expr e -> print_string (string_of_expr (Located.elem_of e))
		in
		matching;
		print_endline "";
		print_structure_tree q


let execute lexbuf verbose = 
  try
    let l = structure_tree nexttoken lexbuf in
    	(*if verbose then begin
	    	print_structure_tree l;
	    	print_newline();
	    end; *)
	    print_structure_tree l;
	    print_newline();
	    (* D'autres opérations *)
	    exit 0
  with PError (e, t) ->
  	(* Handle errors *)
  	Location.print t;
  	print_endline (Errors.string_of_error e);
    print_endline (Lexing.lexeme lexbuf);
    exit (-1)