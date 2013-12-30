open Located
open Location
open Errors
open Structure

type exprType = 
	| IntType
	| BooleanType
	| StringType

let string_of_expr_type = function
	| IntType -> "Int"
	| BooleanType -> "Boolean"
	| StringType -> "String"

let make_error expr exp_type real_type = 
	raise (PError(TypeError(string_of_expr_type exp_type, string_of_expr_type real_type), 
		Located.loc_of expr))

let rec type_of_expr exp = 
	let rec type_of_unop unop locExpr = match unop with
		| Udiff -> (match (type_of_expr (Located.elem_of locExpr)) with
			| BooleanType -> BooleanType
			| _ as t -> make_error locExpr BooleanType t
		)
	  	| Uminus -> (match (type_of_expr (Located.elem_of locExpr)) with
	  		| IntType -> IntType
	  		| _ as t -> make_error locExpr IntType t
	  	)
  	in match exp with 
		| Int(i) -> IntType
		| Boolean(b) -> BooleanType
		| String(s) -> StringType
		| Unop(u, e) -> type_of_unop (Located.elem_of u) e

let rec type_of_structure_tree tree = 
	let rec type_of_structure = function
		| Expr e -> type_of_expr (Located.elem_of e)
	in match tree with 
	| t::q -> type_of_structure t

let _ = 
	let expr = String(Located.mk_elem "true" Location.none) in
		print_string (string_of_expr_type (type_of_expr expr));
		print_newline()