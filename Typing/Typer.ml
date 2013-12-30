open Located
open Location
open Structure

type exprType = 
	| IntType
	| BooleanType
	| StringType

let string_of_expr_type = function
	| IntType -> "Int"
	| BooleanType -> "Boolean"
	| StringType -> "String"

let rec find_expr_type = function
	| Int(i) -> IntType
	| Boolean(b) -> BooleanType
	| String(s) -> StringType

let _ = 
	let expr = Int(Located.mk_elem 1 Location.none) in
	print_string (string_of_expr_type (find_expr_type expr))
