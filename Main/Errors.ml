open Location

type error = 
	| SyntaxError
	| TypeError of string * string
	| UndefinedType of string
	| UndefinedMethod of string * string * string list

exception PError of error * Location.t

let string_of_error e = 
	let rec string_of_args = function
		| [] -> ""
		| [t] -> t
		| t::q -> t ^ ", " ^ (string_of_args q)
	in match e with
	| SyntaxError -> "Syntax error"
	| TypeError(exp, real) -> "Type error: This expression has type " ^ real 
		^ ", but an expression was expected of type " ^ exp
	| UndefinedType t -> "Definition error: type " ^ t ^ " is undefined"
	| UndefinedMethod (t, m, args) -> "Definition error: method " ^ m ^ "(" 
		^ (string_of_args args) ^ ") of type " ^ t ^ " is undefined"