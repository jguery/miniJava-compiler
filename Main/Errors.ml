open Location

type error = 
	| SyntaxError
	| TypeError of string * string
	| UndefinedType of string
	| UndefinedMethod of string * string * string list
	| UndefinedObject of string
	| IllegalCast of string * string
	| IllegalRuntimeCast of string * string
	| NamingError of string
	| NullError

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
	| UndefinedType t -> "Definition error: Type " ^ t ^ " is undefined"
	| UndefinedMethod (t, m, args) -> "Definition error: Method " ^ m ^ "(" 
		^ (string_of_args args) ^ ") of type " ^ t ^ " is undefined"
	| UndefinedObject s -> "Definition error: Object " ^ s ^ " is undefined"
	| IllegalCast(set, nt) -> "Casting error: Cannot cast expression of type " ^ set ^ " to type " ^ nt
	| IllegalRuntimeCast (set, nt) -> "Runtime casting error: Object real type is " ^ set ^ " and cannot be casted to type " ^ nt
	| NamingError n -> "Naming Error: Object " ^ n ^ " is already defined"
	| NullError -> "Null Error: Object or expression is null" 