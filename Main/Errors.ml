open Location

type error = 
	| SyntaxError
	| TypeError of string * string

exception PError of error * Location.t

let string_of_error = function
	| SyntaxError -> "Syntax error"
	| TypeError(exp, real) -> "Type error: This expression has type " ^ real 
		^ ", but an expression was expected of type " ^ exp