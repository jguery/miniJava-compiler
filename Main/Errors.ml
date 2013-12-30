open Location

type error = 
	| SyntaxError
	| TypeError of string * string

exception PError of error * Location.t

let string_of_error = function
	| SyntaxError -> "Syntax error"
	| TypeError(exp, real) -> "Type error. Expected type" ^ exp ^ " , but got type " ^ real