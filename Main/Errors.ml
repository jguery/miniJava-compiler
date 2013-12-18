open Location

type error = 
	| SyntaxError

exception PError of error * Location.t

let string_of_error = function
	| SyntaxError -> "Syntax error"