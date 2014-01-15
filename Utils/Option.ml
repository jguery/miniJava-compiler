exception No_value

let get = function
	| None -> raise No_value
	| Some a -> a