exception No_value

let get = function
	| None -> raise No_value
	| Some a -> a

let is_none = function
	| None -> true
	| _ -> false