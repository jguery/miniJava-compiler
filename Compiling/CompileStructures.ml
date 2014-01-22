open Hashtbl

open TypedStructure

(* 
	Class descriptor, with:
	name: name of the class
	size: number of attributes
	attributes: hash table with keys: name of an attribute, values: typed expression of the default values
	methods: list of string keys from the methods hash table
*)
type advanced_class_descriptor = {
	name: string;
	size: int;
	attributes: (string, typed_expr Located.t) Hashtbl.t;
	methods: string list;
}

type class_descriptor =
	| ClassDescriptor of advanced_class_descriptor
	| ObjectClass
	| IntClass
	| BooleanClass
	| StringClass