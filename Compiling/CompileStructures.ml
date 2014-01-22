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
	name: string;	(* 	Name is redundant since a class descriptor is the value of a hash table, 
						which keys are the names of the classes *)
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

type method_descriptor = {
	args_names: string list;
	core: typed_expr;
}