open Hashtbl

open TypedStructure


type attribute_descriptor = {
	static: bool;
	default: typed_expr Located.t;
}

type method_descriptor = {
	static: bool;
	args_names: string list;
	core: typed_expr Located.t;
}

(* 
	Class descriptor, with:
	name: name of the class
	attributes: hash table with keys: name of an attribute, values: typed expression of the default values
	methods: Hash table with keys: id of a method without the class, values: keys from the global methods table
*)
type advanced_class_descriptor = {
	name: string;	(* 	Name is redundant since a class descriptor is the value of a hash table, 
						which keys are the names of the classes *)
	parent: string;	(* We keep this information for casting, at least. *)
	attributes: (string, attribute_descriptor) Hashtbl.t;
	methods: (string, string) Hashtbl.t;
}

type class_descriptor =
	| ClassDescriptor of advanced_class_descriptor
	| ObjectClass
	| IntClass
	| BooleanClass
	| StringClass

let build_short_method_identifier (m_name: string) (args: string list) =
	let rec args_str = function
		| [] -> ""
		| [t] -> t
		| t::q -> t ^ "," ^ (args_str q)
	(* Short Identifier looks like: m(Int,Boolean) *)
	in (m_name ^ "(" ^ (args_str args) ^ ")")