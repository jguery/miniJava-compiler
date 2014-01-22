open Hashtbl

type advanced_object_descriptor = {
	t: string; (* Type of the object *)
	attrs_values: (string, int) Hashtbl.t; (* Hash table with key: name of the attribute, value: address in the heap of the current value *)
}

type object_descriptor = 
	| ObjectDescriptor of advanced_object_descriptor
	| IntDescriptor of int option
	| BooleanDescriptor of bool option
	| StringDescriptor of string option