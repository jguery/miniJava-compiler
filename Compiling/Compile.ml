open Hashtbl

open TypedStructure
open CompileStructures

(* Build the classes descriptors of the primitive classes. *)
let build_basic_classes_descriptors classes_descriptors =
	Hashtbl.add classes_descriptors "Object" ObjectClass;
	Hashtbl.add classes_descriptors "Int" IntClass;
	Hashtbl.add classes_descriptors "Boolean" BooleanClass;
	Hashtbl.add classes_descriptors "String" StringClass
	(* TODO in Typer, add attributes to class environment of basic types *)


let build_class_descriptor methods_table name parent l_attrs_methods = 
	let attrs = Hashtbl.create 5; (* TODO add attributes from parent class *)
	and methods = []
	in (match l_attrs_methods with
	| [] -> ()
	| h::q -> (match Located.elem_of h with
				| TypedAttr (c, n, t) -> Hashtbl.add attrs (Located.elem_of n) (Located.mk_elem TypedNull (Located.loc_of h))
				| TypedAttrWithValue (c, n, e, t) -> Hashtbl.add attrs (Located.elem_of n) e

	(* 				 | TypedAttr of classname Located.t * string Located.t * string
	  | TypedAttrWithValue of classname Located.t * string Located.t * typed_expr Located.t * string
	  | TypedMethod of classname Located.t * string Located.t * typed_param Located.t list * typed_expr Located.t 
	  	* string
	  | TypedStaticAttr of classname Located.t * string Located.t * string
	  | TypedStaticAttrWithValue of classname Located.t * string Located.t * typed_expr Located.t * string
	  | TypedStaticMethod of classname Located.t * string Located.t * typed_param Located.t list 
	  	* typed_expr Located.t * string
	 *)	
			)
		);
	ClassDescriptor({
		name = Located.elem_of name;
		size = 0; (* TODO change that *)
		attributes = attrs;
		methods = []
	})


let compile typed_tree = 
	let classes_descriptors = Hashtbl.create 10
	and methods_table = Hashtbl.create 30
	in build_basic_classes_descriptors classes_descriptors;
	let rec rec_compile = function
		| [] -> classes_descriptors
		| t::q -> (match Located.elem_of t with
					| TypedClassdef (n, l) -> Hashtbl.add classes_descriptors (Located.elem_of n) 
							(build_class_descriptor methods_table n None l); 
						rec_compile q
					| TypedExpr e -> rec_compile q
			)
	in rec_compile typed_tree

(* 	  | TypedClassdef of string Located.t * typed_attr_or_method Located.t list
  | TypedClassdefWithParent of string Located.t * classname Located.t * typed_attr_or_method Located.t list 
  | TypedExpr of typed_expr Located.t
 *)