open Hashtbl

open TypedStructure
open CompileStructures

(* Build the classes descriptors of the primitive classes. *)
let build_basic_classes_descriptors classes_descriptors =
	Hashtbl.add classes_descriptors "Object" ObjectClass;
	Hashtbl.add classes_descriptors "Int" IntClass;
	Hashtbl.add classes_descriptors "Boolean" BooleanClass;
	Hashtbl.add classes_descriptors "String" StringClass

(* Build a method descriptor and add it to the global methods table. Also, add a link to the method
	in the list of methods of the current class descriptor. It returns Unit *)
let build_method_descriptor methods_table class_methods class_name m_name args m_expr =
	let m_short_id = build_short_method_identifier m_name (params_types args)
	in let m_id = class_name ^ "[" ^ m_short_id ^ "]"
	in 
	Hashtbl.add methods_table m_id 
		{
			core=m_expr;
			args_names=params_names args;
		};
	Hashtbl.add class_methods m_short_id m_id

let rec build_class_descriptor methods_table name parent l_attrs_methods = 
	let attrs = Hashtbl.create 5 (* TODO add attributes from parent class *)
	and methods = Hashtbl.create 5
	in let match_attr_or_method h = match Located.elem_of h with
		| TypedAttr (c, n, t) -> Hashtbl.add attrs (Located.elem_of n) (Located.mk_elem TypedNull (Located.loc_of h))
		| TypedAttrWithValue (c, n, e, t) -> Hashtbl.add attrs (Located.elem_of n) e
		| TypedMethod (c, n, args, e, t) -> build_method_descriptor methods_table methods (Located.elem_of name) (Located.elem_of n) args e
			(* TODO Should check here redefinition, and erase the existing, if any *)

	in let rec iter_attrs_or_methods = function
		| [] -> ()
		| h::q -> match_attr_or_method h; iter_attrs_or_methods q
	in iter_attrs_or_methods l_attrs_methods;
	ClassDescriptor({
		name = Located.elem_of name;
		size = 0; (* TODO change that *)
		attributes = attrs;
		methods = methods
	})


let compile typed_tree = 
	let classes_descriptors = Hashtbl.create 10
	and methods_table = Hashtbl.create 30
	in build_basic_classes_descriptors classes_descriptors;
	let rec rec_compile = function
		| [] -> classes_descriptors, methods_table
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