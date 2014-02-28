open Hashtbl

open Structure
open TypedStructure
open CompileStructures

(* Build the classes descriptors of the primitive classes. *)
let build_basic_classes_descriptors classes_descriptors =
	Hashtbl.add classes_descriptors "Object" ObjectClass;
	Hashtbl.add classes_descriptors "Int" IntClass;
	Hashtbl.add classes_descriptors "Boolean" BooleanClass;
	Hashtbl.add classes_descriptors "String" StringClass


let add_heritage_structures classes_descriptors methods_table =
	let (table_done: (string, bool) Hashtbl.t) = Hashtbl.create 10

	in let merge_attrs parent_desc class_desc =
		match parent_desc with 
		| ClassDescriptor cd ->
			Hashtbl.iter 
				(fun k (v: attribute_descriptor) -> if v.static then () else Hashtbl.add class_desc.attributes k v) 
				cd.attributes
		| _ -> ()

	and merge_methods parent_desc class_desc =
		let add_method m_short_id m_id = 
			try
				Hashtbl.find class_desc.methods m_short_id;
				()
				(* Found, don't add the parent method definition *)
			with Not_found ->
				(* Not found, so the parent's definition must be added *)
				Hashtbl.add class_desc.methods m_short_id m_id
		in match parent_desc with
		| ClassDescriptor cd -> Hashtbl.iter add_method cd.methods
		| _ -> ()

	in let add_heritage_structure class_name class_descriptor =
		match class_descriptor with
		| ClassDescriptor cd -> 
			if Hashtbl.find table_done class_name <> true then begin
				let parent_descriptor = Hashtbl.find classes_descriptors cd.parent
				in
				Hashtbl.replace table_done cd.name true;
				merge_attrs parent_descriptor cd;
				merge_methods parent_descriptor cd
			end
			(* The descriptor for that class has already been checked, return it as is. *)
		| _ -> ()
	in
	Hashtbl.iter (fun k _ -> Hashtbl.add table_done k false) classes_descriptors;
	Hashtbl.iter add_heritage_structure classes_descriptors


(* This function builds the methods and attributes descriptors of a class *)
(* class_descriptor is the class descriptor to which we add attributs and methods descriptors. *)
(* methods_table is the global methods' table. *)
(* l_methods_attrs is the list of typed methods and attributs defined in the class. *)
(* This function returns Unit, since it only modifies the two first parameters. *)
let rec build_attrs_and_methods_descriptors class_descriptor methods_table l_methods_attrs = 

	let _add_method_to_descriptor m = 
		(* Build a method descriptor and add it to the global methods table. Also, add a link to the method
		in the list of methods of the current class descriptor. It returns Unit *)
		let build_method_descriptor m_name args m_expr m_static =
			let m_short_id = build_short_method_identifier m_name (params_types args)
			in let m_id = class_descriptor.name ^ "[" ^ m_short_id ^ "]"
			in 
			Hashtbl.add methods_table m_id 
				{
					static=m_static;
					core=m_expr;
					args_names=params_names args;
				};
			Hashtbl.add class_descriptor.methods m_short_id m_id
		in match Located.elem_of m with 
			| TypedMethod(r, n, args, e, t) -> build_method_descriptor (Located.elem_of n) args e false 
			| TypedStaticMethod(r, n, args, e, t) -> build_method_descriptor (Located.elem_of n) args e true 

	and _add_attr_to_descriptor n static e =
		Hashtbl.add class_descriptor.attributes (Located.elem_of n) {default=e; static=static;}

	in match l_methods_attrs with
	| [] -> ()
	| elem::q -> (match (Located.elem_of elem) with 
			| TypedMethod _ | TypedStaticMethod _ -> _add_method_to_descriptor elem;
			| TypedAttr(_, n, t) -> _add_attr_to_descriptor n false (Located.mk_elem TypedNull (Located.loc_of elem))
			| TypedAttrWithValue(_, n, e, t) -> _add_attr_to_descriptor n false e
			| TypedStaticAttr(_, n, t) -> _add_attr_to_descriptor n true (Located.mk_elem TypedNull (Located.loc_of elem))
			| TypedStaticAttrWithValue(_, n, e, t) -> _add_attr_to_descriptor n true e
		);
		build_attrs_and_methods_descriptors class_descriptor methods_table q



(* Create new classes descriptors, but without methods and attributes for the moment. *)
let rec build_descriptors_1 classes_descriptors methods_table tree =
	match tree with
	| [] -> ()
	| t::q -> (match Located.elem_of t with 
			| TypedClassdef (n, l) ->
				let adv_class_descriptor = {
					name=Located.elem_of n;
					parent="Object";
					attributes=Hashtbl.create 10;
					methods=Hashtbl.create 10;
				}
				in 
				Hashtbl.add classes_descriptors (Located.elem_of n) (ClassDescriptor(adv_class_descriptor));
				build_attrs_and_methods_descriptors adv_class_descriptor methods_table l

			| TypedClassdefWithParent (n, p, l) -> 
				let adv_class_descriptor = {
					name=Located.elem_of n;
					parent=string_of_classname (Located.elem_of p);
					attributes=Hashtbl.create 10;
					methods=Hashtbl.create 10;
				}
				in 
				Hashtbl.add classes_descriptors (Located.elem_of n) (ClassDescriptor(adv_class_descriptor));
				build_attrs_and_methods_descriptors adv_class_descriptor methods_table l

			| _ -> ()
		);
		build_descriptors_1 classes_descriptors methods_table q


let compile tree = 
	let classes_descriptors = Hashtbl.create 10
	and methods_table = Hashtbl.create 30
	in
	build_basic_classes_descriptors classes_descriptors;
	build_descriptors_1 classes_descriptors methods_table tree;
	add_heritage_structures classes_descriptors methods_table;

	classes_descriptors, methods_table