open Option
open Structure
open TypedStructure
open Errors

(**************************************************************************************************)
(******************** These functions build the classes definition environment ********************)

(* Basic types classes' environment. Object is the only one to have no parent. *)
let static_classes_env = 
	[
		{name="Int"; parent=Some "Object"; methods=[]; attributes=[]};
		{name="String"; parent=Some "Object"; methods=[]; attributes=[]};
		{name="Boolean"; parent=Some "Object"; methods=[]; attributes=[]};
		{name="Object"; parent=None; methods=[]; attributes=[]};
	]

(* This function checks that a type exists for the given classname, and returns it. *)
(* The classname is a non-located Structure.classname. *)
let rec type_of_classname currentClassesEnv cn loc = 
	match currentClassesEnv with 
	| [] -> raise (PError(UndefinedType(string_of_classname cn), loc))
	| t::q when t.name = (string_of_classname cn) -> t.name
	| t::q -> type_of_classname q cn loc

(* This function takes a class environment and a located classname and
returns the methods associated to the classname in the env *)
let rec methods_of_type currentClassesEnv withStaticMethods locCn = 
	let rec parse_methods methods = if (withStaticMethods) then methods else
		begin match methods with 
			| [] -> []
			| t::q -> if (t.static) then parse_methods q else t::(parse_methods q)
		end
	in match currentClassesEnv with 
	| [] -> raise (PError(UndefinedType(string_of_classname (Located.elem_of locCn)), Located.loc_of locCn))
	| t::q -> (match (Located.elem_of locCn) with
			| Classname s when (Located.elem_of s) = t.name -> parse_methods t.methods
			| _ -> methods_of_type q withStaticMethods locCn
		)

(* This function takes a class environment and a located classname and
returns the attributes associated to the classname in the env *)
let rec attributes_of_type currentClassesEnv withStaticAttrs locCn = 
	let rec parse_attrs attrs = if (withStaticAttrs) then attrs else
		begin match attrs with 
			| [] -> []
			| t::q -> t.t; if (t.static) then parse_attrs q else t::(parse_attrs q)
		end
	in match currentClassesEnv with 
	| [] -> raise (PError(UndefinedType(string_of_classname (Located.elem_of locCn)), Located.loc_of locCn))
	| t::q -> (match (Located.elem_of locCn) with
			| Classname s when (Located.elem_of s) = t.name -> parse_attrs t.attributes
			| _ -> attributes_of_type q withStaticAttrs locCn
		)

(* This function builds a list of string types, based on a list of params *)
let rec build_params_env currentClassesEnv p = 
	let rec build_param_env = function
		| Param (c, n) -> type_of_classname currentClassesEnv (Located.elem_of c) (Located.loc_of c)
	in match p with 
	| [] -> []
	| t::q -> (build_param_env (Located.elem_of t))::(build_params_env currentClassesEnv q)

(* Check that the classes environment checks out. In particular, watches out for naming errors and redefinitions. *)
let rec check_env currentClassesEnv =
	let (table_done: (string, bool) Hashtbl.t) = Hashtbl.create (List.length currentClassesEnv)

	in let rec init_table_done env = match env with
		| [] -> ()
		| t::q -> Hashtbl.add table_done t.name false; init_table_done q

	in let rec check_circular_extends env = 
		(* Description of the algorithm: visit each node of the graph and put them in a hash table of already seen nodes.
			For each pass in the _sub method, we save a current path. If, when passing through the current heritage path,
			we meet a node that we've seen on the same path, there is a cycle. If we've seen this node already during another
			call of the _sub function, we stop its execution: this heritage path is sane. A heritage path is also sane when
			the parent is None (ie, the parent of Object).
			This analysis is built on the fact that, for a cycle to exist, there must be a portion of the graph that is not
			at all linked to Object (and thus neither to None) *)
		let rec _sub current_path visited_before class_def = 
		(* parent: string option *)
			try
				Hashtbl.find current_path class_def.name;
				(* Found in the current path: cycle *)
				raise (PError(CircularExtendsError(class_def.name), Location.none))
			with Not_found ->
				(* Add current element to the current path *)
				Hashtbl.add current_path class_def.name true;
				try
					Hashtbl.find visited_before class_def.name;
					() (* This stops looking in the current heritage path *)
				with Not_found ->
					match class_def.parent with
					| None -> ()
					| Some p -> _sub current_path visited_before (get_classdef currentClassesEnv p (Location.none))
		in let visited = Hashtbl.create 10
		in let rec rec_check_circular_extends sub_env = 
			match sub_env with
			| [] -> ()
			| t::q -> 
				let current_path = Hashtbl.create 10
				in
				_sub current_path visited t; 
				Hashtbl.iter (fun k _ -> Hashtbl.add visited k true) current_path;
				rec_check_circular_extends q
		in rec_check_circular_extends env

	in let rec check_attr_names (attrs: varType list) =
		let rec _rec_check_current current_attr l =
			match l with 
			| [] -> ()
			| t::q when t.n = current_attr.n -> raise (PError(NamingError(t.n), t.loc))
			| t::q -> _rec_check_current current_attr q
		in match attrs with
		| [] -> ()
		| t::q ->
			_rec_check_current t q; 
			check_attr_names q

	in let rec check_methods_names (methods: methodType list) =
		let rec _rec_check_current (current_method: methodType) (l:methodType list) =
			match l with 
			| [] -> ()
			| t::q when t.name = current_method.name && t.params = current_method.params -> 
				raise (PError(NamingError(t.name), t.loc))
			| t::q -> _rec_check_current current_method q
		in match methods with
		| [] -> ()
		| t::q ->
			_rec_check_current t q; 
			check_methods_names q

	and purge_static_attrs (l: varType list) = match l with
		| [] -> []
		| attr::q when attr.static -> purge_static_attrs q
		| attr::q -> attr::(purge_static_attrs q)

	and purge_static_methods (l: methodType list) = match l with
		| [] -> []
		| m::q when m.static -> purge_static_methods q
		| m::q -> m::(purge_static_methods q)

	in let merge_attrs p_attrs attrs =
		let purged_p_attrs = purge_static_attrs p_attrs
		in let merge = purged_p_attrs@attrs
		in 
		check_attr_names merge;
		merge

	and merge_methods (p_methods: methodType list) (methods: methodType list) = 

		let purged_p_methods = purge_static_methods p_methods
		in let rec merge_each_method to_merge merged =

			let rec make_merge (sub_merged_methods: methodType list) (method_to_add: methodType) =
				match sub_merged_methods with
				| [] -> method_to_add::merged
				| m::q when m.name = method_to_add.name && m.params = method_to_add.params ->
					(* This is a redefinition. This can't be a method with the same signature as another method in the same class,
						for it has already been checked in a previous step in check_methods_names *)
					(* We check that the new return type is at least a child of the redefined method's return type *)
					(* Here, method_to_add comes from the parent, so its return type is the expected type *)
					check_type_is_legal currentClassesEnv (Some method_to_add.return) (Some m.return) m.loc;
					merged
				| m::q -> make_merge q method_to_add

			in match to_merge with
			| [] -> merged
			| t::q -> merge_each_method q (make_merge merged t)

		in merge_each_method purged_p_methods methods


	in let rec check_class_env class_env =
		match class_env with
			(* The env for that class has already been checked, return it as is. *)
		| c when Hashtbl.find table_done c.name -> class_env
			(* We do the checkings *)
		| c -> 
			Hashtbl.replace table_done c.name true;
			check_attr_names c.attributes;
			check_methods_names c.methods;
				(* Retrieve attributes and methods of the parent *)
			let p_attrs, p_methods = match c.parent with
				| None -> [], []
				| Some p_str -> 
					let p_env = check_class_env (get_classdef currentClassesEnv p_str (Location.none)) (* No possible error in get_classdef *)
					in p_env.attributes, p_env.methods
			in
			c.attributes <- merge_attrs p_attrs c.attributes;
			c.methods 	 <- merge_methods p_methods c.methods;
			c

	in let rec check_classes_env classes_env = match classes_env with
		| [] -> currentClassesEnv
		| t::q -> check_class_env t; check_classes_env q
	in
	init_table_done currentClassesEnv;
	check_circular_extends currentClassesEnv;
	check_classes_env currentClassesEnv


(* This function builds the methods and attributes definition environments of a class. 
	Classname is here the name-string of the class the method or attr belongs to *)
(* It returns a list of methodType and a list of varType *)
let rec build_shallow_methods_and_attrs_env currentClassesEnv methods_env attrs_env classname l_methods_attrs = 

	let _add_method_to_shallow_env m = 
		let build_method r n p static = {	
			name = Located.elem_of n; 
			return = type_of_classname currentClassesEnv (Located.elem_of r) (Located.loc_of r); 
			static = static;
			cl = classname;
			params = build_params_env currentClassesEnv p;
			loc = Located.loc_of m
		}
		in match Located.elem_of m with 
			| Method(r, n, p, _) -> (build_method r n p false)::methods_env
			| StaticMethod(r, n, p, _) -> (build_method r n p true)::methods_env

	and _add_attr_to_shallow_env c n static =
		{
			n=Located.elem_of n; 
			t=type_of_classname currentClassesEnv (Located.elem_of c) (Located.loc_of c); 
			attr=true; 
			static=static;
			loc=Located.loc_of n;
		}::attrs_env

	in match l_methods_attrs with
	| [] -> List.rev methods_env, List.rev attrs_env (* Reverse to retrieve the order of definition *)
	| t::q -> (match (Located.elem_of t) with 
			| Method _ | StaticMethod _ -> 
				build_shallow_methods_and_attrs_env currentClassesEnv (_add_method_to_shallow_env t) attrs_env classname q

			| Attr(c, n) | AttrWithValue(c, n, _) -> 
				build_shallow_methods_and_attrs_env currentClassesEnv methods_env (_add_attr_to_shallow_env c n false) classname q

			| StaticAttr(c, n) | StaticAttrWithValue(c, n, _) -> 
				build_shallow_methods_and_attrs_env currentClassesEnv methods_env (_add_attr_to_shallow_env c n true) classname q
		)


(* Change the class environment and add the methods and attributs defined in the classes, but not in their parents.
	Also, check if parents are defined.
	We don't check here if names of attributes or methods are not used twice. *)
let rec build_shallow_types_2 currentClassesEnv tree =
	match tree with
	| [] -> currentClassesEnv
	| t::q -> (match Located.elem_of t with 
			| Classdef (n, l) | ClassdefWithParent (n, _, l) -> 

				let methods, attrs = build_shallow_methods_and_attrs_env currentClassesEnv [] [] (Located.elem_of n) l
				and classdef = get_classdef currentClassesEnv (Located.elem_of n) (Located.loc_of n)
				and parent = (match Located.elem_of t with
					| Classdef _ -> Some "Object"
					| ClassdefWithParent (_, p, _) -> Some (type_of_classname currentClassesEnv (Located.elem_of p) (Located.loc_of p))
				) 
				in 
				classdef.methods <- methods;
				classdef.attributes <- attrs;
				classdef.parent <- parent;

				build_shallow_types_2 currentClassesEnv q

			| _ -> build_shallow_types_2 currentClassesEnv q
		)

(* Build a class environment with only the names of the classes defined in the file. *)
let rec build_shallow_types_1 shallowClassesEnv tree = 
	let rec _check_type_name n envToLookUp = match envToLookUp with
		| [] -> Located.elem_of n
			(* Class already exists *)
		| t::q when t.name = Located.elem_of n -> raise (PError(NamingError(Located.elem_of n), Located.loc_of n))
		| t::q -> _check_type_name n q
	in match tree with
	| [] -> shallowClassesEnv
	| t::q -> (match Located.elem_of t with 
			| Classdef (n, _) | ClassdefWithParent (n, _, _) -> 
				build_shallow_types_1 ({
					name=_check_type_name n shallowClassesEnv; 
					parent=None; 
					methods=[]; 
					attributes=[]
				}::shallowClassesEnv) q
			| _ -> build_shallow_types_1 shallowClassesEnv q
		)

(* This function builds the classes definition environment of the located structured tree in param *)
(* It returns a list of classTypeEnv *)
let build_classes_env tree = 
	let shallow_types_1 = build_shallow_types_1 static_classes_env tree
	in let shallow_types_2 = build_shallow_types_2 shallow_types_1 tree
	in let final_env = check_env shallow_types_2
	in
	List.rev final_env

