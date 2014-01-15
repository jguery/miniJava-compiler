open Option
open Structure
open TypedStructure
open Errors

(**************************************************************************************************)
(******************** These functions build the classes definition environment ********************)

(* Basic types classes' environment. Object is the only one to have no parent. *)
let static_classes_env = 
	[
		{name="Object"; parent=None; methods=[]; attributes=[]};
		{name="Int"; parent=Some "Object"; methods=[]; attributes=[]};
		{name="String"; parent=Some "Object"; methods=[]; attributes=[]};
		{name="Boolean"; parent=Some "Object"; methods=[]; attributes=[]};
	]

let type_of_classname currentClassEnv cn = match cn with 
	| Classname s -> Located.elem_of s
		(* TODO: check if the type already is in the env. Or later ? Since 
		classes of a same file are supposed to know each other recursively. 
		Yet, a parent needs to be defined before, and so we need to check to add
		the parents methods *)

(* This function takes a class environment and a located classname and
returns the methods associated to the classname in the env *)
let rec methods_of_type currentClassEnv withStaticMethods locCn = 
	let rec parse_methods methods = if (withStaticMethods) then methods else
		begin match methods with 
			| [] -> []
			| t::q -> if (t.static) then parse_methods q else t::(parse_methods q)
		end
	in match currentClassEnv with 
	| [] -> raise (PError(UndefinedType(string_of_classname (Located.elem_of locCn)), Located.loc_of locCn))
	| t::q -> (match (Located.elem_of locCn) with
			| Classname s when (Located.elem_of s) = t.name -> parse_methods t.methods
			| _ -> methods_of_type q withStaticMethods locCn
		)

(* This function takes a class environment and a located classname and
returns the attributes associated to the classname in the env *)
let rec attributes_of_type currentClassEnv withStaticAttrs locCn = 
	let rec parse_attrs attrs = if (withStaticAttrs) then attrs else
		begin match attrs with 
			| [] -> []
			| t::q -> t.t; if (t.static) then parse_attrs q else t::(parse_attrs q)
		end
	in match currentClassEnv with 
	| [] -> raise (PError(UndefinedType(string_of_classname (Located.elem_of locCn)), Located.loc_of locCn))
	| t::q -> (match (Located.elem_of locCn) with
			| Classname s when (Located.elem_of s) = t.name -> parse_attrs t.attributes
			| _ -> attributes_of_type q withStaticAttrs locCn
		)

(* This function builds a list of string types, based on a list of params *)
let rec build_params_env currentClassEnv p = 
	let rec build_param_env = function
		| Param (c, n) -> type_of_classname currentClassEnv (Located.elem_of c)
	in match p with 
	| [] -> []
	| t::q -> (build_param_env (Located.elem_of t))::(build_params_env currentClassEnv q)


(* This function receives a non-located method and the method environment. 
It returns this environment updated with the new method. *)
let add_method_to_env currentClassEnv methodsEnv classname m = 

	(* This inner function checks if a redefinition is taking place, and if it is legal. 
	If so, redefines and returns true. Otherwise returns false. *)
	let check_redefinition r n p methodType = 
		methodType.cl; (* Hack *)
		if ((Located.elem_of n) = methodType.name && (build_params_env currentClassEnv p) = methodType.params) then begin
			match methodType.cl with 
				(* Trying to redefine an method already defined in the SAME class... *)
			| s when s = classname -> raise (PError(Errors.NamingError(Located.elem_of n), Located.loc_of n))
				(* Trying to redefine a method from a parent (s can't be anything else than the parent here) *)
			| s when s <> classname -> 
					(* TODO: check return type is a parent, but can't make it in the same pass..... SHIT *)

					methodType.cl <- classname;
					methodType.return <- type_of_classname currentClassEnv (Located.elem_of r);
					true
		end else
			false

	(* We check the methods environment and see if a method of the same signature doesn't already exists. *)
	in let rec check_env = function 
		(* Method doesn't already exist in the methodsEnv, we add it *)
		| [] -> 
			let build_method r n p static = 
				{	
					name = Located.elem_of n; 
					return = type_of_classname currentClassEnv (Located.elem_of r); 
					static = static;
					cl = classname;
					params = (build_params_env currentClassEnv p)
				}
			in (match m with 
				| Method(r, n, p, _) -> (build_method r n p false)::methodsEnv
				| StaticMethod(r, n, p, _) -> (build_method r n p true)::methodsEnv
			)
		(* Method already exists in the methodsEnv, we redefine it 
			(sort of in some cases, covered by tests) *)
		| t::q -> t.cl; (* Hack to make sure t is recognized as a methodType *)
			(match m with
				| Method(r, n, p, _) -> if (check_redefinition r n p t) then methodsEnv else check_env q
				| _ -> check_env q
			)
	in check_env methodsEnv 

(* This function builds the methods definition environment of a class. 
The param is a located list of attr_or_methods. Classname is here the name-string 
of the class the method or attr belongs to *)
(* It returns a list of methodType *)
let rec build_methods_and_attrs_env currentClassEnv methodsEnv attrsEnv classname elems = 
	let rec add_attr_to_env env c n static = 
		match env with 
		| [] -> {n=Located.elem_of n; t=type_of_classname currentClassEnv (Located.elem_of c); 
					attr=true; static=static;}::attrsEnv
		| t::q when t.n = (Located.elem_of n) -> raise (PError(Errors.NamingError(t.n), Located.loc_of n))
		| t::q -> add_attr_to_env q c n static

	in match elems with 
		(* Reverse to retrieve the order of definition *)
	| [] -> List.rev methodsEnv, List.rev attrsEnv 
	| t::q -> (match (Located.elem_of t) with 
				(* The item is a method, we check its environment *)
			| Method _ | StaticMethod _ -> 
				build_methods_and_attrs_env currentClassEnv 
					(add_method_to_env currentClassEnv methodsEnv classname (Located.elem_of t)) 
					attrsEnv classname q

			| Attr(c, n) | AttrWithValue(c, n, _) -> 
				build_methods_and_attrs_env currentClassEnv methodsEnv (add_attr_to_env attrsEnv c n false) classname q

			| StaticAttr(c, n) | StaticAttrWithValue(c, n, _) -> 
				build_methods_and_attrs_env currentClassEnv methodsEnv (add_attr_to_env attrsEnv c n true) classname q
		)	 

let rec build_shallow_types shallowClassesEnv tree = 
	let rec check_type_name n envToLookUp = match envToLookUp with
		| [] -> Located.elem_of n
			(* Class already exists *)
		| t::q when t.name = Located.elem_of n -> raise (PError(NamingError(Located.elem_of n), Located.loc_of n))
		| t::q -> check_type_name n q
	in match tree with
	| [] -> []
	| t::q -> (match Located.elem_of t with 
			| Classdef (n, _) | ClassdefWithParent (n, _, _) -> 
				{name=check_type_name n shallowClassesEnv; parent=None; methods=[]; attributes=[]} 
					::(build_shallow_types shallowClassesEnv q)
			| _ -> build_shallow_types shallowClassesEnv q
		)

(* This function builds the classes definition environment of the located structured tree in param *)
(* It returns a list of classTypeEnv *)
let build_classes_env tree = 
	(* This inner function receives a non-located structure, 
	which is either a Classdef or a ClassdefWithParent. It returns a classTypeEnv *)
	let rec build_class_env currentClassEnv c = match c with 
		| Classdef(n, l) -> let (methods, attrs) = 
			build_methods_and_attrs_env currentClassEnv [] [] (Located.elem_of n) l
			in 
			{name = Located.elem_of n; parent = Some "Object"; methods = methods; attributes = attrs}
		| ClassdefWithParent(n, p, l) -> let (methods, attrs) =
			(* Use copy_methods_types_list to get an independent copy of the parent methods *)
			(* Yet, no need to copy the attributes list since we never change them in a son class *)
			build_methods_and_attrs_env currentClassEnv 
					(copy_methods_types_list (methods_of_type currentClassEnv false p)) 
					(attributes_of_type currentClassEnv false p) 
					(Located.elem_of n) l 
			in 
			{
				name = Located.elem_of n ; 
				parent = Some (type_of_classname currentClassEnv (Located.elem_of p));
				methods = methods;
				attributes = attrs;
			}
	in let rec build_rec_classes_env env tr = match tr with 
		| [] -> env
		| t::q -> (match (Located.elem_of t) with 
					(* The structure is an expression, don't add it to the class environment *)
				| Expr e -> build_rec_classes_env env q
					(* The structure is a class definition, we check its environment *)
				| _ -> build_rec_classes_env ((build_class_env env (Located.elem_of t))::env) q
			)
	(* Use this because we need to access the environment at any moment *)
	in List.rev (build_rec_classes_env static_classes_env tree)
