open Structure
open TypedStructure
open Errors

(**************************************************************************************************)
(******************** These functions build the classes definition environment ********************)

let type_of_classname currentClassEnv cn = match cn with 
	| Classname s when (Located.elem_of s) = "Int" ->  IntType
	| Classname s when (Located.elem_of s) = "Boolean" -> BooleanType
	| Classname s when (Located.elem_of s) = "String" -> StringType
	| Classname s -> CustomType (Located.elem_of s) 	
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

(* This function builds a list of exprType, based on a list of params *)
let rec build_params_env currentClassEnv p = 
	let rec build_param_env = function
		| Param (c, n) -> type_of_classname currentClassEnv (Located.elem_of c); 
	in match p with 
	| [] -> []
	| t::q -> (build_param_env (Located.elem_of t))::(build_params_env currentClassEnv q)

(* This function receives a non-located method and the method environment. 
It returns this environment updated with the new method. *)
let add_method_to_env currentClassEnv methodsEnv classname m = 
	(* TODO: error if redefinition of a method of the current class 
	(defined twice) ? Or not, juste overwrite... *)
	let rec check_env = function 
		(* Method doesn't already exist in the methodsEnv, we add it *)
		| [] -> (match m with 
				| Method(r, n, p, _) -> {name = Located.elem_of n; 
					return = type_of_classname currentClassEnv (Located.elem_of r); 
					static = false;
					cl = CustomType classname;
					params = (build_params_env currentClassEnv p)}::methodsEnv
				| StaticMethod(r, n, p, _) -> {name = Located.elem_of n; 
					return = type_of_classname currentClassEnv (Located.elem_of r); 
					static = true;
					cl = CustomType classname;
					params = (build_params_env currentClassEnv p)}::methodsEnv
			)
		(* Method already exists in the methodsEnv, we redefine it 
			(sort of in some cases, covered by tests) *)
		| t::q -> t.cl; (* Hack to make sure t is recognized as a methodType *)
			(match m with
				| Method(r, n, p, _) when ((Located.elem_of n) = t.name 
					&& (build_params_env currentClassEnv p) = t.params) -> 
					(* Redefinition of a method *)
					(t.cl <- CustomType classname;
					t.return <- type_of_classname currentClassEnv (Located.elem_of r);
					methodsEnv;)
				| StaticMethod(r, n, p, _) when ((Located.elem_of n) = t.name 
					&& (build_params_env currentClassEnv p) = t.params) -> 
					(* Redefinition of a method *)
					(t.cl <- CustomType classname;
					t.return <- type_of_classname currentClassEnv (Located.elem_of r);
					methodsEnv;)
				| _ -> check_env q
			)
	in check_env methodsEnv 

(* This function builds the methods definition environment of a class. 
The param is a located list of attr_or_methods *)
(* It returns a list of methodType *)
let rec build_methods_and_attrs_env currentClassEnv methodsEnv attrsEnv classname elems = 
	match elems with 
	| [] -> List.rev methodsEnv, List.rev attrsEnv (* Reverse to retrieve the order of definition *)
	| t::q -> (match (Located.elem_of t) with 
				(* The item is a method, we check its environment *)
			| Method _ | StaticMethod _ -> 
				build_methods_and_attrs_env currentClassEnv 
					(add_method_to_env currentClassEnv methodsEnv classname (Located.elem_of t)) 
					attrsEnv classname q
			| Attr(c, n) -> build_methods_and_attrs_env currentClassEnv methodsEnv 
								({n=Located.elem_of n; t=type_of_classname currentClassEnv (Located.elem_of c); 
									attr=true; static=false;}::attrsEnv) classname q
			| AttrWithValue(c, n, _) -> build_methods_and_attrs_env currentClassEnv methodsEnv 
								({n=Located.elem_of n; t=type_of_classname currentClassEnv (Located.elem_of c); 
									attr=true; static=false;}::attrsEnv) classname q
			| StaticAttr(c, n) -> build_methods_and_attrs_env currentClassEnv methodsEnv 
								({n=Located.elem_of n; t=type_of_classname currentClassEnv (Located.elem_of c); 
									attr=true; static=true;}::attrsEnv) classname q
			| StaticAttrWithValue(c, n, _) -> build_methods_and_attrs_env currentClassEnv methodsEnv 
								({n=Located.elem_of n; t=type_of_classname currentClassEnv (Located.elem_of c); 
									attr=true; static=true;}::attrsEnv) classname q
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
			{name = Located.elem_of n; parent = ObjectType; methods = methods; attributes = attrs}
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
				parent = type_of_classname currentClassEnv (Located.elem_of p) ;
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
	in List.rev (build_rec_classes_env [] tree)
