(* A word about static methods: they are NOT put in the methods environment 
	of a daughter class, because there is no such thing as a redefinition of 
	a static method. Static methods MUST only be called with : A.m(). a.m(), 
	with a being an instance of A and m a static method, will be rejected. *)

open Located
open Location
open Errors
open Structure

type exprType = 
	| ObjectType	(* For classes with no parent *)
	| IntType
	| BooleanType
	| StringType
	| CustomType of string

type varType = {
	n : string;
	t : exprType;
	attr : bool;
	static : bool;
}

(* Do we need location info ? Don't add it for now *)
type methodType = {
	name : string;
	mutable return : exprType;
	static : bool;
	mutable cl : exprType; (* Class the method belongs to. Can change in case of redefinition *)
	params : exprType list;
}

type classTypeEnv = {
	name : string;
	parent: exprType;
	methods : methodType list;
	attributes : varType list;
}

(* Copy a list of methodType structures *)
let rec copy_methods_types_list = function
	| [] -> []
	| t::q -> t.cl; (* Hack to recognize methodType *) {
		return = t.return;
		name = t.name;
		static = t.static;
		cl = t.cl;
		params = t.params;
	}::(copy_methods_types_list q)

(**************************************************************************************************)
(********** Redifinition of the parsing structure, to which we add the type information ***********)
type typed_expr = 
  | TypedNull
  | TypedThis
  | TypedInt of int Located.t * exprType
  | TypedBoolean of bool Located.t * exprType
  | TypedString of string Located.t * exprType
  | TypedVar of string Located.t * exprType
  | TypedAttrAffect of string Located.t * typed_expr Located.t * exprType
  | TypedUnop of unop Located.t * typed_expr Located.t * exprType
  | TypedBinop of binop Located.t * typed_expr Located.t * typed_expr Located.t * exprType
  | TypedLocal of classname Located.t * string Located.t * typed_expr Located.t * typed_expr Located.t 
  	* exprType
  | TypedCondition of typed_expr Located.t * typed_expr Located.t * typed_expr Located.t * exprType
  | TypedMethodCall of typed_expr Located.t * string Located.t * typed_expr Located.t list * exprType
  | TypedStaticMethodCall of classname Located.t * string Located.t * typed_expr Located.t list * exprType
    (* Static method calls are only applied ot classnames *)
  | TypedInstance of classname Located.t * exprType
  | TypedCast of classname Located.t * typed_expr Located.t * exprType
  | TypedInstanceof of typed_expr Located.t * classname Located.t * exprType

type typed_param = 
  | TypedParam of classname Located.t * string Located.t * exprType

type typed_attr_or_method = 
  | TypedAttr of classname Located.t * string Located.t * exprType
  | TypedAttrWithValue of classname Located.t * string Located.t * typed_expr Located.t * exprType
  | TypedMethod of classname Located.t * string Located.t * typed_param Located.t list * typed_expr Located.t 
  	* exprType
  | TypedStaticAttr of classname Located.t * string Located.t * exprType
  | TypedStaticAttrWithValue of classname Located.t * string Located.t * typed_expr Located.t * exprType
  | TypedStaticMethod of classname Located.t * string Located.t * typed_param Located.t list 
  	* typed_expr Located.t * exprType

type typed_class_or_expr = 
  | TypedClassdef of string Located.t * typed_attr_or_method Located.t list
  | TypedClassdefWithParent of string Located.t * classname Located.t * typed_attr_or_method Located.t list 
  | TypedExpr of typed_expr Located.t


let string_of_expr_type = function
	| ObjectType -> "Object"
	| IntType -> "Int"
	| BooleanType -> "Boolean"
	| StringType -> "String"
	| CustomType s -> s

let rec string_of_expr_types = function
	| [] -> ""
	| [t] -> (string_of_expr_type t)
	| t::q -> (string_of_expr_type t) ^ ", " ^ (string_of_expr_types q)

let make_error expr exp_type real_type = 
	raise (PError(
		TypeError(string_of_expr_type exp_type, string_of_expr_type real_type), 
		Located.loc_of expr))

(**************************************************************************************************)
(************************ These functions give the types of typed structures **********************)

let rec type_of_expr = function
	| TypedInt(_, t) -> t
	| TypedBoolean(_, t) -> t 
	| TypedString(_, t) -> t
	| TypedVar(_, t) -> t 
	| TypedAttrAffect(_, _, t) -> t 
	| TypedUnop(_, _, t) -> t 
	| TypedBinop(_, _, _, t) -> t 
	| TypedLocal(_, _, _, _, t) -> t 
	| TypedCondition(_, _, _, t) -> t 
	| TypedMethodCall(_, _, _, t) -> t 
	| TypedStaticMethodCall(_, _, _, t) -> t 
	| TypedInstance(_, t) -> t 
	| TypedCast(_, _, t) -> t 
	| TypedInstanceof(_, _, t) -> t 

let rec type_of_structure_tree tree = match tree with 
	| [] -> []
	| t::q -> (match (Located.elem_of t) with
			| TypedExpr e -> (type_of_expr (Located.elem_of e))::(type_of_structure_tree q)
			| _ -> type_of_structure_tree q
		)


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
let rec attributes_of_type currentClassEnv locCn = match currentClassEnv with 
	| [] -> raise (PError(UndefinedType(string_of_classname (Located.elem_of locCn)), Located.loc_of locCn))
	| t::q -> (match (Located.elem_of locCn) with
			| Classname s when (Located.elem_of s) = t.name -> t.attributes
			| _ -> attributes_of_type q locCn
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
let rec build_methods_and_attrs_env currentClassEnv methodsEnv attrsEnv classname elems = match elems with 
	| [] -> List.rev methodsEnv, List.rev attrsEnv (* Reverse to retrieve the order of definition *)
	| t::q -> (match (Located.elem_of t) with 
				(* The item is a method, we check its environment *)
			| Method(_, _, _, _) -> 
				build_methods_and_attrs_env currentClassEnv 
					(add_method_to_env currentClassEnv methodsEnv classname (Located.elem_of t)) 
					attrsEnv classname q
			| StaticMethod(_, _, _, _) -> 
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
				(* The item is not a method, don't add it to the methods environment *)
			(* | _ -> build_methods_and_attrs_env currentClassEnv methodsEnv attrsEnv classname q *)
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
					(attributes_of_type currentClassEnv p) 
					(Located.elem_of n) l 
			in 
			{name = Located.elem_of n ; 
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


(**************************************************************************************************)
(******************* These functions translate a structure into a typed structure *****************)

let check_type_is exp real e = 
	if (exp = real) then real else (make_error e exp real)

let rec get_var_type varEnv var_string loc checkAttr = match varEnv with 
	(* varEnv is a list of varType, and checkAttr is a boolean to make sure var is an attribute *)
	| [] -> raise (PError(UndefinedObject(var_string), loc))
	| t::q -> if (t.n = var_string && (checkAttr = false || (checkAttr && t.attr))) 
		then t.t else (get_var_type q var_string loc checkAttr)

let rec get_classdef classesEnv classname_string loc = 
	let s c = 
		if (c.name = classname_string) then true else false
	in match classesEnv with
	| [] -> raise (PError(UndefinedType(classname_string), loc))
	| t::q -> if (s t) then t else get_classdef q classname_string loc

(* args_types is a list of exprType *)
let rec get_methoddef classdef method_string args_types static loc = 
	let s c = 
		c.cl; if (c.name = method_string && c.params = args_types && c.static = static) then true else false
	in let rec list_of_string_types = function
		| [] -> []
		| t::q -> (string_of_expr_type t)::(list_of_string_types q)
	in let rec do_l = function 
		| [] -> raise (PError(UndefinedMethod(classdef.name, method_string, 
					(list_of_string_types args_types)), loc))
		| t::q -> if (s t) then t else do_l q
	in 
	do_l classdef.methods

let rec params_to_vartype classesEnv nparams = match nparams with 
	| [] -> []
	| t::q -> (match Located.elem_of t with 
			| TypedParam(_, s, t) -> {t=t; n=Located.elem_of s; attr=false; static=false;}
				::(params_to_vartype classesEnv q)
		)

(* This function receives a non-located expr and returns a non-located typed_expr *)
let rec type_expr classesEnv varEnv expr = 
	let type_unop u e = 
		let ne = type_expr classesEnv varEnv (Located.elem_of e) in 
		let bufType = match (Located.elem_of u) with
				| Udiff -> check_type_is BooleanType (type_of_expr ne) e
				| Uminus -> check_type_is IntType (type_of_expr ne) e
		in TypedUnop(u, Located.mk_elem ne (Located.loc_of e), bufType)

	and type_condition i t e = 
		let ni = type_expr classesEnv varEnv (Located.elem_of i) and
		nt = type_expr classesEnv varEnv (Located.elem_of t) and
		ne = type_expr classesEnv varEnv (Located.elem_of e) in
		check_type_is BooleanType (type_of_expr ni) i;
		TypedCondition(Located.mk_elem ni (Located.loc_of i),
			Located.mk_elem nt (Located.loc_of t),
			Located.mk_elem ne (Located.loc_of e),
			check_type_is (type_of_expr nt) (type_of_expr ne) e)

	and type_method_call e m args = 
		let rec do_l = function 
			| [] -> []
			| t::q -> (Located.mk_elem (type_expr classesEnv varEnv (Located.elem_of t)) 
				(Located.loc_of t))::(do_l q)
		and type_args = function
			| [] -> []
			| t::q -> (type_of_expr (Located.elem_of t))::(type_args q)
		and ne = type_expr classesEnv varEnv (Located.elem_of e)
		in let classdef = get_classdef classesEnv (string_of_expr_type (type_of_expr ne)) (Located.loc_of e)
		in let nargs = do_l args
		in let methoddef = get_methoddef classdef (Located.elem_of m) (type_args nargs) false (Located.loc_of m) 
		in TypedMethodCall(Located.mk_elem ne (Located.loc_of e), m, nargs, methoddef.return)

	and type_local_variable c v ve e =
		let nve = type_expr classesEnv varEnv (Located.elem_of ve)
		and classname_type = type_of_classname classesEnv (Located.elem_of c)
		in let ne = type_expr classesEnv ({t=check_type_is classname_type (type_of_expr nve) ve; 
			n=(Located.elem_of v); attr=false; static=false}::varEnv) (Located.elem_of e)
		in TypedLocal (c, v, Located.mk_elem nve (Located.loc_of ve), 
			Located.mk_elem ne (Located.loc_of e), type_of_expr ne)

	and type_attr_affect s e =
		(* TODO check var is an attribute, and not a local var *)
		let ne = type_expr classesEnv varEnv (Located.elem_of e)
		in let tne = type_of_expr ne
		in 
		check_type_is (get_var_type varEnv (Located.elem_of s) (Located.loc_of s) true) tne e;
		TypedAttrAffect(s, Located.mk_elem ne (Located.loc_of e), tne)

	in match expr with
  	| Null -> TypedNull
  	| This -> TypedThis
	| Int i -> TypedInt (i, IntType)
	| Boolean b -> TypedBoolean (b, BooleanType)
	| String s -> TypedString (s, StringType)
	| Unop (u, e) -> type_unop u e
	| Condition (i, t, e) -> type_condition i t e
	| Instance cn -> TypedInstance(cn, CustomType ((get_classdef classesEnv 
		(string_of_classname (Located.elem_of cn)) (Located.loc_of cn)).name))
	| MethodCall (e, m, args) -> type_method_call e m args
	| Instanceof (e, c) -> TypedInstanceof(Located.mk_elem (type_expr classesEnv varEnv (Located.elem_of e)) 
								(Located.loc_of e), c, BooleanType)
	| Local (c, v, ve, e) -> type_local_variable c v ve e
	| Var s -> TypedVar(s, get_var_type varEnv (Located.elem_of s) (Located.loc_of s) false)
	| AttrAffect (s, e) -> type_attr_affect s e

let rec type_params_list classesEnv params = match params with
	| [] -> []
	| t::q -> (match (Located.elem_of t) with 
			| Param(c, s) -> Located.mk_elem (TypedParam(c, s, type_of_classname classesEnv (Located.elem_of c))) 
					(Located.loc_of t)::(type_params_list classesEnv q)
		)

let rec type_attr_or_method_list classesEnv currentClassEnv l =

	let type_method c s params e static = 
		(* Check type of the expression is the return type of the method *)
		let nparams = type_params_list classesEnv params
		and return_type = type_of_classname classesEnv (Located.elem_of c)
		in let params_vartypes = params_to_vartype classesEnv nparams
		in let ne = type_expr classesEnv (currentClassEnv.attributes@params_vartypes) (Located.elem_of e)
		in
		check_type_is return_type (type_of_expr ne) e;
		if (static) then TypedStaticMethod(c, s, nparams, Located.mk_elem ne (Located.loc_of e), return_type)
			else TypedStaticMethod(c, s, nparams, Located.mk_elem ne (Located.loc_of e), return_type)

	and type_attr_with_value c s e static =
		(* Don't use other attributes in the expression of an attribute *)
		let ne = type_expr classesEnv [] (Located.elem_of e)
		in let tne = (type_of_expr ne)
		in 
		check_type_is (type_of_classname classesEnv (Located.elem_of c)) tne e;
		if (static) then TypedStaticAttrWithValue(c, s, Located.mk_elem ne (Located.loc_of e), tne) 
			else TypedAttrWithValue(c, s, Located.mk_elem ne (Located.loc_of e), tne)

	in let typed_attr_or_method = function
		| Attr (c, s) -> TypedAttr(c, s, type_of_classname classesEnv (Located.elem_of c))
		| StaticAttr (c, s) -> TypedStaticAttr(c, s, type_of_classname classesEnv (Located.elem_of c))
		| AttrWithValue (c, s, e) -> type_attr_with_value c s e false
		| StaticAttrWithValue (c, s, e) -> type_attr_with_value c s e true
		| Method (c, s, params, e) -> type_method c s params e false
		| StaticMethod (c, s, params, e) -> type_method c s params e true

	in match l with
	| [] -> []
	| t::q -> (Located.mk_elem (typed_attr_or_method (Located.elem_of t)) (Located.loc_of t))
				::(type_attr_or_method_list classesEnv currentClassEnv q)

(* This function receives a located list of class_or_expr, 
and returns a located list of typed_class_or_expr *)
let type_structure_tree tree = 
	let classesEnv = build_classes_env tree 
	in let rec type_rec_structure_tree sub_tree =
		(* This inner function receives a non-located class_or_expr *)
		let type_structure = function
			| Expr e -> TypedExpr (Located.mk_elem (type_expr classesEnv [] (Located.elem_of e)) (Located.loc_of e))
			| Classdef (s, l) -> TypedClassdef(s, type_attr_or_method_list classesEnv 
				(get_classdef classesEnv (Located.elem_of s) (Located.loc_of s)) l)
			| ClassdefWithParent (s, p, l) -> TypedClassdefWithParent(s, p, type_attr_or_method_list classesEnv 
				(get_classdef classesEnv (Located.elem_of s) (Located.loc_of s)) l)
		in match sub_tree with
		| [] -> []
		| t::q -> (Located.mk_elem (type_structure (Located.elem_of t)) (Located.loc_of t))
								::(type_rec_structure_tree q)
	in 
	type_rec_structure_tree tree 
