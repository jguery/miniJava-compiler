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

(* Do we need location info ? Don't add it for now *)
type methodType = {
	name : string;
	return : exprType;
	static : bool;
	mutable cl : exprType;
	params : exprType list;
}

type classTypeEnv = {
	name : string;
	parent: exprType;
	methods : methodType list
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

let rec type_of_structure_tree tree = 
	let rec type_of_structure = function
		| TypedExpr e -> type_of_expr (Located.elem_of e)
	in match tree with 
	| [] -> []
	| t::q -> (type_of_structure (Located.elem_of t))::(type_of_structure_tree q)


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
let rec methods_of_type currentClassEnv locCn = match currentClassEnv with 
	| [] -> raise (PError(Undefined(string_of_classname (Located.elem_of locCn)), Located.loc_of locCn))
	| t::q -> (match (Located.elem_of locCn) with
			| Classname s when (Located.elem_of s) = t.name -> t.methods
			| _ -> methods_of_type q locCn
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
		| [] -> (match m with 
				| Method(r, n, p, _) -> {name = Located.elem_of n; 
					return = type_of_classname currentClassEnv (Located.elem_of r); 
					static = false;
					cl = CustomType classname;
					params = (build_params_env currentClassEnv p)}::methodsEnv
				(* | StaticMethod(r, n, p, _) -> *)
			)
		| t::q -> t.cl; (* Hack to make sure t is recognized as a methodType *)
			(match m with
				| Method(r, n, p, _) when ((Located.elem_of n) = t.name 
					&& (type_of_classname currentClassEnv (Located.elem_of r)) = t.return
					&& (build_params_env currentClassEnv p) = t.params) -> 
					(t.cl <- CustomType classname; methodsEnv)
				(* | StaticMethod(r, n, p, _) -> *)
				| _ -> check_env q
			)
	in check_env methodsEnv 

(* This function builds the methods definition environment of a class. 
The param is a located list of attr_or_methods *)
(* It returns a list of methodType *)
let rec build_methods_env currentClassEnv methodsEnv classname elems = match elems with 
	| [] -> List.rev methodsEnv (* Reverse to retrieve the order of definition *)
	| t::q -> (match (Located.elem_of t) with 
				(* The item is a method, we check its environment *)
			| Method(_, _, _, _) -> 
				build_methods_env currentClassEnv 
					(add_method_to_env currentClassEnv methodsEnv classname (Located.elem_of t)) 
					classname 
					q
			| StaticMethod(_, _, _, _) -> 
				build_methods_env currentClassEnv 
					(add_method_to_env currentClassEnv methodsEnv classname (Located.elem_of t)) 
					classname 
					q
				(* The item is not a method, don't add it to the methods environment *)
			| _ -> build_methods_env currentClassEnv methodsEnv classname q
		)	 

(* This function builds the classes definition environment of the located structured tree in param *)
(* It returns a list of classTypeEnv *)
let build_classes_env tree = 
	(* This inner function receives a non-located structure, 
	which is either a Classdef or a ClassdefWithParent. It returns a classTypeEnv *)
	let rec build_class_env currentClassEnv c = match c with 
		| Classdef(n, l) -> {name = Located.elem_of n ; parent = ObjectType ; 
			methods = (build_methods_env currentClassEnv [] (Located.elem_of n) l)}
		| ClassdefWithParent(n, p, l) -> {name = Located.elem_of n ; 
			parent = type_of_classname currentClassEnv (Located.elem_of p) ;
			methods = 
				(* Use copy_methods_types_list to get an independent copy of the parent methods *)
				build_methods_env currentClassEnv 
					(copy_methods_types_list (methods_of_type currentClassEnv p)) 
					(Located.elem_of n) l 
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

(* The classname in params is located. *)
let rec search_classname classEnv classname = 
	let s c = 
		if (c.name = (string_of_classname (Located.elem_of classname))) then true else false
	in match classEnv with
	| [] -> raise (PError(Undefined(string_of_classname (Located.elem_of classname)), 
				Located.loc_of classname))
	| t::q -> if (s t) then CustomType (t.name) else search_classname q classname 


(* This function receives a non-located expr and returns a non-located typed_expr *)
let rec type_expr classEnv expr = 
	let type_unop u e = 
		let ne = type_expr classEnv (Located.elem_of e) in 
		let bufType = match (Located.elem_of u) with
				| Udiff -> check_type_is BooleanType (type_of_expr ne) e
				| Uminus -> check_type_is IntType (type_of_expr ne) e
			in TypedUnop(u, Located.mk_elem ne (Located.loc_of e), bufType)

	and type_condition i t e = 
		let ni = type_expr classEnv (Located.elem_of i) and
		nt = type_expr classEnv (Located.elem_of t) and
		ne = type_expr classEnv (Located.elem_of e) in
		check_type_is BooleanType (type_of_expr ni) i;
		TypedCondition(Located.mk_elem ni (Located.loc_of i),
			Located.mk_elem nt (Located.loc_of t),
			Located.mk_elem ne (Located.loc_of e),
			check_type_is (type_of_expr nt) (type_of_expr ne) e)

	in match expr with
	| Int i -> TypedInt (i, IntType)
	| Boolean b -> TypedBoolean (b, BooleanType)
	| String s -> TypedString (s, StringType)
	| Unop (u, e) -> type_unop u e
	| Condition (i, t, e) -> type_condition i t e
	| Instance cn -> TypedInstance(cn, search_classname classEnv cn)
	(* | MethodCall (e, m, args) ->  *)
  (* | MethodCall of expr Located.t * string Located.t * expr Located.t list *)


(* This function receives a located list of class_or_expr, 
and returns a located list of typed_class_or_expr *)
let type_structure_tree tree = 
	let classEnv = build_classes_env tree 
	(* This inner function receives a non-located class_or_expr *)
	in let rec type_structure = function
		| Expr e -> TypedExpr (Located.mk_elem (type_expr classEnv (Located.elem_of e)) (Located.loc_of e))
	in let rec type_rec_structure_tree = function
		| [] -> []
		| t::q -> (Located.mk_elem (type_structure (Located.elem_of t)) (Located.loc_of t))
				::(type_rec_structure_tree q)
	in 
	type_rec_structure_tree tree 
