open Structure
open Errors

type varType = {
	n : string;
	t : string;
	attr : bool;
	static : bool;
	loc: Location.t;
}

(* Do we need location info ? Don't add it for now *)
type methodType = {
	name : string;
	mutable return : string;
	static : bool;
	mutable cl : string;  (* TODO remove this: no use in the typer *) (* Class the method belongs to. Can change in case of redefinition *)
	params : string list;
	loc: Location.t;
}

type classTypeEnv = {
	name : string;
	mutable parent: string option;		(* None is ONLY for the Object class *)
	mutable methods : methodType list;
	mutable attributes : varType list;
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
		loc = t.loc;
	}::(copy_methods_types_list q)

(**************************************************************************************************)
(********** Redifinition of the parsing structure, to which we add the type information ***********)
type typed_expr = 
  | TypedNull
  | TypedThis of string
  | TypedInt of int Located.t * string
  | TypedBoolean of bool Located.t * string
  | TypedString of string Located.t * string
  | TypedVar of string Located.t * string
  | TypedAttrAffect of string Located.t * typed_expr Located.t * string
  | TypedUnop of unop Located.t * typed_expr Located.t * string
  | TypedBinop of binop Located.t * typed_expr Located.t * typed_expr Located.t * string
  | TypedLocal of classname Located.t * string Located.t * typed_expr Located.t * typed_expr Located.t 
  	* string
  | TypedCondition of typed_expr Located.t * typed_expr Located.t * typed_expr Located.t * string
  | TypedMethodCall of typed_expr Located.t * string Located.t * typed_expr Located.t list * string
  | TypedStaticMethodCall of classname Located.t * string Located.t * typed_expr Located.t list * string
    (* Static method calls are only applied ot classnames *)
  | TypedInstance of classname Located.t * string
  | TypedCast of classname Located.t * typed_expr Located.t * string
  | TypedInstanceof of typed_expr Located.t * classname Located.t * string

type typed_param = 
  | TypedParam of classname Located.t * string Located.t * string

type typed_attr_or_method = 
  | TypedAttr of classname Located.t * string Located.t * string
  | TypedAttrWithValue of classname Located.t * string Located.t * typed_expr Located.t * string
  | TypedMethod of classname Located.t * string Located.t * typed_param Located.t list * typed_expr Located.t 
  	* string
  | TypedStaticAttr of classname Located.t * string Located.t * string
  | TypedStaticAttrWithValue of classname Located.t * string Located.t * typed_expr Located.t * string
  | TypedStaticMethod of classname Located.t * string Located.t * typed_param Located.t list 
  	* typed_expr Located.t * string

type typed_class_or_expr = 
  | TypedClassdef of string Located.t * typed_attr_or_method Located.t list
  | TypedClassdefWithParent of string Located.t * classname Located.t * typed_attr_or_method Located.t list 
  | TypedExpr of typed_expr Located.t


let string_of_expr_type t =
	t

let rec string_of_expr_types = function
	| [] -> ""
	| [t] -> (string_of_expr_type t)
	| t::q -> (string_of_expr_type t) ^ ", " ^ (string_of_expr_types q)


let make_type_error exp_type real_type loc = 
	raise (PError(TypeError(Option.get exp_type, Option.get real_type), loc))

(* Retrieve a class definition from the classes environment, with its name. *)
let rec get_classdef classesEnv classname_string loc = 
	let s c = 
		if (c.name = classname_string) then true else false
	in match classesEnv with
	| [] -> raise (PError(UndefinedType(classname_string), loc))
	| t::q -> if (s t) then t else get_classdef q classname_string loc

(* args_types is a list of strings *)
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

(* Check if a type is the parent of another type *)
(* Parent and daughter are of type string option *)
let rec is_parent classesEnv parent daughter =
	match parent, daughter with 
	| None, Some "Object" -> true
	| None, _ -> false
	| _, None -> false
	| Some "Object", Some "Object" -> false
	| Some "Object", Some _ -> true
	| Some _, Some "Object" -> false
	| _, Some nd -> 
		let classdef_daughter = get_classdef classesEnv nd Location.none
		in if (classdef_daughter.parent = parent) then true else 
			(* We don't care about the location here, since it is not possible that get_classdef 
				raises an error. The error would have been signaled when building the classes environment *)
			is_parent classesEnv parent classdef_daughter.parent

let rec find_lowest_common_ancestor classesEnv c1 c2 = 
	match c1, c2 with
	| "Object", "Object" -> "Object"
	| n1, n2 when n1 = n2 -> n1
	| n1, n2 ->
		let classdef_1 = get_classdef classesEnv n1 Location.none
		and classdef_2 = get_classdef classesEnv n2 Location.none
		in if classdef_1.parent = classdef_2.parent then 
			Option.get classdef_1.parent
		else if is_parent classesEnv (Some c1) (Some c2)  then
			n1
		else if is_parent classesEnv (Some c2) (Some c1) then 
			n2
		else 
			find_lowest_common_ancestor classesEnv (Option.get classdef_1.parent) (Option.get classdef_2.parent)


(* This method makes sure the expected type is either the real type, or a parent of the real type *)
(* exp and real are of type string option *)
(* It returns the expected type, a string, if it is legal. Raises an exception otherwise *)
let check_type_is_legal classesEnv exp real loc = 
	if (exp = real || is_parent classesEnv exp real) then Option.get exp else  
		make_type_error exp real loc


(* This function builds a list of string types, based on a list of located typed params *)
let rec params_types params = 
	let param_type = function
		| TypedParam (_, _, t) -> t
	in match params with 
	| [] -> []
	| t::q -> (param_type (Located.elem_of t))::(params_types q)


(* This function extracts the names of the params, which is a list of located typed params *)
let rec params_names params = 
	let param_name = function
		| TypedParam (_, n, _) -> Located.elem_of n
	in match params with
	| [] -> []
	| t::q -> (param_name (Located.elem_of t))::(params_names q)

(**************************************************************************************************)
(************************ These functions give the types of typed structures **********************)

let type_of_expr = function
	| TypedInt(_, t) | TypedBoolean(_, t) | TypedString(_, t) | TypedVar(_, t)
	| TypedAttrAffect(_, _, t) | TypedUnop(_, _, t) | TypedBinop(_, _, _, t) 
	| TypedLocal(_, _, _, _, t) | TypedCondition(_, _, _, t) | TypedMethodCall(_, _, _, t) 
	| TypedStaticMethodCall(_, _, _, t) | TypedInstance(_, t) | TypedCast(_, _, t) 
	| TypedInstanceof(_, _, t) | TypedThis t -> t 
		(* Null is a very special case which needs to be treated independently in most cases *)
	| TypedNull -> "null"

let rec types_of_expressions = function
	| [] -> []
	| t::q -> (type_of_expr (Located.elem_of t))::(types_of_expressions q)

let rec type_of_structure_tree tree = match tree with 
	| [] -> []
	| t::q -> (match (Located.elem_of t) with
			| TypedExpr e -> (type_of_expr (Located.elem_of e))::(type_of_structure_tree q)
			| _ -> type_of_structure_tree q
		)