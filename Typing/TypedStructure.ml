open Structure

type varType = {
	n : string;
	t : string;
	attr : bool;
	static : bool;
}

(* Do we need location info ? Don't add it for now *)
type methodType = {
	name : string;
	mutable return : string;
	static : bool;
	mutable cl : string; (* Class the method belongs to. Can change in case of redefinition *)
	params : string list;
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
	}::(copy_methods_types_list q)

(**************************************************************************************************)
(********** Redifinition of the parsing structure, to which we add the type information ***********)
type typed_expr = 
  | TypedNull
  | TypedThis
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


(**************************************************************************************************)
(************************ These functions give the types of typed structures **********************)

let rec type_of_expr = function
	| TypedInt(_, t) | TypedBoolean(_, t) | TypedString(_, t) | TypedVar(_, t)
	| TypedAttrAffect(_, _, t) | TypedUnop(_, _, t) | TypedBinop(_, _, _, t) 
	| TypedLocal(_, _, _, _, t) | TypedCondition(_, _, _, t) | TypedMethodCall(_, _, _, t) 
	| TypedStaticMethodCall(_, _, _, t) | TypedInstance(_, t) | TypedCast(_, _, t) 
	| TypedInstanceof(_, _, t) -> t 

let rec type_of_structure_tree tree = match tree with 
	| [] -> []
	| t::q -> (match (Located.elem_of t) with
			| TypedExpr e -> (type_of_expr (Located.elem_of e))::(type_of_structure_tree q)
			| _ -> type_of_structure_tree q
		)