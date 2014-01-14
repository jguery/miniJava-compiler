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