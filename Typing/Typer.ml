open Located
open Location
open Errors
open Structure

type exprType = 
	| IntType
	| BooleanType
	| StringType
	| Custom of string

(* Redifinition of the parsing structure, to which we add the type information *)
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
	| IntType -> "Int"
	| BooleanType -> "Boolean"
	| StringType -> "String"
	| Custom s -> s

let rec string_of_expr_types = function
	| [] -> ""
	| t::q -> (string_of_expr_type t) ^ "\n" ^ (string_of_expr_types q)

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
(******************* These functions translate a structure into a typed structure *****************)

(* This function receives a non-located expr and returns a non-located typed_expr *)
let rec type_expr = function
	| Int i -> TypedInt (i, IntType)
	| Boolean b -> TypedBoolean (b, BooleanType)
	| String s -> TypedString (s, StringType)
	| Unop (u, e) -> (let ne = type_expr (Located.elem_of e) in 
			let bufType = match (Located.elem_of u) with
				| Udiff -> (match (type_of_expr ne) with 
						| BooleanType -> BooleanType
						| _ as t -> make_error e BooleanType t
					)
				| Uminus -> (match (type_of_expr ne) with 
						| IntType -> IntType
						| _ as t -> make_error e IntType t
					)
			in 
			TypedUnop(u, Located.mk_elem ne (Located.loc_of e), bufType)
		)

(* This function receives a located list of class_or_expr, and returns a located list of typed_class_or_expr *)
let rec type_structure_tree tree = 
	(* This inner function receives a non-located class_or_expr *)
	let rec type_structure = function
		| Expr e -> TypedExpr (Located.mk_elem (type_expr (Located.elem_of e)) (Located.loc_of e))
	in match tree with 
	| [] -> []
	| t::q -> (Located.mk_elem (type_structure (Located.elem_of t)) (Located.loc_of t))::(type_structure_tree q)

