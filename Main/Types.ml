open Located

type binop =
  | Bsemicol | Binf | BinfEq | Bsup | Bsupeq | Bdiff | Beq 
  | Badd | Bsub | Bmul | Bdiv | Bmod | Band | Bor

type unop =
  | Udiff 
  | Uminus

type classname =
  | Classname of string Located.t (* Name of a class, which has to be defined, otherwise the compiler will fail (later)  *)
  (*| IntType 
  | BooleanType
  | StringType *)

type expr = 
  | Null
  | This
  | Int of int Located.t
  | Boolean of bool Located.t
  | String of string Located.t
  | Var of string Located.t
  | AttrAffect of string Located.t * expr Located.t
  | Unop of unop Located.t * expr Located.t
  | Binop of binop Located.t * expr Located.t * expr Located.t
  | Local of classname Located.t * string Located.t * expr Located.t * expr Located.t
    (* Defines an expression used locally *)
  | Condition of expr Located.t * expr Located.t * expr Located.t
  | MethodCall of expr Located.t * string Located.t * expr Located.t list
  | StaticMethodCall of classname Located.t * string Located.t * expr Located.t list
    (* Static method calls are only applied ot classnames *)
  | Instance of classname Located.t
  | Cast of classname Located.t * expr Located.t
  | Instanceof of expr Located.t * classname Located.t

type param = 
  | Param of classname Located.t * string Located.t

type attr_or_method = 
  | Attr of classname Located.t * string Located.t
  | AttrWithValue of classname Located.t * string Located.t * expr Located.t
  | Method of classname Located.t * string Located.t * param Located.t list * expr Located.t
  | StaticAttr of classname Located.t * string Located.t
  | StaticAttrWithValue of classname Located.t * string Located.t * expr Located.t
  | StaticMethod of classname Located.t * string Located.t * param Located.t list * expr Located.t

type class_or_expr = 
  | Classdef of string Located.t * attr_or_method Located.t list (* No parent, the parent is the Object class *)
  | ClassdefWithParent of string Located.t * classname Located.t * attr_or_method Located.t list
  | Expr of expr Located.t

  (* | Expression of expression *)
