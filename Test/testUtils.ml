open Located
open Structure
open Typer

let mk_none x = 
	Located.mk_elem x (Location.none)

let mk_param t =
	mk_none (Param(mk_none (Classname(mk_none t)), mk_none "foo"))

let mk_param_n t n =
	mk_none (Param(mk_none (Classname(mk_none t)), mk_none n))

let mk_attr c s = 
	mk_none (Attr(mk_none (Classname(mk_none c)), mk_none s))

let mk_attr_v c s e = 
	mk_none (AttrWithValue(mk_none (Classname(mk_none c)), mk_none s, mk_none e))

let mk_sattr c s = 
	mk_none (StaticAttr(mk_none (Classname(mk_none c)), mk_none s))

let mk_sattr_v c s e = 
	mk_none (StaticAttrWithValue(mk_none (Classname(mk_none c)), mk_none s, mk_none e))

let mk_method return name params =
	mk_none (Method(mk_none (Classname (mk_none return)), 
			mk_none name, params, mk_none (Int (mk_none 1))))

let mk_smethod return name params =
	mk_none (StaticMethod(mk_none (Classname (mk_none return)), 
			mk_none name, params, mk_none (Int (mk_none 1))))

let mk_method_e return name params expr =
	mk_none (Method(mk_none (Classname (mk_none return)), 
			mk_none name, params, mk_none expr))

let mk_smethod_e return name params expr =
	mk_none (StaticMethod(mk_none (Classname (mk_none return)), 
			mk_none name, params, mk_none expr))

let mk_class classname methods =
	mk_none (Classdef(mk_none classname, methods))

let mk_class_p classname parent methods =
	mk_none (ClassdefWithParent(mk_none classname, mk_none (Classname(mk_none parent)), methods))


let rec string_of_attributes_env = function
	| [] -> ""
	| t::q -> "name: " ^ t.n ^ " type: " ^ (string_of_expr_type t.t) ^ "; " 
		^ (string_of_attributes_env q)

let rec string_of_methods_env = function
	| [] -> ""
	| t::q -> t.cl;"Name " ^ t.name ^ " class " ^ (string_of_expr_type t.cl) 
		^ " params [" ^ (string_of_expr_types t.params) ^ "]; " ^ (string_of_methods_env q) 

let rec string_of_env = function
	| [] -> ""
	| t::q -> "Class " ^ t.name ^ " parent " ^ (string_of_expr_type t.parent) 
		^ " attributes : [" ^ (string_of_attributes_env t.attributes)
		^ "] methods : [" ^ (string_of_methods_env t.methods) ^ "]\n" ^ (string_of_env q)