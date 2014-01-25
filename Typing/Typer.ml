(* A word about static methods: they are NOT put in the methods environment 
	of a daughter class, because there is no such thing as a redefinition of 
	a static method. Static methods MUST only be called with : A.m(). a.m(), 
	with a being an instance of A and m a static method, will be rejected. 
	In the same way, only the static attributes can be seen in a static method.
	Yet, a normal method can see static attributes. Also, static attributes are not
	copied in a daughter class. *)

open Option
open Located
open Location
open Errors
open Structure
open TypedStructure
open ClassesEnv


(**************************************************************************************************)
(******************* These functions translate a structure into a typed structure *****************)

let rec get_var_type varEnv var_string loc checkAttr = match varEnv with 
	(* varEnv is a list of varType, and checkAttr is a boolean to make sure var is an attribute *)
	| [] -> raise (PError(UndefinedObject(var_string), loc))
	| t::q -> if (t.n = var_string && (checkAttr = false || (checkAttr && t.attr))) 
		then t.t else (get_var_type q var_string loc checkAttr)

let rec params_to_vartype classesEnv nparams = match nparams with 
	| [] -> []
	| h::q -> (match Located.elem_of h with 
			| TypedParam(_, s, t) -> {t=t; n=Located.elem_of s; attr=false; static=false; loc=Located.loc_of h}
				::(params_to_vartype classesEnv q)
		)

(* This function receives an expr and returns a non-located typed_expr *)
(* Classname_str is the name of the class the expression is in, if any. *)
(* Static_m is true if we are evaluating an expression in a static method. *)
let rec type_expr classname_str static_m classesEnv varEnv expr = 
	let type_unop u e = 
		let ne = type_expr classname_str static_m classesEnv varEnv e in 
		let bufType = match (Located.elem_of u) with
				| Udiff -> check_type_is_legal classesEnv (Some "Boolean") (Some (type_of_expr ne)) (Located.loc_of e)
				| Uminus -> check_type_is_legal classesEnv (Some "Int") (Some (type_of_expr ne)) (Located.loc_of e)
		in TypedUnop(u, Located.mk_elem ne (Located.loc_of e), bufType)

	and type_binop b e1 e2 =
		let ne1 = type_expr classname_str static_m  classesEnv varEnv e1
		and ne2 = type_expr classname_str static_m  classesEnv varEnv e2
		in let bufType = match (Located.elem_of b) with
				| Bsemicol -> type_of_expr ne2
				| Badd | Bsub | Bmul | Bdiv | Bmod -> 
					check_type_is_legal classesEnv (Some "Int") (Some (type_of_expr ne1)) (Located.loc_of e1);
					check_type_is_legal classesEnv (Some "Int") (Some (type_of_expr ne2)) (Located.loc_of e2)
				| Binf | Binfeq | Bsup | Bsupeq ->
					check_type_is_legal classesEnv (Some "Int") (Some (type_of_expr ne1)) (Located.loc_of e1);
					check_type_is_legal classesEnv (Some "Int") (Some (type_of_expr ne2)) (Located.loc_of e2);
					"Boolean"
				| Bdiff | Beq -> 
					check_type_is_legal classesEnv (Some (type_of_expr ne1)) (Some (type_of_expr ne2)) (Located.loc_of e2); 
					"Boolean"
				| Band | Bor -> 
					check_type_is_legal classesEnv (Some "Boolean") (Some (type_of_expr ne1)) (Located.loc_of e1);
					check_type_is_legal classesEnv (Some "Boolean") (Some (type_of_expr ne2)) (Located.loc_of e2)
		in TypedBinop(b, Located.mk_elem ne1 (Located.loc_of e1), 
			Located.mk_elem ne2 (Located.loc_of e2), bufType)

	and type_condition i t e = 
		let ni = type_expr classname_str static_m  classesEnv varEnv i 
		and nt = type_expr classname_str static_m  classesEnv varEnv t 
		and ne = type_expr classname_str static_m  classesEnv varEnv e 
		in let common_ancestor = find_lowest_common_ancestor classesEnv (type_of_expr nt) (type_of_expr ne)
		in
		check_type_is_legal classesEnv (Some "Boolean") (Some (type_of_expr ni)) (Located.loc_of i);
		TypedCondition(Located.mk_elem ni (Located.loc_of i),
			Located.mk_elem nt (Located.loc_of t),
			Located.mk_elem ne (Located.loc_of e),
			common_ancestor)

	and type_method_call e m args = 
		let rec do_l = function 
			| [] -> []
			| t::q -> (Located.mk_elem (type_expr classname_str static_m  classesEnv varEnv t) 
				(Located.loc_of t))::(do_l q)
		and type_args = function
			| [] -> []
			| t::q -> (type_of_expr (Located.elem_of t))::(type_args q)
		and ne = type_expr classname_str static_m  classesEnv varEnv e
		in let classdef = get_classdef classesEnv (type_of_expr ne) (Located.loc_of e)
		in let nargs = do_l args
		in let methoddef = get_methoddef classdef (Located.elem_of m) (type_args nargs) false (Located.loc_of m) 
		in TypedMethodCall(Located.mk_elem ne (Located.loc_of e), m, nargs, methoddef.return)

	and type_local_variable c v ve e =
		let nve = type_expr classname_str static_m  classesEnv varEnv ve
		and classname_type = type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c) 
		in let ne = type_expr classname_str static_m  classesEnv ({
				t=check_type_is_legal classesEnv (Some classname_type) (Some (type_of_expr nve)) (Located.loc_of ve); 
				n=(Located.elem_of v); 
				attr=false; 
				static=false;
				loc=Located.loc_of v;
			}::varEnv) e
		in TypedLocal (c, v, Located.mk_elem nve (Located.loc_of ve), 
			Located.mk_elem ne (Located.loc_of e), type_of_expr ne)

	and type_attr_affect s e =
		(* TODO check var is an attribute, and not a local var *)
		let ne = type_expr classname_str static_m classesEnv varEnv e
		in let tne = type_of_expr ne
		and ta = get_var_type varEnv (Located.elem_of s) (Located.loc_of s) true
		in 
		check_type_is_legal classesEnv (Some ta) (Some tne) (Located.loc_of e);
		TypedAttrAffect(s, Located.mk_elem ne (Located.loc_of e), ta)

	and type_static_method_call c m args =
		let rec do_l = function 
			| [] -> []
			| t::q -> (Located.mk_elem (type_expr classname_str static_m  classesEnv varEnv t) 
				(Located.loc_of t))::(do_l q)
		and type_args = function
			| [] -> []
			| t::q -> (type_of_expr (Located.elem_of t))::(type_args q)
		in let classdef = get_classdef classesEnv (string_of_classname (Located.elem_of c)) (Located.loc_of c)
		in let nargs = do_l args
		in let methoddef = get_methoddef classdef (Located.elem_of m) (type_args nargs) true (Located.loc_of m) 
		in TypedStaticMethodCall(c, m, nargs, methoddef.return)

	and type_cast c e =
		let type_to = type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c) 
		and ne = type_expr classname_str static_m classesEnv varEnv e
		in let tne = type_of_expr ne
		in 
		(* At this stage, casting is authorized if there is a heritage relationship between the two classes. *)
		if (type_to = tne || is_parent classesEnv (Some type_to) (Some tne) 
			|| is_parent classesEnv (Some tne) (Some type_to)) then 
			TypedCast(c, Located.mk_elem ne (Located.loc_of e), type_to)
		else 
			raise (PError(IllegalCast(tne, type_to), Located.loc_of e))

	and type_this () = 
		if (Option.is_none classname_str) || static_m then
			raise (PError(UndefinedObject("this"), (Located.loc_of expr)))
		else 
			TypedThis (Option.get classname_str)

	in match Located.elem_of expr with
  	| Null -> TypedNull
  	| This -> type_this ()
	| Int i -> TypedInt (i, "Int")
	| Boolean b -> TypedBoolean (b, "Boolean")
	| String s -> TypedString (s, "String")
	| Unop (u, e) -> type_unop u e
	| Condition (i, t, e) -> type_condition i t e
	| Instance cn -> TypedInstance(cn, (get_classdef classesEnv 
		(string_of_classname (Located.elem_of cn)) (Located.loc_of cn)).name)
	| MethodCall (e, m, args) -> type_method_call e m args
	| Instanceof (e, c) -> TypedInstanceof(Located.mk_elem (type_expr classname_str static_m classesEnv varEnv e) 
								(Located.loc_of e), c, "Boolean")
	| Local (c, v, ve, e) -> type_local_variable c v ve e
	| Var s -> TypedVar(s, get_var_type varEnv (Located.elem_of s) (Located.loc_of s) false)
	| AttrAffect (s, e) -> type_attr_affect s e
	| StaticMethodCall (c, m, args) -> type_static_method_call c m args
	| Binop (b, e1, e2) -> type_binop b e1 e2
	| Cast (c, e) -> type_cast c e


let rec type_params_list classesEnv params = match params with
	| [] -> []
	| t::q -> (match (Located.elem_of t) with 
			| Param(c, s) -> Located.mk_elem (TypedParam(c, s, type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c))) 
					(Located.loc_of t)::(type_params_list classesEnv q)
		)

let rec type_attr_or_method_list classesEnv currentClassEnv l =

	let type_method c s params e static = 
		(* parse_attributes is made for static methods to receive 
			only the static attributes in its variables env *)
		let rec parse_attributes attrs = if (static = false) then attrs else 
			begin match attrs with
				| [] -> []
				| t::q -> t.t; if (t.static) then t::(parse_attributes q) else parse_attributes q
			end
		in let nparams = type_params_list classesEnv params
		and return_type = type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c)
		in let params_vartypes = params_to_vartype classesEnv nparams
		in let ne = type_expr (Some currentClassEnv.name) static classesEnv ((parse_attributes currentClassEnv.attributes)@params_vartypes) e
		in
		check_type_is_legal classesEnv (Some return_type) (Some (type_of_expr ne)) (Located.loc_of e);
		if (static) then TypedStaticMethod(c, s, nparams, Located.mk_elem ne (Located.loc_of e), return_type)
			else TypedMethod(c, s, nparams, Located.mk_elem ne (Located.loc_of e), return_type)

	and type_attr_with_value c s e static =
		(* Don't use other attributes in the expression of an attribute *)
		let ne = type_expr (Some currentClassEnv.name) static classesEnv [] e
		in let tne = (type_of_expr ne)
		in 
		check_type_is_legal classesEnv (Some (type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c))) 
			(Some tne) (Located.loc_of e);
		if (static) then TypedStaticAttrWithValue(c, s, Located.mk_elem ne (Located.loc_of e), tne) 
			else TypedAttrWithValue(c, s, Located.mk_elem ne (Located.loc_of e), tne)

	in let typed_attr_or_method = function
		| Attr (c, s) -> TypedAttr(c, s, type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c))
		| StaticAttr (c, s) -> TypedStaticAttr(c, s, type_of_classname classesEnv (Located.elem_of c) (Located.loc_of c) )
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
	let classesEnv = ClassesEnv.build_classes_env tree 
	in let rec type_rec_structure_tree sub_tree =
		(* This inner function receives a non-located class_or_expr *)
		let type_structure = function
			| Expr e -> TypedExpr (Located.mk_elem (type_expr None false classesEnv [] e) (Located.loc_of e))
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
