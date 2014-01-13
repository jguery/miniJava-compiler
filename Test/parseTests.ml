open OUnit2

open Main
open Compile
open Parser
open Structure
open Errors
open Location
open Located
open Expr


(***************************************************************************)
(* The data structure is redefined without the location information, 
	so testing is clearer *)
exception TestError of Errors.error

type classname_t =
  | Classname_t of string

type expr_t = 
  | Null_t
  | This_t
  | Int_t of int
  | Boolean_t of bool
  | String_t of string
  | Var_t of string
  | AttrAffect_t of string * expr_t
  | Unop_t of unop * expr_t
  | Binop_t of binop * expr_t * expr_t
  | Local_t of classname_t * string * expr_t * expr_t
    (* Defines an expression used locally *)
  | Condition_t of expr_t * expr_t * expr_t
  | MethodCall_t of expr_t * string * expr_t list
  | StaticMethodCall_t of classname_t * string * expr_t list
    (* Static method calls are only applied ot classnames *)
  | Instance_t of classname_t
  | Cast_t of classname_t * expr_t
  | Instanceof_t of expr_t * classname_t

type param_t = 
  | Param_t of classname_t * string

type attr_or_method_t = 
  | Attr_t of classname_t * string
  | AttrWithValue_t of classname_t * string * expr_t
  | Method_t of classname_t * string * param_t list * expr_t
  | StaticAttr_t of classname_t * string
  | StaticAttrWithValue_t of classname_t * string * expr_t
  | StaticMethod_t of classname_t * string * param_t list * expr_t

type class_or_expr_t = 
  | Classdef_t of string * attr_or_method_t list 
  | ClassdefWithParent_t of string * classname_t * attr_or_method_t list
  | Expr_t of expr_t


(***************************************************************************)
(* Functions to translate from located data structure 
	to non-located data structure *)
let strip_classname_location = function
	| Classname s -> Classname_t (Located.elem_of s)

let rec strip_expr_location expr = 
	let rec strip_exprs_locations = function
	| [] -> []
	| t::q -> (strip_expr_location (Located.elem_of t))::(strip_exprs_locations q)
	in
	match expr with
  	| Null -> Null_t
  	| This -> This_t
  	| Int i -> Int_t (Located.elem_of i)
  	| Boolean b -> Boolean_t (Located.elem_of b)
  	| String s -> String_t (Located.elem_of s)
  	| Var v -> Var_t (Located.elem_of v)
  	| AttrAffect(s,e) -> AttrAffect_t (Located.elem_of s, strip_expr_location(Located.elem_of e))
  	| Unop(u, e) -> Unop_t (Located.elem_of u, strip_expr_location(Located.elem_of e))
  	| Binop(b, e1, e2) -> Binop_t (Located.elem_of b, strip_expr_location(Located.elem_of e1), 
  			strip_expr_location(Located.elem_of e2))
  	| Local(c,s,e1,e2) -> Local_t (strip_classname_location (Located.elem_of c),
  			Located.elem_of s, strip_expr_location(Located.elem_of e1), strip_expr_location(Located.elem_of e2))
    (* Defines an expression used locally *)
  	| Condition(e1,e2,e3) -> Condition_t (strip_expr_location(Located.elem_of e1), 
  			strip_expr_location(Located.elem_of e2), strip_expr_location(Located.elem_of e3))
  	| MethodCall(e,s,l) -> MethodCall_t(strip_expr_location(Located.elem_of e), 
  			Located.elem_of s, strip_exprs_locations l)
  	| StaticMethodCall(c,s,l) -> StaticMethodCall_t(strip_classname_location (Located.elem_of c),
  			Located.elem_of s, strip_exprs_locations l)
    (* Static method calls are only applied ot classnames *)
  	| Instance(c) -> Instance_t(strip_classname_location (Located.elem_of c))
  	| Cast(c,e) -> Cast_t(strip_classname_location (Located.elem_of c), strip_expr_location (Located.elem_of e))
  	| Instanceof(e,c) -> Instanceof_t(strip_expr_location (Located.elem_of e), 
  			strip_classname_location (Located.elem_of c))
	

let rec strip_params_locations l =
	let rec strip_param_location = function
		| Param(c,s) -> Param_t (strip_classname_location (Located.elem_of c), Located.elem_of s)
	in 
	match l with
	| [] -> []
	| t::q -> (strip_param_location (Located.elem_of t))::(strip_params_locations q)

let rec strip_attr_or_methods_locations l = 
	let rec strip_attr_or_method_location = function
		| Attr(c,s) -> Attr_t (strip_classname_location (Located.elem_of c), Located.elem_of s)
	  	| AttrWithValue(c,s,e) -> AttrWithValue_t(strip_classname_location (Located.elem_of c),
	  			Located.elem_of s, strip_expr_location (Located.elem_of e))
	  	| Method(c,s,l,e) -> Method_t (strip_classname_location (Located.elem_of c),
	  			Located.elem_of s, strip_params_locations l, strip_expr_location (Located.elem_of e))
	  	| StaticAttr(c,s) -> StaticAttr_t(strip_classname_location (Located.elem_of c), Located.elem_of s)
	  	| StaticAttrWithValue(c,s,e) -> StaticAttrWithValue_t(strip_classname_location (Located.elem_of c),
	  			Located.elem_of s, strip_expr_location (Located.elem_of e))
	  	| StaticMethod(c,s,l,e) -> StaticMethod_t (strip_classname_location (Located.elem_of c),
	  			Located.elem_of s, strip_params_locations l, strip_expr_location (Located.elem_of e))
	in
	match l with 
	| [] -> []
	| t::q -> (strip_attr_or_method_location (Located.elem_of t))::(strip_attr_or_methods_locations q)

let rec strip_location l = 
	let rec strip_expr_or_class_location = function
		| Expr e -> Expr_t (strip_expr_location (Located.elem_of e))
		| Classdef (s,l) -> Classdef_t (Located.elem_of s, strip_attr_or_methods_locations l)
  		| ClassdefWithParent(s,c,l) -> ClassdefWithParent_t(Located.elem_of s,
  				strip_classname_location (Located.elem_of c), strip_attr_or_methods_locations l)
	in match l with
	| [] -> []
	| t::q -> (strip_expr_or_class_location (Located.elem_of t))::(strip_location q)		


(***************************************************************************)
(* Transform a file into data structure *)
let parse_file str =
	let (file, filename) = get_file str in
	    let input_file = open_in file in
	    let lexbuf = Lexing.from_channel input_file in
	    Location.init lexbuf file;
	    print_endline ("\n====================");
	    let res = structure_tree nexttoken lexbuf in
	    	close_in (input_file);
	    	print_string (string_of_structure_tree res);
	    	strip_location res


(***************************************************************************)
(* Utils for building tests *)
let build_path filename = 
	"Test/Parsing/" ^ filename

let build_success_test expected_struct filename = 
	assert_equal expected_struct (parse_file (build_path filename))

let build_failure_test filename error =
	let test _ = 
		try 
			parse_file (build_path filename)
		with Errors.PError (e, t) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises (TestError (error)) test


(***************************************************************************)
(* ================ TESTS ================= *)

(* Comments in all kind of situations *)
let test_comments test_ctxt = 
	build_success_test 
		[Expr_t (Boolean_t true); Expr_t (Boolean_t false);
		 Expr_t (Local_t (Classname_t "String", "s", String_t "foo", String_t "bar"))]  
		"comments.mjava"

(* Long comment not closed *)
let test_comments_not_closed test_ctxt = 
	build_failure_test "commentsNotClosed.mjava" SyntaxError

(* Test Strings matching *)
let test_strings test_ctxt = 
	build_success_test 
		[Expr_t(String_t "\n\n"); Expr_t(String_t "\\n foo \n");
		 Expr_t(String_t "\n")]
		"strings.mjava"

(* String not closed *)
let test_string_not_closed test_ctxt = 
	build_failure_test "stringNotClosed.mjava" SyntaxError

(* Simple class with no attribute or method *)
let test_simple_class _ = 
	build_success_test
		[Classdef_t("A", [])]
		"simpleClass.mjava"

(* Simple class, name error (in lowercase) *)
let test_simple_class_name_error test_ctxt = 
	build_failure_test "simpleClassNameError.mjava" SyntaxError 

(* Simple class with no attribute or method but with parent *)
let test_simple_class_with_parent _ = 
	build_success_test
		[ClassdefWithParent_t("A", Classname_t "B", [])]
		"simpleClassWithParent.mjava"

(* Simple class with parent, name error in the parent (in lowercase) *)
let test_simple_class_with_parent_name_error test_ctxt = 
	build_failure_test "simpleClassWithParentNameError.mjava" SyntaxError 

(* Simple class with attributes *)
let test_simple_class_attrs _ = 
	build_success_test
		[ClassdefWithParent_t("A", Classname_t "B", [
			Attr_t(Classname_t "Int", "i");
			Attr_t(Classname_t "Boolean", "b");
			Attr_t(Classname_t "String", "s");])]
		"simpleClassAttrs.mjava"

(* Attribute affectation when defined. Test that some expressions can be affected to an attribute *)
let test_attr_affect _ = 
	build_success_test
		[ClassdefWithParent_t("A", Classname_t "B", [
			AttrWithValue_t(Classname_t "Int", "i", Int_t 10);
			AttrWithValue_t(Classname_t "Boolean", "b", Boolean_t true);
			AttrWithValue_t(Classname_t "String", "s", String_t "foobar");
			AttrWithValue_t(Classname_t "String", "d", Null_t);
			AttrWithValue_t(Classname_t "A", "a", This_t);
			AttrWithValue_t(Classname_t "B", "bi", 
				Local_t (Classname_t "C", "c", Boolean_t false, Int_t 10));
			AttrWithValue_t(Classname_t "Int", "cond",
				Condition_t (Boolean_t true, Int_t 1, Int_t 2));])]
		"attrAffect.mjava"

(* Test operation priorites *)
let test_operations_priorities _ = 
	build_success_test
		[Expr_t(Binop_t(Badd, Unop_t(Uminus, Int_t 2), Binop_t(Bmul, Int_t 3, Int_t 4)));
		 Expr_t(Binop_t(Badd, Binop_t(Bmul, Int_t 2, Int_t 3), Int_t 4));
		 Expr_t(Binop_t(Bmul, Int_t 2, Binop_t(Badd, Int_t 3, Int_t 4)));
		 Expr_t(Binop_t(Bsub, Binop_t(Badd, Int_t 1, Binop_t(Bmul, Int_t 2, Int_t 3)), 
			Binop_t(Bdiv, Int_t 4, Int_t 5)));
		 Expr_t(Binop_t(Bor, Binop_t(Band, Boolean_t true, Boolean_t false), Boolean_t true));
		 Expr_t(Binop_t(Bor, Int_t 1, Binop_t(Band, Int_t 2, Int_t 3)));
		 Expr_t(Binop_t(Band, Binop_t(Beq, Int_t 1, Int_t 2), Boolean_t true));
		 Expr_t(Binop_t(Band, Int_t 1, Binop_t(Beq, Int_t 2, Int_t 3))); 
		 Expr_t(Binop_t(Bsemicol, Int_t 1, Binop_t(Band, Int_t 2, Int_t 3)));
		 Expr_t(Binop_t(Bsemicol, 
		 	Binop_t(Bsub, Binop_t(Badd, Int_t 1, Binop_t(Bmul, Int_t 2, Int_t 3)), 
				Binop_t(Bdiv, Int_t 4, Int_t 5)), 
		 	Binop_t(Bor, Binop_t(Band, Boolean_t true, Boolean_t false), Boolean_t true)));
		 Expr_t(Binop_t(Band, Boolean_t true, Unop_t(Udiff, Boolean_t true)));
		 Expr_t(Binop_t(Bor, Binop_t(Band, Boolean_t true, Unop_t(Udiff, Boolean_t false)), Boolean_t true));
		 Expr_t(Binop_t(Band, Binop_t(Bsupeq, Int_t 2, Unop_t(Uminus, Int_t 3)), 
		 	Binop_t(Bdiff, Int_t 4, Unop_t(Udiff, Int_t 5))));
		 Expr_t(Binop_t(Bsupeq, Binop_t(Bmul, Int_t 2, Int_t 2), Int_t 2));
		]
		"operationsPriorities.mjava"

(* Test the unary operators in complexe expressions *)
let test_expr_unop _ = 
	build_success_test
		[Expr_t(Binop_t(Bsub, Unop_t(Udiff, Int_t 10), Int_t 10));
		 Expr_t(Local_t(Classname_t "String", "s", String_t "foobar", Unop_t(Uminus, Int_t 10)));]
		"exprUnop.mjava"

(* Attribute affectation in expression *)
let test_attr_affect_in_expr _ = 
	build_success_test 
		[Expr_t(Binop_t(Bsemicol, AttrAffect_t("b", String_t "foo"), 
			Local_t(Classname_t "String", "bar", String_t "true", Var_t "bar")));
		 Expr_t(AttrAffect_t("b", Binop_t(Bsemicol, String_t "foo", 
			Local_t(Classname_t "String", "bar", String_t "true", Var_t "bar"))));
		 Expr_t(Local_t(Classname_t "A", "a", 
		 	AttrAffect_t("c", Local_t(Classname_t "B", "b", String_t "foo", Var_t "b")), Var_t "a"))]
		"attrAffectInExpr.mjava"

(* Local affectations tests *)
let test_local_vars _ = 
	build_success_test 
		[Expr_t(Binop_t(Bsemicol, Binop_t(Bsemicol, Binop_t(Bsemicol, 
			Local_t(Classname_t "A", "a", Binop_t(Bsemicol, 
				Binop_t(Bsemicol, Boolean_t true, This_t), String_t "tr"), Int_t 1), 
			Int_t 1), Boolean_t true), Var_t "v"));
		 Expr_t(Local_t(Classname_t "A", "a", Binop_t(Bsemicol, 
			Binop_t(Bsemicol, Boolean_t true, This_t), String_t "tr"), 
		 	Binop_t(Bsemicol, Binop_t(Bsemicol, Binop_t(Bsemicol, Int_t 1, Int_t 1), Boolean_t true), 
		 		Var_t "v")));
		 Expr_t(Local_t(Classname_t "A", "a", Binop_t(Badd, Int_t 1, Int_t 1), Binop_t(Badd, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bsub, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bmul, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bdiv, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bmod, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bsup, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bsupeq, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Binf, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Binfeq, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Beq, Int_t 1, Int_t 1)));
		 Expr_t(Local_t(Classname_t "A", "a", Int_t 1, Binop_t(Bdiff, Int_t 1, Int_t 1)));
		]
		"localVars.mjava"

(* Test method calls and the priority of its operator (the point) *)
let test_method_calls _ = 
	build_success_test
		[Expr_t(MethodCall_t(Var_t "obj", "method", []));
		 Expr_t(Binop_t(Badd, Var_t "a", MethodCall_t(Var_t "b", "method", [])));
		 Expr_t(MethodCall_t(Binop_t(Badd, Var_t "a", Var_t "b"), "m", []));
		 Expr_t(Local_t(Classname_t "A", "a", String_t "foo", MethodCall_t(Var_t "a", "m", [])));
		 Expr_t(MethodCall_t(Local_t(Classname_t "A", "a", String_t "foo", Var_t "a"), "m", []));
		 Expr_t(MethodCall_t(Var_t "a", "m", [Binop_t(Bsemicol, 
		 	Binop_t(Badd, Var_t "a", Var_t "b"), Var_t "c"); Var_t "c";]));
		 Expr_t(Local_t(Classname_t "A", "a", String_t "foo", MethodCall_t(Var_t "a", "m", [])));
		 Expr_t(AttrAffect_t("a", MethodCall_t(Var_t "b", "m", [])))]
		"methodCall.mjava"

(* Test method definitions in classes
	Since the core of the method, the expression, is between brackets, 
	there is not much ambiguity here *)
let test_method_definition _ = 
	build_success_test
		[Classdef_t("A", [
			Method_t(Classname_t "String", "m", [], String_t "foo");
			Method_t(Classname_t "Boolean", "m2", [Param_t(Classname_t "Int", "i");], Boolean_t true);
			Method_t(Classname_t "B", "m3", [Param_t(Classname_t "Int", "i"); Param_t(Classname_t "C", "c")], 
				Binop_t(Bsemicol, Binop_t(Bsemicol, Local_t(Classname_t "D", "d", Var_t "i", 
					Condition_t(Binop_t(Beq, Var_t "c", String_t "foo"), Boolean_t true, Boolean_t false)), 
				AttrAffect_t("a", Var_t "c")), Binop_t(Badd, Var_t "a", Binop_t(Bmul, Int_t 2, Var_t "c"))));
		])]
		"methodDefinition.mjava"

(* Test cast operator, its ambiguities *)
let test_cast _ = 
	build_success_test
		[Expr_t(Binop_t(Badd, Unop_t(Uminus, Cast_t(Classname_t "A", Var_t "a")), Var_t "b"));
		 Expr_t(Binop_t(Badd, Cast_t(Classname_t "A", Var_t "a"), Var_t "b"));
		 Expr_t(AttrAffect_t("a", Binop_t(Bor, Cast_t(Classname_t "Boolean", Int_t 1), Boolean_t true)));
		 Expr_t(Local_t(Classname_t "A", "a", String_t "foo", Binop_t(Badd, 
		 	Cast_t(Classname_t "Int", Int_t 1), Int_t 1)));]
		"cast.mjava"

(* Test instanceof operator, its ambiguities *)
let test_instanceof _ =
	build_success_test
		[Expr_t(Instanceof_t(Var_t "a", Classname_t "Boolean"));
		 Expr_t(Instanceof_t(Cast_t(Classname_t "A", Var_t "a"), Classname_t "B"));
		 Expr_t(Binop_t(Badd, Var_t "a", Instanceof_t(Var_t "b", Classname_t "A")));
		 Expr_t(AttrAffect_t("a", Instanceof_t(Var_t "a", Classname_t "B")));
		 Expr_t(Local_t(Classname_t "Boolean", "b", Int_t 3, Instanceof_t(Var_t "b", Classname_t "Int")));]
		"instanceof.mjava"

(* Not much to test, the new operator is pretty straightforward, no ambiguity *)
let test_new_operator _ = 
	build_success_test
		[Expr_t(Instance_t(Classname_t "A"));
		 Expr_t(Local_t(Classname_t "A", "a", Instance_t(Classname_t "A"), MethodCall_t(Var_t "a", "m", [])));]
		"new.mjava"

let test_static_operator _ = 
	build_success_test
		[Classdef_t("A", [StaticAttr_t(Classname_t "String", "b");
			StaticAttrWithValue_t(Classname_t "Boolean", "foo", Boolean_t true);
			StaticMethod_t(Classname_t "Boolean", "method", [Param_t(Classname_t "A", "a")], 
				Binop_t(Bsemicol, Binop_t(Bsemicol, AttrAffect_t("b", String_t "bar"), 
					MethodCall_t(Var_t "a", "m2", [])), Boolean_t true));
			Method_t(Classname_t "Int", "m2", [], StaticMethodCall_t(Classname_t "A", "method", 
				[Instance_t(Classname_t "A")]));]);]
		"static.mjava"

(***************************************************************************)
(* Test suite *)
let suite =
	"suite">:::
		["comments">:: test_comments;
		 "comments_not_closed">:: test_comments_not_closed;

		 "strings">:: test_strings;		 
		 "string_not_closed">:: test_string_not_closed;

		 "simpleClass">:: test_simple_class;
		 "simpleClassNameError">:: test_simple_class_name_error;
		 "simpleClassWithParent">:: test_simple_class_with_parent;
		 "simpleClassWithParentNameError">:: test_simple_class_with_parent_name_error;
		 "simpleClasseAttrs">:: test_simple_class_attrs;

		 "attrAffect">:: test_attr_affect;

		 "operationsPriorities">:: test_operations_priorities;
		 "exprUnop">:: test_expr_unop;
		 "attrAffectInExpr">:: test_attr_affect_in_expr;
		 "localVars">:: test_local_vars;

		 "methodCall">:: test_method_calls;
		 "methodDefinition">:: test_method_definition;

		 "cast">:: test_cast;
		 "instanceof">:: test_instanceof;

		 "newInstance">:: test_new_operator;

		 "static">:: test_static_operator;
		]


let () =
  run_test_tt_main suite