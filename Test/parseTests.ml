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
	    	print_structure_tree res;
	    	strip_location res


(***************************************************************************)
(* Utils for building tests *)
let build_path filename = 
	"Test/Files/" ^ filename

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
		[Expr_t(Binop_t(Badd, Int_t 2, Binop_t(Bmul, Int_t 3, Int_t 4)));
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
		]
		"operationsPriorities.mjava"


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
		]


let () =
  run_test_tt_main suite