open OUnit2

open Located
open Location
open Structure
open Errors
open Typer

exception TestError of Errors.error

(*************************************************************************************)
(***************************** Utils for building tests ******************************)
let mk_none x = 
	Located.mk_elem x (Location.none)

let build_success_test expType env expr =
	print_endline ((Structure.string_of_expr expr) ^ " => " ^ (Typer.string_of_expr_type expType));
	print_endline "========================================";
	assert_equal expType (Typer.type_of_expr (Typer.type_expr env expr))

let build_failure_type_test env expr expType realType =
	let test _ = 
		try 
			print_endline ((Structure.string_of_expr expr) ^ " => Expected " 
				^ (Typer.string_of_expr_type expType) ^ ", got " 
				^ (Typer.string_of_expr_type realType));
			print_endline "========================================";
			Typer.type_expr env expr
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises 
		(TestError (Errors.TypeError(
			Typer.string_of_expr_type expType, 
			Typer.string_of_expr_type realType
		))) 
		test

let build_failure_defined_test env expr undefType =
	let test _ = 
		try 
			print_endline ((Structure.string_of_expr expr) ^ " => Undefined " 
				^ (Typer.string_of_expr_type undefType));
			print_endline "========================================";
			Typer.type_expr env expr
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises 
		(TestError (Errors.Undefined(Typer.string_of_expr_type undefType))) 
		test

(*************************************************************************************)
(************************************** Tests ****************************************)

let test_basic_types _ = 
	build_success_test
		Typer.IntType
		[]
		(* 10 *)
		(Int(mk_none 10));
	build_success_test
		Typer.BooleanType
		[]
		(* false *)
		(Boolean(mk_none false));
	build_success_test
		Typer.StringType
		[]
		(* "foobar" *)
		(String(mk_none "foobar"))

let test_unop _ = 
	build_success_test 
		Typer.BooleanType 
		[]
		(* !true *)
		(Unop(mk_none Udiff, mk_none (Boolean (mk_none true))));
	build_success_test 
		Typer.IntType 
		[]
		(* -10 *)
		(Unop(mk_none Uminus, mk_none (Int (mk_none 10))));
	build_failure_type_test
		[]
		(* -true *)
		(Unop(mk_none Uminus, mk_none (Boolean (mk_none true))))
		IntType
		BooleanType;
	build_failure_type_test
		[]
		(* !10 *)
		(Unop(mk_none Udiff, mk_none (Int (mk_none 10))))
		BooleanType
		IntType

let test_conditions _ = 
	build_success_test
		Typer.IntType
		[]
		(* if (true) {1} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 1)), mk_none (Int (mk_none 2))));
	build_success_test
		Typer.StringType
		[]
		(* if (true) {"foo"} else {"bar"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), 
			mk_none (String (mk_none "bar"))));
	build_failure_type_test
		[]
		(* if (true) {"foo"} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), mk_none (Int (mk_none 2))))
		StringType
		IntType;
	build_failure_type_test
		[]
		(* if (true) {2} else {"foo"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 2)), mk_none (String (mk_none "foo"))))
		IntType
		StringType

let test_instance _  =
	build_success_test
		(Typer.CustomType("A"))
		[{name="B"; parent=ObjectType; methods=[]};
		 {name="A"; parent=ObjectType; methods=[]}]
		(* new A *)
		(Instance(mk_none (Classname (mk_none "A"))));
	build_failure_defined_test
		[]
		(* new A // undefined *)
		(Instance(mk_none (Classname (mk_none "A"))))
		(CustomType "A")

(*************************************************************************************)
(*********************************** Test suite **************************************)

let suite =
	"suite">:::
		["basicTypes">:: test_basic_types;
		 "unop">:: test_unop;
		 "condition">:: test_conditions;
		 "instance">:: test_instance;
		]

let () =
  run_test_tt_main suite