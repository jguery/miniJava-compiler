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

let build_failure_test env expr err =
	let test _ = 
		try 
			print_endline ((Structure.string_of_expr expr) ^ " => " 
				^ (Errors.string_of_error err));
			print_endline "========================================";
			Typer.type_expr env expr
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises (TestError err) test

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
	build_failure_test
		[]
		(* -true *)
		(Unop(mk_none Uminus, mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[]
		(* !10 *)
		(Unop(mk_none Udiff, mk_none (Int (mk_none 10))))
		(Errors.TypeError("Boolean", "Int"))

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
	build_failure_test
		[]
		(* if (true) {"foo"} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), mk_none (Int (mk_none 2))))
		(Errors.TypeError("String", "Int"));
	build_failure_test
		[]
		(* if (true) {2} else {"foo"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 2)), mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"))

let test_instance _  =
	build_success_test
		(Typer.CustomType("A"))
		[{name="B"; parent=ObjectType; methods=[]};
		 {name="A"; parent=ObjectType; methods=[]}]
		(* new A *)
		(Instance(mk_none (Classname (mk_none "A"))));
	build_failure_test
		[]
		(* new A // undefined *)
		(Instance(mk_none (Classname (mk_none "A"))))
		(Errors.UndefinedType("A"))

let test_method_call _ = 
	build_success_test
		(Typer.IntType)
		[{name="A"; parent=ObjectType; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		(* (new A).m() *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", []));
	build_success_test
		(Typer.CustomType "A")
		[{name="A"; parent=ObjectType; methods=[{
			name="m";
			return=CustomType "A";
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		(* ((new A).m()).m() *)
		(MethodCall(mk_none (MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [])), 
			mk_none "m", []));
	build_failure_test
		[{name="A"; parent=ObjectType; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		(* (new A).m2() *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m2", []))
		(Errors.UndefinedMethod("A", "m2", []));
	build_failure_test
		[{name="A"; parent=ObjectType; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [mk_none (Int (mk_none 1))]))
		(Errors.UndefinedMethod("A", "m", ["Int"]));
	build_success_test
		(IntType)
		[{name="A"; parent=ObjectType; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[IntType]
		};]}]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [mk_none (Int (mk_none 1))]));
	build_failure_test
		[{name="A"; parent=ObjectType; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[IntType]
		};]}]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", 
			[mk_none (Int (mk_none 1)); mk_none (Boolean (mk_none true))]))
		(Errors.UndefinedMethod("A", "m", ["Int"; "Boolean"]))

(*************************************************************************************)
(*********************************** Test suite **************************************)

let suite =
	"suite">:::
		["basicTypes">:: test_basic_types;
		 "unop">:: test_unop;
		 "condition">:: test_conditions;
		 "instance">:: test_instance;

		 "methodCall">:: test_method_call;
		]

let () =
  run_test_tt_main suite