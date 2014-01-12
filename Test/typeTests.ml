open OUnit2

open TestUtils
open Located
open Location
open Structure
open Errors
open Typer

exception TestError of Errors.error

(*************************************************************************************)
(***************************** Utils for building tests ******************************)

let build_success_test expType classEnv varEnv expr =
	print_endline ((Structure.string_of_expr expr) ^ " => " ^ (Typer.string_of_expr_type expType));
	print_endline "========================================";
	assert_equal expType (Typer.type_of_expr (Typer.type_expr classEnv varEnv expr))

let build_failure_test classEnv varEnv expr err =
	let test _ = 
		try 
			print_endline ((Structure.string_of_expr expr) ^ " => " 
				^ (Errors.string_of_error err));
			print_endline "========================================";
			Typer.type_expr classEnv varEnv expr
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises (TestError err) test

(* This test-builder evaluates the expression of the method called testM 
in the last class of the structure tree *)
let build_method_expr_success_test expType tree =
	print_endline ((Structure.string_of_structure_tree tree) ^ " => " ^ (Typer.string_of_expr_type expType));
	print_endline "========================================";
	let rec find_m l = match l with 
		| [] -> raise (TestError (UndefinedMethod("TestType", "testM", [])))
		| t::q -> (match Located.elem_of t with 
				| TypedMethod (_, m, _, e, _) when (Located.elem_of m) = "testM" -> 
					type_of_expr (Located.elem_of e)
				| TypedStaticMethod (_, m, _, e, _) when (Located.elem_of m) = "testM" -> 
					type_of_expr (Located.elem_of e)
				| _ -> find_m q
			)
	in let typed_tree = type_structure_tree tree
	in let last_class = Located.elem_of (List.hd (List.rev typed_tree))
	in let method_expr_type =  match last_class with 
		| TypedClassdef (_, l) -> find_m l
		| TypedClassdefWithParent (_, _, l) -> find_m l
		| _ -> raise (TestError (UndefinedType("Any class")))
	in assert_equal expType method_expr_type

let build_method_expr_failure_test tree err =
	let test _ = 
		try 
			print_endline ((Structure.string_of_structure_tree tree) ^ " => "
				^ (Errors.string_of_error err));
			print_endline "========================================";
			type_structure_tree tree
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
		[] []
		(* 10 *)
		(Int(mk_none 10));
	build_success_test
		Typer.BooleanType
		[] []
		(* false *)
		(Boolean(mk_none false));
	build_success_test
		Typer.StringType
		[] []
		(* "foobar" *)
		(String(mk_none "foobar"))

let test_unop _ = 
	build_success_test 
		Typer.BooleanType 
		[] []
		(* !true *)
		(Unop(mk_none Udiff, mk_none (Boolean (mk_none true))));
	build_success_test 
		Typer.IntType 
		[] []
		(* -10 *)
		(Unop(mk_none Uminus, mk_none (Int (mk_none 10))));
	build_failure_test
		[] []
		(* -true *)
		(Unop(mk_none Uminus, mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(* !10 *)
		(Unop(mk_none Udiff, mk_none (Int (mk_none 10))))
		(Errors.TypeError("Boolean", "Int"))

let test_conditions _ = 
	build_success_test
		Typer.IntType
		[] []
		(* if (true) {1} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 1)), mk_none (Int (mk_none 2))));
	build_success_test
		Typer.StringType
		[] []
		(* if (true) {"foo"} else {"bar"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), 
			mk_none (String (mk_none "bar"))));
	build_failure_test
		[] []
		(* if (true) {"foo"} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), mk_none (Int (mk_none 2))))
		(Errors.TypeError("String", "Int"));
	build_failure_test
		[] []
		(* if (true) {2} else {"foo"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 2)), mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"))

let test_instance _  =
	build_success_test
		(Typer.CustomType("A"))
		[{name="B"; parent=ObjectType; attributes=[]; methods=[]};
		 {name="A"; parent=ObjectType; attributes=[]; methods=[]}]
		[]
		(* new A *)
		(Instance(mk_none (Classname (mk_none "A"))));
	build_failure_test
		[][] 
		(* new A // undefined *)
		(Instance(mk_none (Classname (mk_none "A"))))
		(Errors.UndefinedType("A"))

let test_method_call _ = 
	build_success_test
		(Typer.IntType)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		[]
		(* (new A).m() *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", []));
	build_success_test
		(Typer.CustomType "A")
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=CustomType "A";
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		[]
		(* ((new A).m()).m() *)
		(MethodCall(mk_none (MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [])), 
			mk_none "m", []));
	build_failure_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		[]
		(* (new A).m2() *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m2", []))
		(Errors.UndefinedMethod("A", "m2", []));
	build_failure_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		[]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [mk_none (Int (mk_none 1))]))
		(Errors.UndefinedMethod("A", "m", ["Int"]));
	build_success_test
		(IntType)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[IntType]
		};]}]
		[]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [mk_none (Int (mk_none 1))]));
	build_failure_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[IntType]
		};]}]
		[]
		(* (new A).m(1, true) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", 
			[mk_none (Int (mk_none 1)); mk_none (Boolean (mk_none true))]))
		(Errors.UndefinedMethod("A", "m", ["Int"; "Boolean"]));
	build_failure_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=true;
			cl=CustomType "A";
			params=[]
		};]}]
		[]
		(* (new A).m() *)
		(* Method calls CANNOT be done on static methods *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", []))
		(Errors.UndefinedMethod("A", "m", []))

let test_instanceof _ = 
	build_success_test
		Typer.BooleanType
		[] []
		(* 1 instanceof Int *)
		(Instanceof(mk_none (Int (mk_none 1)), mk_none (Classname (mk_none "Int"))))

let test_local_var _ = 
	build_success_test
		Typer.BooleanType
		[] []
		(* Int i = 1 in true *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (Int (mk_none 1)), 
			mk_none (Boolean (mk_none true))));
	build_success_test
		(Typer.CustomType "A")
		[{name="A"; parent=ObjectType; attributes=[]; methods=[]}] 
		[]
		(* Int i = 1 in new A *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (Int (mk_none 1)), 
			mk_none (Instance(mk_none (Classname (mk_none "A"))))));
	build_success_test
		Typer.IntType
		[] []
		(* Int i = 1 in i *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (Int (mk_none 1)), 
			mk_none (Var (mk_none "i"))));
	build_failure_test
		[] []
		(* Int i = "foo" in true *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (String (mk_none "foo")), 
			mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "String"))

let test_var _ = 
	build_success_test
		Typer.IntType
		[] [{t=IntType; n="i"; attr=false; static=false;}]
		(* i *)
		(Var(mk_none "i"));
	build_success_test
		Typer.IntType
		[] 
		[{t=StringType; n="a"; attr=false; static=false;};
		 {t=IntType; n="i"; attr=false; static=false;}]
		(* i *)
		(Var(mk_none "i"));
	build_failure_test
		[] [{t=IntType; n="i"; attr=false; static=false;}]
		(* a *)
		(Var(mk_none "a"))
		(Errors.UndefinedObject("a"));
	build_failure_test
		[] [{t=IntType; n="ii"; attr=false; static=false;}]
		(* a *)
		(Var(mk_none "i"))
		(Errors.UndefinedObject("i"));
	build_failure_test
		[] [{t=IntType; n="i"; attr=false; static=false;}]
		(* a *)
		(Var(mk_none "ii"))
		(Errors.UndefinedObject("ii"))

let test_attr_affect _ = 
	build_success_test
		Typer.IntType
		[] [{t=IntType; n="i"; attr=true; static=false}]
		(* i = 3 *)
		(AttrAffect(mk_none "i", mk_none (Int (mk_none 3))));
	build_failure_test
		[] [{t=IntType; n="i"; attr=true; static=false}]
		(* i = "foo" *)
		(AttrAffect(mk_none "i", mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"));
	build_failure_test
		[] [{t=IntType; n="a"; attr=true; static=false}]
		(* i = "foo" *)
		(AttrAffect(mk_none "i", mk_none (String (mk_none "foo"))))
		(Errors.UndefinedObject("i"));
	build_failure_test
		[] [{t=IntType; n="i"; attr=false; static=false}]
		(* i = "foo" *)
		(AttrAffect(mk_none "i", mk_none (Int (mk_none 1))))
		(Errors.UndefinedObject("i")) (* Undefined because i is not an attribute *)

let test_static_method_call _ =
	build_success_test
		Typer.IntType
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=true;
			cl=CustomType "A";
			params=[]
		};]}] []
		(* A.m() *)
		(StaticMethodCall(mk_none (Classname (mk_none "A")), mk_none "m", []));
	build_success_test
		Typer.IntType
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=true;
			cl=CustomType "A";
			params=[]
		};]}; {name="B"; parent=CustomType "A"; attributes=[]; methods=[{
			name="m";
			return=StringType;
			static=true;
			cl=CustomType "B";
			params=[]
		};]};] 
		[]
		(StaticMethodCall(mk_none (Classname (mk_none "A")), mk_none "m", []));
	build_success_test
		Typer.StringType
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=true;
			cl=CustomType "A";
			params=[]
		};]}; {name="B"; parent=CustomType "A"; attributes=[]; methods=[{
			name="m";
			return=StringType;
			static=true;
			cl=CustomType "B";
			params=[]
		};]};] 
		[]
		(StaticMethodCall(mk_none (Classname (mk_none "B")), mk_none "m", []))

let test_binop _ =
	build_success_test
		Typer.IntType [] []
		(Binop(mk_none Bsemicol, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.IntType [] []
		(Binop(mk_none Badd, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.IntType [] []
		(Binop(mk_none Bsub, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.IntType [] []
		(Binop(mk_none Bmul, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.IntType [] []
		(Binop(mk_none Bdiv, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.IntType [] []
		(Binop(mk_none Bmod, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Bsup, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Bsupeq, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Binf, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Binfeq, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Band, mk_none (Boolean (mk_none true)), mk_none (Boolean (mk_none true))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Bor, mk_none (Boolean (mk_none true)), mk_none (Boolean (mk_none true))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Bdiff, mk_none (String (mk_none "foo")), mk_none (String (mk_none "bar"))));
	build_success_test
		Typer.BooleanType [] []
		(Binop(mk_none Beq, mk_none (String (mk_none "foo")), mk_none (String (mk_none "bar"))));

	build_failure_test
		[] []
		(Binop(mk_none Badd, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Bsub, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Bmul, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Bdiv, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Bmod, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Bsup, mk_none (Int (mk_none 1)), mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"));
	build_failure_test
		[] []
		(Binop(mk_none Bsupeq, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Binf, mk_none (Int (mk_none 1)), mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"));
	build_failure_test
		[] []
		(Binop(mk_none Binfeq, mk_none (Int (mk_none 1)), mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"));
	build_failure_test
		[] []
		(Binop(mk_none Band, mk_none (Int (mk_none 1)), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Boolean", "Int"));
	build_failure_test
		[] []
		(Binop(mk_none Bor, mk_none (String (mk_none "foo")), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Boolean", "String"));
	build_failure_test
		[] []
		(Binop(mk_none Bdiff, mk_none (String (mk_none "foo")), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("String", "Boolean"));
	build_failure_test
		[] []
		(Binop(mk_none Beq, mk_none (String (mk_none "foo")), mk_none (Boolean (mk_none true))))
		(Errors.TypeError("String", "Boolean"))

let test_method_expr _ =
		(*** Non static methods ***)
		build_method_expr_success_test
			IntType
			(* class A { Int testM() {1} } *)
			[mk_class "A" [mk_method_e "Int" "testM" [] (Int(mk_none 1))]];
		build_method_expr_success_test
			IntType
			(* class A { Int i; Int testM() {i} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_success_test
			IntType
			(* class A { static Int i; Int testM() {i} } *)
			[mk_class "A" [mk_sattr "Int" "i"; mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_success_test
			IntType
			(* class A { Int i=1; Int testM() {i} } *)
			[mk_class "A" [mk_attr_v "Int" "i" (Int(mk_none 1)); 
				mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_success_test
			IntType
			(* class A { static Int i=1; Int testM() {i} } *)
			[mk_class "A" [mk_sattr_v "Int" "i" (Int(mk_none 1)); 
				mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_failure_test
			(* class A { Int testM() {i} } *)
			[mk_class "A" [mk_method_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));

		(*** Static methods ***)
		build_method_expr_success_test
			IntType
			(* class A { static Int testM() {1} } *)
			[mk_class "A" [mk_smethod_e "Int" "testM" [] (Int(mk_none 1))]];
		build_method_expr_failure_test
			(* class A { Int i; static Int testM() {i} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));
		build_method_expr_success_test
			IntType
			(* class A { static Int i; static Int testM() {i} } *)
			[mk_class "A" [mk_sattr "Int" "i"; mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]];
	 	build_method_expr_failure_test
			(* class A { Int i=1; static Int testM() {i} } *)
			[mk_class "A" [mk_attr_v "Int" "i" (Int(mk_none 1)); 
				mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));
		build_method_expr_success_test
			IntType
			(* class A { static Int i=1; static Int testM() {i} } *)
			[mk_class "A" [mk_sattr_v "Int" "i" (Int(mk_none 1)); 
				mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]];

		(*** Inherited attributes ***)
		build_method_expr_success_test
			IntType
			(* class A { Int i } class B extends A { Int testM() {i} } *)
			[mk_class "A" [mk_attr "Int" "i"];
			 mk_class_p "B" "A" [mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_failure_test
			(* class A { static Int i } class B extends A { Int testM() {i} } *)
			(* Static attributes are not inherited *)
			[mk_class "A" [mk_sattr "Int" "i"];
			 mk_class_p "B" "A" [mk_method_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));
		build_method_expr_success_test
			(CustomType "A")
			(* class A { } class B { A testM() {new A} } *)
			[mk_class "A" [];
			 mk_class "B" [mk_method_e "A" "testM" [] (Instance(mk_none (Classname(mk_none "A"))))]];

		(*** Test arguments of methods ***)
		build_method_expr_success_test
			IntType
			(* class A { Int i; Int testM(Int a) {i+a} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_method_e "Int" "testM" [mk_param_n "Int" "a"] 
				(Binop(mk_none Badd, mk_none (Var(mk_none "i")), mk_none (Var(mk_none "a"))))]];
		build_method_expr_failure_test
			(* class A { Int i; Int testM(Boolean a) {i+a} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_method_e "Int" "testM" [mk_param_n "Boolean" "a"] 
				(Binop(mk_none Badd, mk_none (Var(mk_none "i")), mk_none (Var(mk_none "a"))))]]
			(Errors.TypeError("Int", "Boolean"))
 
(*************************************************************************************)
(*********************************** Test suite **************************************)

let suite =
	"suite">:::
		["basicTypes">:: test_basic_types;
		 "unop">:: test_unop;
		 "condition">:: test_conditions;
		 "instance">:: test_instance;

		 "methodCall">:: test_method_call;

		 "instanceof">:: test_instanceof;

		 "localVar">:: test_local_var;
		 "var">:: test_var;
		 "attrAffect">:: test_attr_affect;

		 "staticMethodCall">:: test_static_method_call;

		 "binop">:: test_binop;

		 "methodExpr">::test_method_expr;
		]

let () =
  run_test_tt_main suite