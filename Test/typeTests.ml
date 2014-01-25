open OUnit2

open TestUtils
open Located
open Location
open Structure
open TypedStructure
open Errors
open Typer

exception TestError of Errors.error

(*************************************************************************************)
(***************************** Utils for building tests ******************************)

let build_success_test_w_params expType classEnv varEnv class_str static_m expr =
	print_endline ((Structure.string_of_expr expr) ^ " => " ^ (TypedStructure.string_of_expr_type expType));
	print_endline "========================================";
	assert_equal expType (TypedStructure.type_of_expr (Typer.type_expr class_str static_m 
		(ClassesEnv.static_classes_env@classEnv) varEnv 
		(mk_none expr)))

let build_success_test expType classEnv varEnv expr =
	build_success_test_w_params expType classEnv varEnv None false expr

let build_failure_test_w_params classEnv varEnv class_str static_m expr err =
	let test _ = 
		try 
			print_endline ((Structure.string_of_expr expr) ^ " => " 
				^ (Errors.string_of_error err));
			print_endline "========================================";
			Typer.type_expr class_str static_m (ClassesEnv.static_classes_env@classEnv) varEnv (mk_none expr)
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises (TestError err) test

let build_failure_test classEnv varEnv expr err =
	build_failure_test_w_params classEnv varEnv None false expr err

(* This test-builder evaluates the expression of the method called testM 
in the last class of the structure tree *)
let build_method_expr_success_test expType tree =
	print_endline ((Structure.string_of_structure_tree tree) ^ " => " ^ (TypedStructure.string_of_expr_type expType));
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
		"Int"
		[] []
		(* 10 *)
		(Int(mk_none 10));
	build_success_test
		"Boolean"
		[] []
		(* false *)
		(Boolean(mk_none false));
	build_success_test
		"String"
		[] []
		(* "foobar" *)
		(String(mk_none "foobar"))

let test_unop _ = 
	build_success_test 
		"Boolean" 
		[] []
		(* !true *)
		(Unop(mk_none Udiff, mk_none (Boolean (mk_none true))));
	build_success_test 
		"Int" 
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
		"Int"
		[] []
		(* if (true) {1} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 1)), mk_none (Int (mk_none 2))));
	build_success_test
		"String"
		[] []
		(* if (true) {"foo"} else {"bar"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), 
			mk_none (String (mk_none "bar"))));
	build_success_test
		"Object"
		[] []
		(* if (true) {"foo"} else {2} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (String (mk_none "foo")), mk_none (Int (mk_none 2))));
	build_success_test
		"Object"
		[] []
		(* if (true) {2} else {"foo"} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 2)), mk_none (String (mk_none "foo"))));
	build_success_test
		"A" (* Least common ancestor *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[];};
		 {name="B"; parent=Some "A"; attributes=[]; methods=[];};
		 {name="C"; parent=Some "A"; attributes=[]; methods=[];};] 
		[]
		(* if (true) {new B} else {new C} *)
		(Condition(mk_none (Boolean (mk_none true)), 
			mk_none (Instance (mk_none (Classname (mk_none "B")))), 
			mk_none (Instance (mk_none (Classname (mk_none "C"))))));
	build_success_test
		"A" (* Least common ancestor *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[];};
		 {name="B"; parent=Some "A"; attributes=[]; methods=[];};
		 {name="C"; parent=Some "A"; attributes=[]; methods=[];};
		 {name="D"; parent=Some "C"; attributes=[]; methods=[];};] 
		[]
		(* if (true) {new B} else {new D} *)
		(Condition(mk_none (Boolean (mk_none true)), 
			mk_none (Instance (mk_none (Classname (mk_none "B")))), 
			mk_none (Instance (mk_none (Classname (mk_none "D"))))));
	build_failure_test
		[] []
		(* if (null) {2} else {1} *)
		(Condition(mk_none Null, mk_none (Int (mk_none 2)), mk_none (Int (mk_none 1))))
		(Errors.NullError);
	build_success_test
		"Int"
		[] []
		(* if (true) {1} else {null} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none (Int (mk_none 1)), mk_none Null));
	build_success_test
		"Int"
		[] []
		(* if (true) {null} else {1} *)
		(Condition(mk_none (Boolean (mk_none true)), mk_none Null, mk_none (Int (mk_none 1))))

let test_instance _  =
	build_success_test
		(("A"))
		[{name="B"; parent=Some "Object"; attributes=[]; methods=[]};
		 {name="A"; parent=Some "Object"; attributes=[]; methods=[]}]
		[]
		(* new A *)
		(Instance(mk_none (Classname (mk_none "A"))));
	build_failure_test
		[][] 
		(* new A // undefined *)
		(Instance(mk_none (Classname (mk_none "A"))))
		(Errors.UndefinedType("A"));
	build_success_test
		("A")  (* Is this logical ?? *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]};
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		[{t="A"; n="a"; attr=true; loc=Location.none; static=false;}]
		(AttrAffect(mk_none "a", mk_none (Instance (mk_none (Classname (mk_none "B"))))))

let test_method_call _ = 
	build_success_test
		("Int")
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}]
		[]
		(* (new A).m() *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", []));
	build_success_test
		("A")
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="A";
			static=false;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}]
		[]
		(* ((new A).m()).m() *)
		(MethodCall(mk_none (MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [])), 
			mk_none "m", []));
	build_failure_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}]
		[]
		(* (new A).m2() *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m2", []))
		(Errors.UndefinedMethod("A", "m2", []));
	build_failure_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}]
		[]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [mk_none (Int (mk_none 1))]))
		(Errors.UndefinedMethod("A", "m", ["Int"]));
	build_success_test
		("Int")
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			loc=Location.none; 
			params=["Int"]
		};]}]
		[]
		(* (new A).m(1) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", [mk_none (Int (mk_none 1))]));
	build_failure_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			loc=Location.none; 
			params=["Int"]
		};]}]
		[]
		(* (new A).m(1, true) *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", 
			[mk_none (Int (mk_none 1)); mk_none (Boolean (mk_none true))]))
		(Errors.UndefinedMethod("A", "m", ["Int"; "Boolean"]));
	build_failure_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=true;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}]
		[]
		(* (new A).m() *)
		(* Method calls CANNOT be done on static methods *)
		(MethodCall(mk_none (Instance(mk_none (Classname (mk_none "A")))), mk_none "m", []))
		(Errors.UndefinedMethod("A", "m", []));
	build_failure_test
		[] []
		(* null.m() *)
		(* Method calls CANNOT be done on static methods *)
		(MethodCall(mk_none Null, mk_none "m", []))
		(Errors.NullError)

let test_instanceof _ = 
	build_success_test
		"Boolean"
		[] []
		(* 1 instanceof Int *)
		(Instanceof(mk_none (Int (mk_none 1)), mk_none (Classname (mk_none "Int"))));
	build_failure_test
		[] []
		(* 1 instanceof Int *)
		(Instanceof(mk_none Null, mk_none (Classname (mk_none "Int"))))
		(Errors.NullError)

let test_local_var _ = 
	build_success_test
		"Boolean"
		[] []
		(* Int i = 1 in true *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (Int (mk_none 1)), 
			mk_none (Boolean (mk_none true))));
	build_success_test
		("A")
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}] 
		[]
		(* Int i = 1 in new A *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (Int (mk_none 1)), 
			mk_none (Instance(mk_none (Classname (mk_none "A"))))));
	build_success_test
		"Int"
		[] []
		(* Int i = 1 in i *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (Int (mk_none 1)), 
			mk_none (Var (mk_none "i"))));
	build_failure_test
		[] []
		(* Int i = "foo" in true *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none (String (mk_none "foo")), 
			mk_none (Boolean (mk_none true))))
		(Errors.TypeError("Int", "String"));
	build_success_test
		"Int"
		[] []
		(* Int i = null in i *)
		(Local(mk_none (Classname (mk_none "Int")), mk_none "i", mk_none Null, 
			mk_none (Var (mk_none "i"))))

let test_var _ = 
	build_success_test
		"Int"
		[] [{t="Int"; n="i"; attr=false; loc=Location.none; static=false;}]
		(* i *)
		(Var(mk_none "i"));
	build_success_test
		"Int"
		[] 
		[{t="String"; n="a"; attr=false; loc=Location.none; static=false;};
		 {t="Int"; n="i"; attr=false; loc=Location.none; static=false;}]
		(* i *)
		(Var(mk_none "i"));
	build_failure_test
		[] [{t="Int"; n="i"; attr=false; loc=Location.none; static=false;}]
		(* a *)
		(Var(mk_none "a"))
		(Errors.UndefinedObject("a"));
	build_failure_test
		[] [{t="Int"; n="ii"; attr=false; loc=Location.none; static=false;}]
		(* a *)
		(Var(mk_none "i"))
		(Errors.UndefinedObject("i"));
	build_failure_test
		[] [{t="Int"; n="i"; attr=false; loc=Location.none; static=false;}]
		(* a *)
		(Var(mk_none "ii"))
		(Errors.UndefinedObject("ii"))

let test_attr_affect _ = 
	build_success_test
		"Int"
		[] [{t="Int"; n="i"; attr=true; loc=Location.none; static=false}]
		(* i = 3 *)
		(AttrAffect(mk_none "i", mk_none (Int (mk_none 3))));
	build_failure_test
		[] [{t="Int"; n="i"; attr=true; loc=Location.none; static=false}]
		(* i = "foo" *)
		(AttrAffect(mk_none "i", mk_none (String (mk_none "foo"))))
		(Errors.TypeError("Int", "String"));
	build_failure_test
		[] [{t="Int"; n="a"; attr=true; loc=Location.none; static=false}]
		(* i = "foo" *)
		(AttrAffect(mk_none "i", mk_none (String (mk_none "foo"))))
		(Errors.UndefinedObject("i"));
	build_failure_test
		[] [{t="Int"; n="i"; attr=false; loc=Location.none; static=false}]
		(* i = "foo" *)
		(AttrAffect(mk_none "i", mk_none (Int (mk_none 1))))
		(Errors.UndefinedObject("i")); (* Undefined because i is not an attribute *)
	build_success_test
		"Int"
		[] [{t="Int"; n="i"; attr=true; loc=Location.none; static=false}]
		(* i = null *)
		(AttrAffect(mk_none "i", mk_none (Null)));
	build_success_test
		"Int"
		[] [{t="Int"; n="i"; attr=true; loc=Location.none; static=true}]
		(* i = null *)
		(AttrAffect(mk_none "i", mk_none (Null)))

let test_static_method_call _ =
	build_success_test
		"Int"
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=true;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}] []
		(* A.m() *)
		(StaticMethodCall(mk_none (Classname (mk_none "A")), mk_none "m", []));
	build_success_test
		"Int"
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=true;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}; {name="B"; parent=Some "A"; attributes=[]; methods=[{
			name="m";
			return="String";
			static=true;
			cl="B";
			loc=Location.none; 
			params=[]
		};]};] 
		[]
		(StaticMethodCall(mk_none (Classname (mk_none "A")), mk_none "m", []));
	build_success_test
		"String"
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=true;
			cl="A";
			loc=Location.none; 
			params=[]
		};]}; {name="B"; parent=Some "A"; attributes=[]; methods=[{
			name="m";
			return="String";
			static=true;
			cl="B";
			loc=Location.none; 
			params=[]
		};]};] 
		[]
		(StaticMethodCall(mk_none (Classname (mk_none "B")), mk_none "m", []))

let test_binop _ =
	build_success_test
		"Int" [] []
		(Binop(mk_none Bsemicol, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Int" [] []
		(Binop(mk_none Badd, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Int" [] []
		(Binop(mk_none Bsub, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Int" [] []
		(Binop(mk_none Bmul, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Int" [] []
		(Binop(mk_none Bdiv, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Int" [] []
		(Binop(mk_none Bmod, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Bsup, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Bsupeq, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Binf, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Binfeq, mk_none (Int (mk_none 1)), mk_none (Int (mk_none 1))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Band, mk_none (Boolean (mk_none true)), mk_none (Boolean (mk_none true))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Bor, mk_none (Boolean (mk_none true)), mk_none (Boolean (mk_none true))));
	build_success_test
		"Boolean" [] []
		(Binop(mk_none Bdiff, mk_none (String (mk_none "foo")), mk_none (String (mk_none "bar"))));
	build_success_test
		"Boolean" [] []
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
		(Errors.TypeError("String", "Boolean"));

	build_success_test
		"Boolean"
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		[{n="b"; t="B"; attr=false; loc=Location.none; static=false;};
		 {n="a"; t="A"; attr=false; loc=Location.none; static=false;};]
		(* a == b *)
		(Binop(mk_none Beq, mk_none (Var (mk_none "a")), mk_none (Var (mk_none "b"))));
	build_success_test
		"Boolean"
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		[{n="b"; t="B"; attr=false; loc=Location.none; static=false;};
		 {n="a"; t="A"; attr=false; loc=Location.none; static=false;};]
		(* b == a *)
		(Binop(mk_none Beq, mk_none (Var (mk_none "b")), mk_none (Var (mk_none "a"))))

let test_method_expr _ =
		(*** Non static methods ***)
		build_method_expr_success_test
			"Int"
			(* class A { Int testM() {1} } *)
			[mk_class "A" [mk_method_e "Int" "testM" [] (Int(mk_none 1))]];
		build_method_expr_success_test
			"Int"
			(* class A { Int i; Int testM() {i} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_success_test
			"Int"
			(* class A { static Int i; Int testM() {i} } *)
			[mk_class "A" [mk_sattr "Int" "i"; mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_success_test
			"Int"
			(* class A { Int i=1; Int testM() {i} } *)
			[mk_class "A" [mk_attr_v "Int" "i" (Int(mk_none 1)); 
				mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_success_test
			"Int"
			(* class A { static Int i=1; Int testM() {i} } *)
			[mk_class "A" [mk_sattr_v "Int" "i" (Int(mk_none 1)); 
				mk_method_e "Int" "testM" [] (Var(mk_none "i"))]];
		build_method_expr_failure_test
			(* class A { Int testM() {i} } *)
			[mk_class "A" [mk_method_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));
		build_method_expr_success_test
			"null" (* The return type would be Int, but here we test the type of the core of the method *)
			(* class A { Int testM() {null} } *)
			[mk_class "A" [mk_method_e "Int" "testM" [] Null]];

		(*** Static methods ***)
		build_method_expr_success_test
			"Int"
			(* class A { static Int testM() {1} } *)
			[mk_class "A" [mk_smethod_e "Int" "testM" [] (Int(mk_none 1))]];
		build_method_expr_failure_test
			(* class A { Int i; static Int testM() {i} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));
		build_method_expr_success_test
			"Int"
			(* class A { static Int i; static Int testM() {i} } *)
			[mk_class "A" [mk_sattr "Int" "i"; mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]];
	 	build_method_expr_failure_test
			(* class A { Int i=1; static Int testM() {i} } *)
			[mk_class "A" [mk_attr_v "Int" "i" (Int(mk_none 1)); 
				mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]]
			(Errors.UndefinedObject("i"));
		build_method_expr_success_test
			"Int"
			(* class A { static Int i=1; static Int testM() {i} } *)
			[mk_class "A" [mk_sattr_v "Int" "i" (Int(mk_none 1)); 
				mk_smethod_e "Int" "testM" [] (Var(mk_none "i"))]];

		(*** Inherited attributes ***)
		build_method_expr_success_test
			"Int"
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
			("A")
			(* class A { } class B { A testM() {new A} } *)
			[mk_class "A" [];
			 mk_class "B" [mk_method_e "A" "testM" [] (Instance(mk_none (Classname(mk_none "A"))))]];

		(*** Test arguments of methods ***)
		build_method_expr_success_test
			"Int"
			(* class A { Int i; Int testM(Int a) {i+a} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_method_e "Int" "testM" [mk_param_n "Int" "a"] 
				(Binop(mk_none Badd, mk_none (Var(mk_none "i")), mk_none (Var(mk_none "a"))))]];
		build_method_expr_failure_test
			(* class A { Int i; Int testM(Boolean a) {i+a} } *)
			[mk_class "A" [mk_attr "Int" "i"; mk_method_e "Int" "testM" [mk_param_n "Boolean" "a"] 
				(Binop(mk_none Badd, mk_none (Var(mk_none "i")), mk_none (Var(mk_none "a"))))]]
			(Errors.TypeError("Int", "Boolean"))

let test_cast _ = 
	build_success_test
		("A")
		(* class A {} class B extends A {} *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		[{n="b"; t="B"; attr=false; loc=Location.none; static=false;}]
		(* (A)b *)
		(Cast(mk_none (Classname (mk_none "A")), mk_none (Var (mk_none "b"))));
	build_success_test
		("B")
		(* class A {} class B extends A {} *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		[{n="a"; t="A"; attr=false; loc=Location.none; static=false;}]
		(* (B)a *)
		(Cast(mk_none (Classname (mk_none "B")), mk_none (Var (mk_none "a"))));
	build_failure_test
		(* class A {} class B {} *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "Object"; attributes=[]; methods=[]}]
		[{n="b"; t="B"; attr=false; loc=Location.none; static=false;}]
		(* (A)b ; definitly not legal! *) 
		(Cast(mk_none (Classname (mk_none "A")), mk_none (Var (mk_none "b"))))
		(Errors.IllegalCast("B", "A"));
	build_success_test
		("A")
		(* class A {} class B extends A {} class C extends B *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]};
		 {name="C"; parent=Some "B"; attributes=[]; methods=[]}]
		[{n="c"; t="C"; attr=false; loc=Location.none; static=false;}]
		(* (A)c <= up casting, always legal *)
		(Cast(mk_none (Classname (mk_none "A")), mk_none (Var (mk_none "c"))));
	build_success_test
		("C")
		(* class A {} class B extends A {} class C extends B *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]};
		 {name="C"; parent=Some "B"; attributes=[]; methods=[]}]
		[{n="a"; t="A"; attr=false; loc=Location.none; static=false;}]
		(* (C)a <= down casting, not always legal *)
		(Cast(mk_none (Classname (mk_none "C")), mk_none (Var (mk_none "a"))));
	build_success_test
		("C")
		(* class A {} class B extends A {} class C extends A *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]};
		 {name="C"; parent=Some "A"; attributes=[]; methods=[]}]
		[{n="b"; t="B"; attr=false; loc=Location.none; static=false;}]
		(* (C)((A)b) <= down casting, not legal but not detectable at this point *)
		(Cast(mk_none (Classname (mk_none "C")), mk_none (
			Cast(mk_none (Classname (mk_none "A")), mk_none (Var (mk_none "b"))))));
	build_success_test
		("Int")
		(* class A extends Int {} *)
		[{name="A"; parent=Some "Int"; attributes=[]; methods=[]}]
		[{n="a"; t="A"; attr=false; loc=Location.none; static=false;}]
		(* (Int)a *)
		(Cast(mk_none (Classname (mk_none "Int")), mk_none (Var (mk_none "a"))));
	build_success_test
		("A")
		(* class A extends Int {} *)
		[{name="A"; parent=Some "Int"; attributes=[]; methods=[]}]
		[{n="i"; t="Int"; attr=false; loc=Location.none; static=false;}]
		(* (A)i *)
		(Cast(mk_none (Classname (mk_none "A")), mk_none (Var (mk_none "i"))));
	build_success_test
		("Int")
		[] []
		(* (Int)2 *)
		(Cast(mk_none (Classname (mk_none "Int")), mk_none (Int (mk_none 2))));
	build_failure_test
		[] []
		(* (Int)null *)
		(Cast(mk_none (Classname (mk_none "Int")), mk_none (Null)))
		(Errors.NullError)

let test_is_parent_function _ =
	assert_equal true (is_parent [] (Some "Object") (Some "Int"));
	assert_equal false (is_parent [] (Some "Int") (Some "Object"));
	(* class A extends Int {} *)
	assert_equal true (is_parent [{name="A"; parent=Some "Int"; attributes=[]; methods=[]}] 
		(Some "Int") (Some  "A"));
	(* class A extends Int {} *)
	assert_equal true (is_parent [{name="A"; parent=Some "Int"; attributes=[]; methods=[]}] 
		(Some "Object") (Some "A"));
	(* class A extends Int {} *)
	assert_equal false (is_parent [{name="Int";parent=Some "Object";attributes=[];methods=[]};
		{name="String";parent=Some "Object";attributes=[];methods=[]};
		{name="A"; parent=Some "Int"; attributes=[]; methods=[]}] 
		(Some "String") (Some "A"));
	(* class A {} class B extends A {} *)
	assert_equal true (is_parent [{name="A"; parent=Some "Object"; attributes=[]; methods=[]};
		{name="B"; parent=Some "A"; attributes=[]; methods=[]}] 
		(Some "A") (Some "B"));
	(* class A {} class B extends A {} *)
	assert_equal false (is_parent [{name="A"; parent=Some "Object"; attributes=[]; methods=[]};
		{name="B"; parent=Some "A"; attributes=[]; methods=[]}] 
		(Some "B") (Some "A"));
	(* class A {} class B extends A {} class C extends B {} *)
	assert_equal true (is_parent [{name="A"; parent=Some "Object"; attributes=[]; methods=[]};
		{name="B"; parent=Some "A"; attributes=[]; methods=[]};
		{name="C"; parent=Some "B"; attributes=[]; methods=[]}] 
		(Some "A") (Some "C"));
	(* class A extends Int {} class B {} *)
	assert_equal false (is_parent [{name="A"; parent=Some "Int"; attributes=[]; methods=[]};
		{name="B"; parent=Some "Object"; attributes=[]; methods=[]}] 
		(Some "Int") (Some "B"));
	assert_equal false (is_parent [{name="Int";parent=Some "Object";attributes=[];methods=[]};
		{name="A"; parent=Some "Int"; attributes=[]; methods=[]};
		{name="B"; parent=Some "A"; attributes=[]; methods=[]}] (Some "B") (Some "A"))

let test_this _ = 
	build_failure_test
		[] []
		(This)
		(* Since, by default, we are not in a class. *)
		(Errors.UndefinedObject("this"));
	build_success_test_w_params
		("A")
		[] []
		(Some "A") false
		(* This can be used inside a non-static method. *)
		(This);
	build_success_test_w_params
		("Int")
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			loc=Location.none; 
			params=[]
		}];}] 
		[]
		(Some "A") false
		(* this.m() in a non static method. *)
		(MethodCall(mk_none This, mk_none "m", []));
	build_failure_test_w_params
		[] []
		(Some "A") true
		(* This cannot be used in a static method. *)
		(This)
		(Errors.UndefinedObject("this"))

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
		 "cast">:: test_cast;

		 "methodExpr">:: test_method_expr;

		 "isParent">:: test_is_parent_function;

		 "this">:: test_this;
		]

let () =
  run_test_tt_main suite