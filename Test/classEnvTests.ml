open OUnit2

open Located
open Location
open Structure
open TestUtils
open Errors
open Typer
open ClassesEnv

exception TestError of Errors.error

(*************************************************************************************)
(***************************** Utils for building tests ******************************)
let rec drop_first_items i l =
	if i = 0 then l else begin
		match l with 
		| [] -> []
		| t::q -> drop_first_items (i-1) q
	end

let build_success_test expEnv structureTree =
	(* Don't take the static classes environment into account *)
	let env = drop_first_items (List.length ClassesEnv.static_classes_env) (ClassesEnv.build_classes_env structureTree) in
	print_endline ((string_of_structure_tree structureTree) ^ " => " 
		^ (string_of_env env));
	print_endline "========================================";	
	assert_equal expEnv env

let build_failure_test structureTree err =
	let test _ = 
		try 
			print_endline ((string_of_structure_tree structureTree) ^ " => " 
				^ (string_of_error err));
			print_endline "========================================";
			ClassesEnv.build_classes_env structureTree
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises (TestError err) test


(*************************************************************************************)
(************************************** Tests ****************************************)

let test_basic_class _ = 
	(* A class with no method and no parent *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}]
		 (* class A {} *)
		[mk_class "A" []];

	(* A class with no parent and one method with no param *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			params=[]
		};]}]
		(*  class A { Int m() {..} } *)
		[mk_class "A" [mk_method "Int" "m" [];]];

	(* A class with no parent and one method with one param *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Boolean";
			static=false;
			cl="A";
			params=["String";]
		};]}]
		(*  class A { Int m(String s) {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String";];]];

	(* A class with no parent and one method with two params *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Boolean";
			static=false;
			cl="A";
			params=["String"; "Int"]
		};]}]
		(*  class A { Int m(String s, B b) {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String"; mk_param "Int"];]];

	(* A class with no parent and two methods *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Boolean";
			static=false;
			cl="A";
			params=["String"; "Boolean"]
		};{
			name="m2";
			return="String";
			static=false;
			cl="A";
			params=[]
		};]}]
		(*  class A { Boolean m(String s, B b) {..} String m2() {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String"; mk_param "Boolean"]; 
			mk_method "String" "m2" [];]];

	(* A class with one method which returns an undefined type. *)
	build_failure_test
		(* class A {B m() {}} *)
		[mk_class "A" [mk_method "B" "m" []]]
		(Errors.UndefinedType("B"));

	(* A class with one method with one param which has an undefined type. *)
	build_failure_test
		(* class A {B m() {}} *)
		[mk_class "A" [mk_method "Int" "m" [mk_param "B"]]]
		(Errors.UndefinedType("B"))

let test_many_classes _ =
	(* Two classes with no method and no parent *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]}; 
		 {name="B"; parent=Some "Object"; attributes=[]; methods=[]}]
		 (* class A {} class B {} *)
		[mk_class "A" []; mk_class "B" []];

	(* Two classes with methods *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Boolean";
			static=false;
			cl="A";
			params=["String"; "B"]
		};{
			name="m2";
			return="String";
			static=false;
			cl="A";
			params=[]
		};]}; {name="B"; parent=Some "Object"; attributes=[]; methods=[{
			name="m3";
			return="A";
			static=false;
			cl="B";
			params=["Int";]
		};]};]
		(*  class A { Boolean m(String s, B b) {..} String m2() {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String"; mk_param "B"]; 
			mk_method "String" "m2" [];]; 
		 mk_class "B" [mk_method "A" "m3" [mk_param "Int"];]]

let test_class_with_parent _ =
	(* Two classes with one being the parent of the other *)
	build_success_test
		(* class A {} class B extends A {} *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[]};
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		[mk_class "A" []; mk_class_p "B" "A" []];

	(* Class A isn't defined *)
	build_failure_test
		[mk_class_p "B" "A" []]
		(UndefinedType "A");

	(* Two classes with one being the parent of the other and methods are involved!*)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Int m2(Int i) {..} } *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=[]
			};]};
		 {name="B"; parent=Some "A"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=[]
			};{
				name="m2";
				return="Int";
				static=false;
				cl="B";
				params=["Int"]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" []]; mk_class_p "B" "A" [mk_method "Int" "m2" [mk_param "Int"]]]

let test_method_redefinition _ =
	(* Redefinition of a parent method *)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=["Int"]
			};]};
		 {name="B"; parent=Some("A"); attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="B";
				params=["Int"]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "Int"]]];

	(* Illegal redefinition: new return type isn't a child of the old one *)
	build_failure_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" []]; mk_class_p "B" "A" [mk_method "Int" "m" []]]
		(Errors.TypeError("Boolean", "Int"));

	(* Legal redefinition: Boolean extends Object *)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Object";
				static=false;
				cl="A";
				params=["Int"]
			};]};
		 {name="B"; parent=Some("A"); attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="B";
				params=["Int"]
			};]};]
		[mk_class "A" [mk_method "Object" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "Int"]]];

	(* Not a redefinition: params are different *)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=["Int"]
			};]};
		 {name="B"; parent=Some("A"); attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=["Int"]
			};{
				name="m";
				return="Boolean";
				static=false;
				cl="B";
				params=["String"]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "String"]]];

	(* Not a redefinition: params are different *)
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=["Int"]
			};]};
		 {name="B"; parent=Some("A"); attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=false;
				cl="A";
				params=["Int"]
			};{
				name="m";
				return="Boolean";
				static=false;
				cl="B";
				params=["Int"; "Boolean"]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "Int"; mk_param "Boolean"]]]

let test_method_overloading _ = 
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
			name="m";
			return="Int";
			static=false;
			cl="A";
			params=["Int"]
		};{
			name="m";
			return="Int";
			static=false;
			cl="A";
			params=[]
		};{
			name="m";
			return="Int";
			static=false;
			cl="A";
			params=["Boolean"]
		};]}]
		[mk_class "A" [mk_method "Int" "m" [mk_param "Int"]; mk_method "Int" "m" []; 
			mk_method "Int" "m" [mk_param "Boolean"]]]

let test_attributes _ = 
	build_success_test
		(* class A {Int i} *)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr "Int" "i"]];
	build_success_test
		(* class A {Int i} *)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=true;};]; methods=[];}]
		[mk_class "A" [mk_sattr "Int" "i"]];
	build_success_test
		(* class A {Int i=1} *)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr_v "Int" "i" (Int (mk_none 1))]];
	build_success_test
		(* class A {static Int i=1} *)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=true;};]; methods=[];}]
		[mk_class "A" [mk_sattr_v "Int" "i" (Int (mk_none 1))]];
	build_success_test
		(* class A {Int i} class B extends A {Boolean b}*)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=false;};]; methods=[];};
		 {name="B"; parent=Some "A"; attributes=[
		 		{n="i"; t="Int"; attr=true; static=false;};
				{n="b"; t="Boolean"; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr "Int" "i"]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]];
	build_success_test
		(* class A {Int i=1} class B extends A {Boolean b}*)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=false;};]; methods=[];};
		 {name="B"; parent=Some "A"; attributes=[
		 		{n="i"; t="Int"; attr=true; static=false;};
				{n="b"; t="Boolean"; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr_v "Int" "i" (Int (mk_none 1))]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]];
	build_success_test
		(* class A {static Int i} class B extends A {Boolean b}*)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=true;};]; methods=[];};
		 {name="B"; parent=Some "A"; attributes=[
				{n="b"; t="Boolean"; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_sattr "Int" "i"]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]];
	build_success_test
		(* class A {static Int i= 1} class B extends A {Boolean b}*)
		[{name="A"; parent=Some "Object"; 
			attributes=[{n="i"; t="Int"; attr=true; static=true;};]; methods=[];};
		 {name="B"; parent=Some "A"; attributes=[
				{n="b"; t="Boolean"; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_sattr_v "Int" "i" (Int (mk_none 1))]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]]

let test_static_methods _ = 
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=true;
				cl="A";
				params=["Int"]
			};]}]
		(* class A { static Boolean m() {...} } *)
		[mk_class "A" [mk_smethod "Boolean" "m" [mk_param "Int"]];];
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=true;
				cl="A";
				params=["Int"]
		 };]}; 
		 {name="B"; parent=Some "A"; attributes=[]; methods=[]}]
		(* class A { static Boolean m() {...} class B extends A {} } *)
		[mk_class "A" [mk_smethod "Boolean" "m" [mk_param "Int"]];
		 mk_class_p "B" "A" []];
	build_success_test
		[{name="A"; parent=Some "Object"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=true;
				cl="A";
				params=["Int"]
		 };]};
		 {name="B"; parent=Some "A"; attributes=[]; methods=[{
				name="m";
				return="Boolean";
				static=true;
				cl="B";
				params=["Int"]
		 };]}]
		(* class A { static Boolean m() {..} } class B extends A { static Boolean m() {..} } *)
		(* Not a redefinition, two methods exist: A.m and B.m *)
		[mk_class "A" [mk_smethod "Boolean" "m" [mk_param "Int"]];
		 mk_class_p "B" "A" [mk_smethod "Boolean" "m" [mk_param "Int"]]]

let test_naming_conflicts _ = 
	(* Naming conflicts with attributes. *)
	build_failure_test
		(* class A {Int i; String i;} *)
		[mk_class "A" [mk_attr "Int" "i"; mk_attr "String" "i"]]
		(Errors.NamingError("i"));
	build_failure_test
		(* class A {static Int i; String i;} *)
		[mk_class "A" [mk_sattr "Int" "i"; mk_attr "String" "i"]]
		(Errors.NamingError("i"));
	build_failure_test
		(* class A {Int i; static String i;} *)
		[mk_class "A" [mk_attr "Int" "i"; mk_sattr "String" "i"]]
		(Errors.NamingError("i"));
	build_failure_test
		(* class A {Int i; } class B extends A {Boolean i;} *)
		[mk_class "A" [mk_attr "Int" "i"]; 
		 mk_class_p "B" "A" [mk_attr "Boolean" "i"]]
		(Errors.NamingError("i"));
	build_failure_test
		[mk_class "A" [mk_method "Int" "m" []; mk_method "Boolean" "m" [];]]
		(Errors.NamingError("m"));

	(* Naming conflicts with classes. *)
	build_failure_test
		(* Class A {} Class A {} *)
		[mk_class "A" []; mk_class "A" []]
		(Errors.NamingError("A"));
	build_failure_test
		(* Class Object {} *)
		[mk_class "Object" [];]
		(Errors.NamingError("Object"));
	build_failure_test
		(* Class Int {} *)
		[mk_class "Int" [];]
		(Errors.NamingError("Int"));
	build_failure_test
		(* Class String {} *)
		[mk_class "String" [];]
		(Errors.NamingError("String"));
	build_failure_test
		(* Class Boolean {} *)
		[mk_class "Boolean" [];]
		(Errors.NamingError("Boolean"));

	(* Naming conflicts with methods. *)
	build_failure_test
		(* class A {Int m() {} Int m() {}} *)
		[mk_class "A" [mk_method "Int" "m" []; mk_method "Int" "m" []]]
		(Errors.NamingError("m"));
	build_failure_test
		(* class A {Int m() {} Int m(Int) {}} *)
		[mk_class "A" [mk_method "Int" "m" [mk_param "Int"]; mk_method "Int" "m" [mk_param "Int"]]]
		(Errors.NamingError("m"));
	build_failure_test
		(* Even if return type is different, still doesn't work *)
		(* class A {Boolean m() {} Int m() {}} *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]; mk_method "Int" "m" [mk_param "Int"]]]
		(Errors.NamingError("m"))

	

(*************************************************************************************)
(*********************************** Test suite **************************************)

let suite =
	"suite">:::
		["basicClass">:: test_basic_class;
		 "manyClasses">:: test_many_classes;

		 "classWithParent">:: test_class_with_parent;

		 "methodRedefinition">:: test_method_redefinition;
		 "methodOverloading">:: test_method_overloading;

		 "attributes">:: test_attributes;

		 "staticMethods">:: test_static_methods;

		 "namingConflicts">:: test_naming_conflicts;
		]

let () =
  run_test_tt_main suite