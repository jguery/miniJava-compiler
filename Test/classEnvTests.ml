open OUnit2

open Located
open Location
open Structure
open Errors
open Typer

exception TestError of Errors.error

(*************************************************************************************)
(***************************** Utils for building tests ******************************)

let rec string_of_expr_types = function
	| [] -> ""
	| t::q -> (string_of_expr_type t) ^ ", " ^ (string_of_expr_types q)

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

let mk_none x = 
	Located.mk_elem x (Location.none)

let mk_param t =
	mk_none (Param(mk_none (Classname(mk_none t)), mk_none "foo"))

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

let mk_class classname methods =
	mk_none (Classdef(mk_none classname, methods))

let mk_class_p classname parent methods =
	mk_none (ClassdefWithParent(mk_none classname, mk_none (Classname(mk_none parent)), methods))

let build_success_test expEnv structureTree =
	print_endline ((string_of_structure_tree structureTree) ^ " => " 
		^ (string_of_env (Typer.build_classes_env structureTree)));
	print_endline "========================================";	
	assert_equal expEnv (Typer.build_classes_env structureTree)

let build_failure_test structureTree undefinedType =
	let test _ = 
		try 
			print_endline (string_of_structure_tree structureTree);
			print_endline "========================================";
			Typer.build_classes_env structureTree
		with Errors.PError (e, l) ->
			(* Strip the location information *)
			raise (TestError e)
	in
	assert_raises 
		(TestError (Errors.UndefinedType(undefinedType))) 
		test


(*************************************************************************************)
(************************************** Tests ****************************************)

let test_basic_class _ = 
	(* A class with no method and no parent *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[]}]
		 (* class A {} *)
		[mk_class "A" []];

	(* A class with no parent and one method with no param *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=IntType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		(*  class A { Int m() {..} } *)
		[mk_class "A" [mk_method "Int" "m" [];]];

	(* A class with no parent and one method with one param *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=BooleanType;
			static=false;
			cl=CustomType "A";
			params=[StringType;]
		};]}]
		(*  class A { Int m(String s) {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String";];]];

	(* A class with no parent and one method with two params *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=BooleanType;
			static=false;
			cl=CustomType "A";
			params=[StringType; CustomType "B"]
		};]}]
		(*  class A { Int m(String s, B b) {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String"; mk_param "B"];]];

	(* A class with no parent and two methods *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=BooleanType;
			static=false;
			cl=CustomType "A";
			params=[StringType; CustomType "B"]
		};{
			name="m2";
			return=StringType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}]
		(*  class A { Boolean m(String s, B b) {..} String m2() {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String"; mk_param "B"]; 
			mk_method "String" "m2" [];]]

let test_many_classes _ =
	(* Two classes with no method and no parent *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[]}; 
		 {name="B"; parent=ObjectType; attributes=[]; methods=[]}]
		 (* class A {} class B {} *)
		[mk_class "A" []; mk_class "B" []];

	(* Two classes with methods *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
			name="m";
			return=BooleanType;
			static=false;
			cl=CustomType "A";
			params=[StringType; CustomType "B"]
		};{
			name="m2";
			return=StringType;
			static=false;
			cl=CustomType "A";
			params=[]
		};]}; {name="B"; parent=ObjectType; attributes=[]; methods=[{
			name="m3";
			return=CustomType "A";
			static=false;
			cl=CustomType "B";
			params=[IntType;]
		};]};]
		(*  class A { Boolean m(String s, B b) {..} String m2() {..} } *)
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "String"; mk_param "B"]; 
			mk_method "String" "m2" [];]; 
		 mk_class "B" [mk_method "A" "m3" [mk_param "Int"];]]

let test_class_with_parent _ =
	(* Two classes with one being the parent of the other *)
	build_success_test
		(* class A {} class B extends A {} *)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[]};
		 {name="B"; parent=CustomType("A"); attributes=[]; methods=[]}]
		[mk_class "A" []; mk_class_p "B" "A" []];

	(* Class A isn't defined *)
	build_failure_test
		[mk_class_p "B" "A" []]
		"A";

	(* Two classes with one being the parent of the other and methods are involved!*)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Int m2(Int i) {..} } *)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[]
			};]};
		 {name="B"; parent=CustomType("A"); attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[]
			};{
				name="m2";
				return=IntType;
				static=false;
				cl=CustomType "B";
				params=[IntType]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" []]; mk_class_p "B" "A" [mk_method "Int" "m2" [mk_param "Int"]]]

let test_method_redefinition _ =
	(* Redefinition of a parent method *)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[IntType]
			};]};
		 {name="B"; parent=CustomType("A"); attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "B";
				params=[IntType]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "Int"]]];

	(* Signatures of methods doesn't take return type into account for redefinition *)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[]
			};]};
		 {name="B"; parent=CustomType("A"); attributes=[]; methods=[{
				name="m";
				return=IntType;
				static=false;
				cl=CustomType "B";
				params=[]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" []]; mk_class_p "B" "A" [mk_method "Int" "m" []]];

	(* Not a redefinition: params are different *)
	build_success_test
		(* class A { Boolean m() {..} } class B extends A { Boolean m() {..} } *)
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[IntType]
			};]};
		 {name="B"; parent=CustomType("A"); attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[IntType]
			};{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "B";
				params=[StringType]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "String"]]];

	(* Not a redefinition: params are different *)
	build_success_test
		[{name="A"; parent=ObjectType; attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[IntType]
			};]};
		 {name="B"; parent=CustomType("A"); attributes=[]; methods=[{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "A";
				params=[IntType]
			};{
				name="m";
				return=BooleanType;
				static=false;
				cl=CustomType "B";
				params=[IntType; BooleanType]
			};]};]
		[mk_class "A" [mk_method "Boolean" "m" [mk_param "Int"]]; 
		 mk_class_p "B" "A" [mk_method "Boolean" "m" [mk_param "Int"; mk_param "Boolean"]]]

let test_attributes _ = 
	build_success_test
		(* class A {Int i} *)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr "Int" "i"]];
	build_success_test
		(* class A {Int i} *)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=true;};]; methods=[];}]
		[mk_class "A" [mk_sattr "Int" "i"]];
	build_success_test
		(* class A {Int i=1} *)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr_v "Int" "i" (Int (mk_none 1))]];
	build_success_test
		(* class A {static Int i=1} *)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=true;};]; methods=[];}]
		[mk_class "A" [mk_sattr_v "Int" "i" (Int (mk_none 1))]];
	build_success_test
		(* class A {Int i} class B extends A {Boolean b}*)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=false;};]; methods=[];};
		 {name="B"; parent=CustomType "A"; attributes=[
		 		{n="i"; t=IntType; attr=true; static=false;};
				{n="b"; t=BooleanType; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr "Int" "i"]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]];
	build_success_test
		(* class A {Int i=1} class B extends A {Boolean b}*)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=false;};]; methods=[];};
		 {name="B"; parent=CustomType "A"; attributes=[
		 		{n="i"; t=IntType; attr=true; static=false;};
				{n="b"; t=BooleanType; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_attr_v "Int" "i" (Int (mk_none 1))]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]];
	build_success_test
		(* class A {Int i} class B extends A {Boolean b}*)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=true;};]; methods=[];};
		 {name="B"; parent=CustomType "A"; attributes=[
		 		{n="i"; t=IntType; attr=true; static=true;};
				{n="b"; t=BooleanType; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_sattr "Int" "i"]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]];
	build_success_test
		(* class A {Int i} class B extends A {Boolean b}*)
		[{name="A"; parent=ObjectType; 
			attributes=[{n="i"; t=IntType; attr=true; static=true;};]; methods=[];};
		 {name="B"; parent=CustomType "A"; attributes=[
		 		{n="i"; t=IntType; attr=true; static=true;};
				{n="b"; t=BooleanType; attr=true; static=false;};]; methods=[];}]
		[mk_class "A" [mk_sattr_v "Int" "i" (Int (mk_none 1))]; mk_class_p "B" "A" [mk_attr "Boolean" "b"]]


(*************************************************************************************)
(*********************************** Test suite **************************************)

let suite =
	"suite">:::
		["basicClass">:: test_basic_class;
		 "manyClasses">:: test_many_classes;

		 "classWithParent">:: test_class_with_parent;

		 "methodRedefinition">:: test_method_redefinition;

		 "attributes">:: test_attributes;
		]

let () =
  run_test_tt_main suite