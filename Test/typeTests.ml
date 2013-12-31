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

let build_success_test expType expr =
	print_endline ((Structure.string_of_expr expr) ^ " => " ^ (Typer.string_of_expr_type expType));
	print_endline "========================================";
	assert_equal expType (Typer.type_of_expr (Typer.type_expr expr))

let build_failure_test expr expType realType =
	let test _ = 
		try 
			print_endline ((Structure.string_of_expr expr) ^ " => Expected " 
				^ (Typer.string_of_expr_type expType) ^ ", got " 
				^ (Typer.string_of_expr_type realType));
			print_endline "========================================";
			Typer.type_expr expr
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


(*************************************************************************************)
(************************************** Tests ****************************************)

let test_unop _ = 
	build_success_test 
		Typer.BooleanType 
		(* !true *)
		(Unop(mk_none Udiff, mk_none (Boolean (mk_none true))));
	build_success_test 
		Typer.IntType 
		(* -10 *)
		(Unop(mk_none Uminus, mk_none (Int (mk_none 10))));
	build_failure_test
		(* -true *)
		(Unop(mk_none Uminus, mk_none (Boolean (mk_none true))))
		IntType
		BooleanType;
	build_failure_test
		(* !10 *)
		(Unop(mk_none Udiff, mk_none (Int (mk_none 10))))
		BooleanType
		IntType

(*************************************************************************************)
(*********************************** Test suite **************************************)

let suite =
	"suite">:::
		["unop">:: test_unop;
		]

let () =
  run_test_tt_main suite