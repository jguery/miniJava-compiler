open OUnit2

open Parser
open Structure
open Errors
open Location
open Located
open Expr

let unity x = 
	x

let test1 test_ctxt = assert_equal "x" (unity "x");;

let test2 test_ctxt = assert_equal 100 (unity 100);;

let suite =
"suite">:::
 ["test1">:: test1;
  "test2">:: test2]


let () =
  run_test_tt_main suite