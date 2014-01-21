open Hashtbl

open TypedStructure
open CompileStructures

let compile typed_tree = 
	let classes_descriptors = Hashtbl.create 5 
	in let rec rec_compile = function
		| [] -> classes_descriptors
		| t::q -> (match Located.elem_of t with
					| TypedClassdef (n, l) -> Hashtbl.add classes_descriptors (Located.elem_of n) {name=(Located.elem_of n);size=0}; rec_compile q
					| TypedExpr e -> rec_compile q
			)
	in rec_compile typed_tree

(* 	  | TypedClassdef of string Located.t * typed_attr_or_method Located.t list
  | TypedClassdefWithParent of string Located.t * classname Located.t * typed_attr_or_method Located.t list 
  | TypedExpr of typed_expr Located.t
 *)