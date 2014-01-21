(* Tout est objet: tout renvoie une adresse vers un object! Et l'évaluation, sur des objets primitifs, sort la valeur de l'objet *)

open Hashtbl

open TypedStructure
open EvalStructures
open CompileStructures

(* Use a stack and a heap *)

let create_new_object_descriptor (class_descriptor: CompileStructures.class_descriptor) = 
	{ 
		t = class_descriptor.name;
	}

let rec string_of_evaluated_expr heap evaluated_expr_addr = 
	let t = (Hashtbl.find heap evaluated_expr_addr).t
	in match t with 
	(* TODO use this more !... *)
	| "String" -> "str"
	| _ -> "<Object " ^ t ^ " Address " ^ (string_of_int evaluated_expr_addr) ^ ">"


(* Evaluate an expression *)
(* Heap is a hash table with keys being addresses (mere integers) and values are object descriptors *)
(* Heap_size is the current size of the heap, to get the last free address in the hash table *)
(* Classes_descriptor is the output of the compiling process, it is a hash table containing the descriptions of classes *)
(* The expression is a located typed expression *)
let eval_expr heap heap_size stack classes_descriptor expr = 
	match Located.elem_of expr with
	| TypedInstance (c, t) -> Hashtbl.add heap (!heap_size) (create_new_object_descriptor 
		(Hashtbl.find classes_descriptor (Structure.string_of_classname (Located.elem_of c)))); 
		heap_size := !heap_size + 1; 	(* Increment heap size *)
		(!heap_size - 1) 				(* Returns the address of the object. *)


let eval typed_tree classes_descriptor = 
	let heap = Hashtbl.create 20
	and heap_size = ref 0
	in let rec rec_eval sub_tree =
		match sub_tree with
		| [] -> []
		| t::q -> (match Located.elem_of t with
					(* If this is a primitive type, give the value, otherwise give the address (strings in both cases) *)
				| TypedExpr e -> (string_of_evaluated_expr heap (eval_expr heap heap_size [] classes_descriptor e))::(rec_eval q)
					(* We don't evaluate classes, only expressions *)
				| _ -> rec_eval q
			)
	in 
	rec_eval typed_tree 	


let rec print_evaluated_list evaluated_list =
	match evaluated_list with
	| [] -> ""
	| t::q -> print_endline t; print_evaluated_list q