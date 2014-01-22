(* Tout est objet: tout renvoie une adresse vers un object! Et l'évaluation, sur des objets primitifs, sort la valeur de l'objet *)

open Hashtbl

open Structure
open TypedStructure
open EvalStructures
open CompileStructures

let heap_default_size = 20

(* Use a stack and a heap *)

let rec string_of_evaluated_expr (heap:(int, object_descriptor) Hashtbl.t) evaluated_expr_addr = 
	if evaluated_expr_addr >= 0 then begin
		let object_descriptor = (Hashtbl.find heap evaluated_expr_addr)
		in match object_descriptor with 
		| ObjectDescriptor od -> (match od.t with 
				(* TODO use this more !... *)
				| "String" -> "str"
				| _ -> "<Object " ^ od.t ^ " Address " ^ (string_of_int evaluated_expr_addr) ^ ">"
			)	
		| IntDescriptor i -> if (Option.is_none i) then "Null" else string_of_int (Option.get i)
		| BooleanDescriptor b -> if (Option.is_none b) then "Null" else string_of_bool (Option.get b)
		| StringDescriptor s -> if (Option.is_none s) then "Null" else Option.get s
	end else "Null"

let int_value o = match o with 
	| IntDescriptor i -> Option.get i

(* Evaluate an expression *)
(* Heap is a hash table with keys being addresses (mere integers) and values are object descriptors *)
(* Heap_size is the current size of the heap, to get the last free address in the hash table *)
(* Classes_descriptor is the output of the compiling process, it is a hash table containing the descriptions of classes *)
(* The expression is a located typed expression *)
let rec eval_expr heap heap_size stack classes_descriptor (this_addr: int option) expr = 

	let create_new_default_object_descriptor (class_descriptor: CompileStructures.class_descriptor) = 
		let create_new_hashtable newhash k v =
			Hashtbl.add newhash k (eval_expr heap heap_size stack classes_descriptor None v)
		in match class_descriptor with
		| ClassDescriptor descriptor -> ObjectDescriptor({ 
				t = descriptor.name;
				attrs_values = (let a = Hashtbl.create 10 in Hashtbl.iter (create_new_hashtable a) descriptor.attributes; a);
			})
		| IntClass -> IntDescriptor None
		| BooleanClass -> BooleanDescriptor None
		| StringClass -> StringDescriptor None

	in let eval_binop b e1 e2 t = 
		let addr_e1 = eval_expr heap heap_size stack classes_descriptor this_addr e1
		and addr_e2 = eval_expr heap heap_size stack classes_descriptor this_addr e2
		and nb = Located.elem_of b
		in match nb with
		| Badd | Bmul | Bdiv | Bsub | Bmod -> 
			let e1_val = int_value (Hashtbl.find heap addr_e1)
			and e2_val = int_value (Hashtbl.find heap addr_e2)
			in let res = match nb with
				| Badd -> e1_val + e2_val
				| Bmul -> e1_val * e2_val
				| Bdiv -> e1_val / e2_val
				| Bsub -> e1_val - e2_val
				| Bmod -> e1_val % e2_val
			in
			heap_size := !heap_size + 1;
			Hashtbl.add heap (!heap_size-1) (IntDescriptor (Some res));
			(!heap_size - 1)

	in match Located.elem_of expr with
	| TypedNull -> -1 (* -1 is the address of null *)
	| TypedThis t -> Option.get this_addr (* Cannot raise exception because typer already treats the error *)
	| TypedInt (i, t) -> 
		heap_size := !heap_size + 1; 
		Hashtbl.add heap (!heap_size-1) (IntDescriptor (Some (Located.elem_of i))); 
		(!heap_size - 1)
	| TypedString (s, t) -> 
		heap_size := !heap_size + 1; 
		Hashtbl.add heap (!heap_size-1) (StringDescriptor (Some (Located.elem_of s))); 
		(!heap_size - 1)
	| TypedBoolean (b, t) -> 
		heap_size := !heap_size + 1; 
		Hashtbl.add heap (!heap_size-1) (BooleanDescriptor (Some (Located.elem_of b))); 
		(!heap_size - 1)
	| TypedInstance (c, t) -> 
		heap_size := !heap_size + 1; 	(* Increment heap size *)
		Hashtbl.add heap (!heap_size-1) (create_new_default_object_descriptor 
			(Hashtbl.find classes_descriptor (Structure.string_of_classname (Located.elem_of c)))); 
		(!heap_size - 1) 				(* Returns the address of the object. *)
	| TypedBinop (b, e1, e2, t) -> eval_binop b e1 e2 t

(* 	  | TypedBinop of binop Located.t * typed_expr Located.t * typed_expr Located.t * string
 *)


let eval typed_tree classes_descriptor = 
	let heap = Hashtbl.create heap_default_size
	and heap_size = ref 0
	in let rec rec_eval sub_tree =
		match sub_tree with
		| [] -> []
		| t::q -> (match Located.elem_of t with
					(* If this is a primitive type, give the value, otherwise give the address (strings in both cases) *)
				| TypedExpr e -> (string_of_evaluated_expr heap (eval_expr heap heap_size [] classes_descriptor None e))
					::(rec_eval q)
					(* We don't evaluate classes, only expressions *)
				| _ -> rec_eval q
			)
	in 
	rec_eval typed_tree 	


let rec print_evaluated_list evaluated_list =
	match evaluated_list with
	| [] -> ""
	| t::q -> print_endline t; print_evaluated_list q