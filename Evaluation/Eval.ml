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

let bool_value o = match o with
	| BooleanDescriptor b -> Option.get b

let string_value o = match o with
	| StringDescriptor s -> Option.get s

let add_to_heap heap size_ref v =
	(* Increment heap size. *)
	size_ref := !size_ref + 1;
	Hashtbl.add heap (!size_ref-1) v;
	(!size_ref - 1)	(* Return heap address of the element we added *)

(* Evaluate an expression *)
(* Heap is a hash table with keys being addresses (mere integers) and values are object descriptors *)
(* Heap_size is the current size of the heap, to get the last free address in the hash table *)
(* Stack is a final hash table with key: name of a local object (variable/attribute), value: address in the heap *)
(* Classes_descriptor is the output of the compiling process, it is a hash table containing the descriptions of classes *)
(* This_addr is the address in the heap of the current object we are evaluating (if we are in a non static method core) *)
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
		let eval_bool_binop binop a b = match binop with
			| Beq -> a = b
			| Bdiff -> a <> b
			| Binf -> a < b
			| Binfeq -> a <= b
			| Bsup -> a > b
			| Bsupeq -> a >= b
		in let addr_e1 = eval_expr heap heap_size stack classes_descriptor this_addr e1
		and addr_e2 = eval_expr heap heap_size stack classes_descriptor this_addr e2
		and nb = Located.elem_of b
		in match nb with
		| Bsemicol -> addr_e2
		| Badd | Bmul | Bdiv | Bsub | Bmod -> 
			let e1_val = int_value (Hashtbl.find heap addr_e1)
			and e2_val = int_value (Hashtbl.find heap addr_e2)
			in let res = match nb with
				| Badd -> e1_val + e2_val
				| Bmul -> e1_val * e2_val
				| Bdiv -> e1_val / e2_val
				| Bsub -> e1_val - e2_val
				| Bmod -> e1_val mod e2_val
			in add_to_heap heap heap_size (IntDescriptor (Some res))

		| Band | Bor ->
			let e1_val = bool_value (Hashtbl.find heap addr_e1)
			and e2_val = bool_value (Hashtbl.find heap addr_e2)
			in let res = match nb with
				| Band -> e1_val && e2_val
				| Bor -> e1_val || e2_val
			in add_to_heap heap heap_size (BooleanDescriptor (Some res))

		| Binf | Binfeq | Bsup | Bsupeq ->
			let e1_val = int_value (Hashtbl.find heap addr_e1)
			and e2_val = int_value (Hashtbl.find heap addr_e2)
			in add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb e1_val e2_val)))

		| Bdiff | Beq -> (
			match Hashtbl.find heap addr_e1, Hashtbl.find heap addr_e2 with
				| IntDescriptor i, IntDescriptor j -> 
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb i j)))
				| BooleanDescriptor b, BooleanDescriptor d -> 
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb b d)))
				| StringDescriptor s, StringDescriptor ss -> 
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb s ss)))
				| ObjectDescriptor o1, ObjectDescriptor o2 -> 
					(* For two objects to be equal, they actually have to be the same object *)
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb addr_e1 addr_e2)))
			)

	in match Located.elem_of expr with
	| TypedNull -> -1 (* -1 is the address of null *)
	| TypedThis t -> Option.get this_addr (* Cannot raise exception because typer already treats the error *)
	| TypedInt (i, t) -> add_to_heap heap heap_size (IntDescriptor (Some (Located.elem_of i)))
	| TypedString (s, t) -> add_to_heap heap heap_size (StringDescriptor (Some (Located.elem_of s)))
	| TypedBoolean (b, t) -> add_to_heap heap heap_size (BooleanDescriptor (Some (Located.elem_of b)))
	| TypedInstance (c, t) -> add_to_heap heap heap_size (create_new_default_object_descriptor 
			(Hashtbl.find classes_descriptor (Structure.string_of_classname (Located.elem_of c))))
	| TypedBinop (b, e1, e2, t) -> eval_binop b e1 e2 t


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