(* Tout est objet: tout renvoie une adresse vers un object! Et l'évaluation, sur des objets primitifs, sort la valeur de l'objet *)

open Hashtbl

open Structure
open TypedStructure
open EvalStructures
open CompileStructures
open Errors

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

let type_from_object_descriptor = function
	| ObjectDescriptor od -> od.t
	| IntDescriptor _ -> "Int"
	| BooleanDescriptor _ -> "Boolean"
	| StringDescriptor _ -> "String"

(* Search an address in the heap. The address must lead to a valid object, otherwise we throw an exception. *)
(* Note that sometimes it is OK to have a null object. One should use this function when it is not. *)
let search_heap heap addr loc =
	if addr = -1 then
		raise (Errors.PError(NullError, loc))
	else
		Hashtbl.find heap addr

(* Evaluate an expression *)
(* Heap is a hash table with keys being addresses (mere integers) and values are object descriptors *)
(* Heap_size is the current size of the heap, to get the last free address in the hash table *)
(* Stack is a final hash table with key: name of a local object (variable/attribute), value: address in the heap *)
(* Classes_descriptor is the output of the compiling process, it is a hash table containing the descriptions of classes *)
(* This_addr is the address in the heap of the current object we are evaluating (if we are in a non static method core) *)
(* The expression is a located typed expression *)
let rec eval_expr heap heap_size stack classes_descriptor methods_table (this_addr: int option) expr = 

	let create_new_default_object_descriptor (class_descriptor: CompileStructures.class_descriptor) = 
		let create_new_hashtable newhash k v =
			Hashtbl.add newhash k (eval_expr heap heap_size stack classes_descriptor methods_table None v)
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
		in let addr_e1 = eval_expr heap heap_size stack classes_descriptor methods_table this_addr e1
		and addr_e2 = eval_expr heap heap_size stack classes_descriptor methods_table this_addr e2
		and nb = Located.elem_of b
		in match nb with
		| Bsemicol -> addr_e2
		| Badd | Bmul | Bdiv | Bsub | Bmod -> 
			let e1_val = int_value (search_heap heap addr_e1 (Located.loc_of e1))
			and e2_val = int_value (search_heap heap addr_e2 (Located.loc_of e2))
			in let res = match nb with
				| Badd -> e1_val + e2_val
				| Bmul -> e1_val * e2_val
				| Bdiv -> e1_val / e2_val
				| Bsub -> e1_val - e2_val
				| Bmod -> e1_val mod e2_val
			in add_to_heap heap heap_size (IntDescriptor (Some res))

		| Band | Bor ->
			let e1_val = bool_value (search_heap heap addr_e1 (Located.loc_of e1))
			and e2_val = bool_value (search_heap heap addr_e2 (Located.loc_of e2))
			in let res = match nb with
				| Band -> e1_val && e2_val
				| Bor -> e1_val || e2_val
			in add_to_heap heap heap_size (BooleanDescriptor (Some res))

		| Binf | Binfeq | Bsup | Bsupeq ->
			let e1_val = int_value (search_heap heap addr_e1 (Located.loc_of e1))
			and e2_val = int_value (search_heap heap addr_e2 (Located.loc_of e2))
			in add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb e1_val e2_val)))

		| Bdiff | Beq -> (
			match search_heap heap addr_e1 (Located.loc_of e1), search_heap heap addr_e2 (Located.loc_of e2) with
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

	and eval_method_call caller m_name args t =

		let addr_caller = eval_expr heap heap_size stack classes_descriptor methods_table this_addr caller
			(* Caller can't be null *)
		in let type_caller = type_from_object_descriptor (search_heap heap addr_caller (Located.loc_of caller))
		in let class_des = Hashtbl.find classes_descriptor type_caller
		in let args_types = TypedStructure.types_of_expressions args
		in let short_id_m = build_short_method_identifier (Located.elem_of m_name) args_types
		in match class_des with
		| ClassDescriptor cd ->
			let id_m = Hashtbl.find cd.methods short_id_m 
			in let method_descriptor = Hashtbl.find methods_table id_m 
			in let new_stack = Hashtbl.create 5 
			in let rec build_new_stack args_left names_left = (* By construction, args_left and names_left have the same length *)
				match args_left, names_left with
				| [], [] -> ()
				| e::q, n::q2 -> 
					let addr_e = eval_expr heap heap_size stack classes_descriptor methods_table this_addr e
					in 
					(* Add to the new stack the argument, with the correct name and the link to the right address in the heap. *)
					Hashtbl.add new_stack n addr_e;
					build_new_stack q q2
			in 
			build_new_stack args method_descriptor.args_names;
			eval_expr heap heap_size new_stack
				classes_descriptor methods_table 
				(Some addr_caller) (* "this" becomes the caller object *)
				method_descriptor.core (* Evaluate the expression of the method *)
		| _ -> -1 (* TODO what if we call a method from a basic type ?? *)

	and eval_var_call var_name t =
		(* Look for the variable in the stack, and then in the attributes of "this" *)
		(* The variable MUST exist in one of those places, otherwise the typer would have raised an exception earlier *)
		try
			Hashtbl.find stack (Located.elem_of var_name)
		with Not_found ->
			(* Variable HAS to be an attribute, thanks to the typer. Thus, Option.get cannot throw an exception. *)
			let object_descriptor = Hashtbl.find heap (Option.get this_addr)
			in match object_descriptor with
			| ObjectDescriptor od -> Hashtbl.find od.attrs_values (Located.elem_of var_name)
			| _ -> -1 (* TODO really can't happen ? *)

	and eval_attr_affect attr_name e t =
		(* Variable HAS to be an attribute, thanks to the typer. Thus, Option.get cannot throw an exception. *)
		let object_descriptor = Hashtbl.find heap (Option.get this_addr)
		in match object_descriptor with
		| ObjectDescriptor od ->
			let new_attr_addr = eval_expr heap heap_size stack classes_descriptor methods_table this_addr e
			in 
			(* We should replace the object in the heap with the new value of the attribute, 
				but because of how eval_expr works, it is easier to just move the address of 
				the value of the attribute. Not so memory efficient... *)
			Hashtbl.replace od.attrs_values (Located.elem_of attr_name) new_attr_addr;
			new_attr_addr
		| _ -> -1 (* TODO really can't happen ? *)
 
	in match Located.elem_of expr with
	| TypedNull -> -1 (* -1 is the address of null *)
	| TypedThis t -> Option.get this_addr (* Cannot raise exception because typer already treats the error *)
	| TypedInt (i, t) -> add_to_heap heap heap_size (IntDescriptor (Some (Located.elem_of i)))
	| TypedString (s, t) -> add_to_heap heap heap_size (StringDescriptor (Some (Located.elem_of s)))
	| TypedBoolean (b, t) -> add_to_heap heap heap_size (BooleanDescriptor (Some (Located.elem_of b)))
	| TypedInstance (c, t) -> add_to_heap heap heap_size (create_new_default_object_descriptor 
			(Hashtbl.find classes_descriptor (Structure.string_of_classname (Located.elem_of c))))
	| TypedBinop (b, e1, e2, t) -> eval_binop b e1 e2 t
	| TypedMethodCall (caller, m_name, args, t) -> eval_method_call caller m_name args t
	| TypedVar (var_name, t) -> eval_var_call var_name t
	| TypedAttrAffect (attr_name, e, t) -> eval_attr_affect attr_name e t
	| TypedLocal (apparent_type, var_name, var_expr, sub_expr, t) ->

(* 	  | TypedLocal of classname Located.t * string Located.t * typed_expr Located.t * typed_expr Located.t 
  	* string
 *)


let eval typed_tree classes_descriptor methods_table = 
	let heap = Hashtbl.create heap_default_size
	and heap_size = ref 0
	in let rec rec_eval sub_tree =
		match sub_tree with
		| [] -> []
		| t::q -> (match Located.elem_of t with
					(* If this is a primitive type, give the value, otherwise give the address (strings in both cases) *)
				| TypedExpr e -> (string_of_evaluated_expr heap (eval_expr heap heap_size (Hashtbl.create 0) classes_descriptor methods_table None e))
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