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

let build_static_attr_id classname attr_name = 
	classname ^ "," ^ attr_name

(* Evaluate an expression *)
(* Heap is a hash table with keys being addresses (mere integers) and values are object descriptors *)
(* Heap_size is the current size of the heap, to get the last free address in the hash table *)
(* Stack is a final hash table with key: name of a local object (variable/attribute), value: address in the heap *)
(* Static_attrs is a hash table with key: id of a static addr (see build_static_attr_id), value: address in the heap of the result *)
(* Classes_descriptor is the output of the compiling process, it is a hash table containing the descriptions of classes *)
(* Classname_str is the name of the class the expression is from, or None if we are not in a class *)
(* This_addr is the address in the heap of the current object we are evaluating (if we are in a non static method core) *)
(* The expression is a located typed expression *)
let rec eval_expr heap heap_size stack static_attrs classes_descriptor methods_table (classname_str: string option) (this_addr: int option) expr = 

	let create_new_default_object_descriptor (class_descriptor: CompileStructures.class_descriptor) = 
		let create_new_hashtable newhash k (v: attribute_descriptor) =
			(* We only care for non static attributes *)
			match v.static with 
			| false -> Hashtbl.add newhash k (eval_expr heap heap_size stack static_attrs classes_descriptor methods_table None None v.default)
			| true -> ()
		in match class_descriptor with
		| ClassDescriptor descriptor -> ObjectDescriptor({ 
				t = descriptor.name;
				(* Instantiate the attributes of the object with their default values *)
				attrs_values = (let a = Hashtbl.create 10 in Hashtbl.iter (create_new_hashtable a) descriptor.attributes; a);
			})
		| IntClass -> IntDescriptor None
		| BooleanClass -> BooleanDescriptor None
		| StringClass -> StringDescriptor None

	in let eval_unop u e t = 
		let addr_e = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e
		in match Located.elem_of u with 
		| Udiff -> 
			let e_val = bool_value (search_heap heap addr_e (Located.loc_of e))
			in add_to_heap heap heap_size (BooleanDescriptor (Some (not e_val)))
		| Uminus ->
			let e_val = int_value (search_heap heap addr_e (Located.loc_of e))
			in add_to_heap heap heap_size (IntDescriptor (Some (-e_val)))

	and eval_binop b e1 e2 t = 
		let eval_bool_binop binop a b = match binop with
			| Beq -> a = b
			| Bdiff -> a <> b
			| Binf -> a < b
			| Binfeq -> a <= b
			| Bsup -> a > b
			| Bsupeq -> a >= b
		in let addr_e1 = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e1
		and addr_e2 = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e2
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

		| Bdiff | Beq -> 
			if addr_e1 = addr_e2 then 
				(* If two objects have the same address, they have to be the same. 
					This treats stuff like if(i==null) with i being a basic type. *)
				add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb addr_e1 addr_e2)))
			else begin match search_heap heap addr_e1 (Located.loc_of e1), search_heap heap addr_e2 (Located.loc_of e2) with
				(* TODO deal with Int i; Int j; i==j ou i==null; *)
				| IntDescriptor i, IntDescriptor j -> 
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb i j)))
				| BooleanDescriptor b, BooleanDescriptor d -> 
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb b d)))
				| StringDescriptor s, StringDescriptor ss -> 
					add_to_heap heap heap_size (BooleanDescriptor (Some (eval_bool_binop nb s ss)))
				| ObjectDescriptor o1, ObjectDescriptor o2 -> 
					(* For two objects to be equal, they actually have to be the same object (same address) *)
					(* At this stage, we know it's not true, otherwise the first if would have been true *)
					add_to_heap heap heap_size (BooleanDescriptor (Some false))
			end

	and _eval_method_call m_this_addr caller_type m_name args t = 
		let class_des = Hashtbl.find classes_descriptor caller_type
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
					let addr_e = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e
					in 
					(* Add to the new stack the argument, with the correct name and the link to the right address in the heap. *)
					Hashtbl.add new_stack n addr_e;
					build_new_stack q q2
			in 
			build_new_stack args method_descriptor.args_names;
			eval_expr heap heap_size new_stack static_attrs
				classes_descriptor methods_table 
				(Some caller_type) m_this_addr 
				method_descriptor.core (* Evaluate the expression of the method *)
		| _ -> -1 (* TODO what if we call a method from a basic type ?? *)

	in let eval_method_call caller m_name args t =
		let addr_caller = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr caller
			(* Caller can't be null *)
		in let type_caller = type_from_object_descriptor (search_heap heap addr_caller (Located.loc_of caller))
		in 
		_eval_method_call 
			(Some addr_caller) (* "this" becomes the caller object *)
			type_caller 
			m_name args t

	and eval_static_method_call classname m_name args t =
		_eval_method_call 
			None (* "this" doesn't exist in a static method *)
			(string_of_classname (Located.elem_of classname)) 
			m_name args t

	and eval_var_call var_name t =
		(* Look for the variable in the stack, in the static_attrs, and then in the attributes of "this" *)
		(* The variable MUST exist in one of those places, otherwise the typer would have raised an exception earlier *)
		try
			Hashtbl.find stack (Located.elem_of var_name)
		with Not_found ->
			try
				(* It could be a static attribute *)
				let static_attr_id = build_static_attr_id (Option.get classname_str) (Located.elem_of var_name)
				in Hashtbl.find static_attrs static_attr_id
			with Not_found ->
				(* It is a non static attribute *)
				let object_descriptor = Hashtbl.find heap (Option.get this_addr)
				in match object_descriptor with
				| ObjectDescriptor od -> Hashtbl.find od.attrs_values (Located.elem_of var_name)
				| _ -> -1 (* This cannot be refering to a basic type (so far) *)

	and eval_attr_affect attr_name e t =
		let modif_heap table id = 
			let new_attr_addr = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e
			in
			(* We should replace the object in the heap with the new value of the attribute, 
				but because of how eval_expr works, it is easier to just move the address of 
				the value of the attribute. Not so memory efficient... 
				Yet, we don't know if the address was used by someone else, so we can't do that *)
			Hashtbl.replace table id new_attr_addr;
			new_attr_addr
		in try
			let static_attr_id = build_static_attr_id (Option.get classname_str) (Located.elem_of attr_name)
			in 
			(* Make this call so that not found is raised if the attribute is not static *)
			Hashtbl.find static_attrs static_attr_id; 
			modif_heap static_attrs static_attr_id
		with Not_found ->
			(* Variable HAS to be an attribute, thanks to the typer. Thus, Option.get cannot throw an exception. *)
			let this_descriptor = Hashtbl.find heap (Option.get this_addr)
			in match this_descriptor with
			| ObjectDescriptor od ->
				let new_attr_addr = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e
				in modif_heap od.attrs_values (Located.elem_of attr_name)
			| _ -> -1 (* This cannot refer to a basic type, can't happen *)

	and eval_local apparent_type var_name var_expr sub_expr t =
		(* The apparent type was really just used in the typer. We only care here about the real type. *)
		let var_addr = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr var_expr
		in let new_stack = Hashtbl.copy stack
		in 
		Hashtbl.add new_stack (Located.elem_of var_name) var_addr;
		eval_expr heap heap_size new_stack static_attrs classes_descriptor methods_table classname_str this_addr sub_expr
 
	and eval_condition e_if e_then e_else t =
		let addr_e_if = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e_if
		in let val_e_if = bool_value (search_heap heap addr_e_if (Located.loc_of e_if))
		in 
		if val_e_if then 
			eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e_then
		else 
			eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e_else

	in let rec _is_parent parent daughter =
		(* Parent and daughter are classes descriptors *)
		match parent, daughter with 
		| ObjectClass, ObjectClass -> false
		| ObjectClass, _ -> true
		| _, ObjectClass -> false

		| _, ClassDescriptor d_cd -> 
			let daughter_parent_des =  (Hashtbl.find classes_descriptor d_cd.parent)
			in if (daughter_parent_des = parent) then true else 
				_is_parent parent daughter_parent_des

		| _, _ -> false (* Things of the sort parent=Int, child=Boolean *)

	in let eval_instance_of e classname t =
		let addr_e = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e 
		in let type_e = type_from_object_descriptor (search_heap heap addr_e (Located.loc_of e))
		in let e_des = Hashtbl.find classes_descriptor type_e
		and class_des = Hashtbl.find classes_descriptor (string_of_classname (Located.elem_of classname))
		in let res = (e_des = class_des) || _is_parent class_des e_des
		in 
		add_to_heap heap heap_size (BooleanDescriptor (Some res))

	and eval_cast classname e t =
		let type_to = string_of_classname (Located.elem_of classname)
		in let des_type_to = Hashtbl.find classes_descriptor type_to
		in let addr_e = eval_expr heap heap_size stack static_attrs classes_descriptor methods_table classname_str this_addr e 
		in let type_e = type_from_object_descriptor (search_heap heap addr_e (Located.loc_of e))
		in let des_e = Hashtbl.find classes_descriptor type_e
		in 
		if (type_to = type_e || _is_parent des_type_to des_e || _is_parent des_e des_type_to) then 
			(* We never actually change the value of the object *)
			addr_e
		else 
			raise (PError(IllegalRuntimeCast(type_e, type_to), Located.loc_of e))

	in match Located.elem_of expr with
	| TypedNull -> -1 (* -1 is the address of null *)
	| TypedThis t -> Option.get this_addr (* Cannot raise exception because typer already treats the error *)
	| TypedInt (i, t) -> add_to_heap heap heap_size (IntDescriptor (Some (Located.elem_of i)))
	| TypedString (s, t) -> add_to_heap heap heap_size (StringDescriptor (Some (Located.elem_of s)))
	| TypedBoolean (b, t) -> add_to_heap heap heap_size (BooleanDescriptor (Some (Located.elem_of b)))
	| TypedInstance (c, t) -> add_to_heap heap heap_size (create_new_default_object_descriptor 
			(Hashtbl.find classes_descriptor (Structure.string_of_classname (Located.elem_of c))))
	| TypedUnop (u, e, t) -> eval_unop u e t
	| TypedBinop (b, e1, e2, t) -> eval_binop b e1 e2 t
	| TypedMethodCall (caller, m_name, args, t) -> eval_method_call caller m_name args t
	| TypedStaticMethodCall (classname, m_name, args, t) -> eval_static_method_call classname m_name args t
	| TypedVar (var_name, t) -> eval_var_call var_name t
	| TypedAttrAffect (attr_name, e, t) -> eval_attr_affect attr_name e t
	| TypedLocal (apparent_type, var_name, var_expr, sub_expr, t) -> eval_local apparent_type var_name var_expr sub_expr t
	| TypedCondition (e_if, e_then, e_else, t) -> eval_condition e_if e_then e_else t
	| TypedInstanceof (e, classname, t) -> eval_instance_of e classname t
	| TypedCast (classname, e, t) -> eval_cast classname e t


let build_static_attrs heap heap_size classes_descriptor methods_table =
	let static_attrs = Hashtbl.create 10
	in let iterate k v = 
		let iter_attr ka (va: attribute_descriptor) = match va.static with
			| true -> Hashtbl.add static_attrs 
				(build_static_attr_id k ka) 
				(eval_expr heap heap_size (Hashtbl.create 0) (Hashtbl.create 0) classes_descriptor methods_table None None va.default)
			| false -> ()
		in match v with
		| ClassDescriptor cd -> Hashtbl.iter iter_attr cd.attributes
		| _ -> ()
	in 
	Hashtbl.iter iterate classes_descriptor;
	static_attrs

let eval typed_tree classes_descriptor methods_table = 
	let heap = Hashtbl.create heap_default_size
	and heap_size = ref 0
	in let static_attrs = build_static_attrs heap heap_size classes_descriptor methods_table 
	in let rec rec_eval sub_tree =
		match sub_tree with
		| [] -> []
		| t::q -> (match Located.elem_of t with
					(* If this is a primitive type, give the value, otherwise give the address (strings in both cases) *)
				| TypedExpr e -> 
					let addr_e = eval_expr heap heap_size (Hashtbl.create 0) static_attrs classes_descriptor methods_table None None e
					in (string_of_evaluated_expr heap addr_e)::(rec_eval q)
					(* We don't evaluate classes, only expressions *)
				| _ -> rec_eval q
			)
	in 
	rec_eval typed_tree 	


let rec print_evaluated_list evaluated_list =
	match evaluated_list with
	| [] -> ""
	| t::q -> print_endline t; print_evaluated_list q