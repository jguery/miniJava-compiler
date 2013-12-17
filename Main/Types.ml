type binop =
  | Bptvirg | Binf | BinfEq | Bsup | Bsupeq | Bdiff | Beq 
  | Badd | Bsub | Bmul | Bdiv | Bmod | Band | Bor

type unop =
  | Udiff | Uminus

type classname =
  | Classname of string (* Name of a class, which has to be defined, otherwise the compiler will fail (later)  *)

type attr_or_method = 
  | Attr of classname * string

type class_or_expr = 
  | Classdef of string * attr_or_method list (* No parent: Object class *)
  | ClassdefWithParent of string * classname * attr_or_method list

  (* | Expression of expression *)
