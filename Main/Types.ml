type binop =
  | Bptvirg | Binf | BinfEq | Bsup | Bsupeq | Bdiff | Beq 
  | Badd | Bsub | Bmul | Bdiv | Bmod | Band | Bor

type unop =
  | Udiff | Uminus

type class = { name : string; parent : class; core : attr_or_method list }

type compile_tree = 
  | Class of class
  (* | Expression of expression *)