%{
  open Types
%}


%token EOF CLASS EXTENDS OBRAK CBRAK
%token <string> STRING UIDENT LIDENT
%token <int> INT

%start compile_tree
%type <Types.compile_tree> compile_tree

compile_tree:
 | e=class_or_expr EOF {e}

class_or_expr:
 | c=class {c} 
 | e=expr {e}

class:
 | CLASS n=UIDENT (EXTENDS p=UIDENT)? OBRAK FBRAK { {name=n,  parent=p, core=[]]} }

