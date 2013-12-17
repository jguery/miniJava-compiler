%{
  open Types
%}


%token EOF CLASS EXTENDS OBRAK FBRAK PTVIRGULE
%token <string> STRING UIDENT LIDENT
%token <int> INT

%start compile_list
%type <Types.class_or_expr list> compile_list

%%

compile_list:
 | e=class_or_expr* EOF { e }

class_or_expr:
 | c=classdef {c} 
 /* | e=expr {e} */

classdef:
 | CLASS n=UIDENT EXTENDS p=UIDENT OBRAK l=attr_or_method* FBRAK { ClassdefWithParent(n, Classname(p), l) }
 | CLASS n=UIDENT OBRAK l=attr_or_method* FBRAK { Classdef(n, l) }

attr_or_method:
 | a=attribute {a}

attribute:
 | t=UIDENT n=LIDENT PTVIRGULE { Attr(Classname(t), n) }

%%