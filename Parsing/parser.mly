%{
  open Types
  open Errors
  open Location
%}


%token EOF CLASS EXTENDS OBRAK FBRAK PTVIRGULE AFFECT NULL THIS
%token <string> STRING UIDENT LIDENT
%token <int> INT
%token <bool> BOOLEAN

%start compile_list
%type <Types.class_or_expr list> compile_list

%%

compile_list:
 | e=class_or_expr* EOF { e }
 | error { raise (Errors.PError (Errors.SyntaxError, (Location.symbol_loc $startpos $endpos))) }

class_or_expr:
 | c=classdef {c} 
 /* | e=expr {e} */

classdef:
 | CLASS n=UIDENT EXTENDS p=UIDENT OBRAK l=attr_or_method* FBRAK { ClassdefWithParent(n, Classname(p), l) }
 | CLASS n=UIDENT OBRAK l=attr_or_method* FBRAK { Classdef(n, l) }

attr_or_method:
 | a=attribute { a }

attribute:
 | t=UIDENT n=LIDENT PTVIRGULE { Attr(Classname(t), n) }
 | t=UIDENT n=LIDENT AFFECT e=expr PTVIRGULE { AttrWithValue(Classname(t), n, e) }

expr:
 | i=INT { Int(i) }
 | b=BOOLEAN { Boolean(b) } 
 | s=STRING { String(s) }
 | NULL { Null }
 | THIS { This }

%%