%{
  open Types
  open Errors
  open Location
  open Located
%}

%token EOF
%token CLASS EXTENDS 
%token LBRAK RBRAK
%token DIFF PTVIRGULE AFFECT
%token MINUS 
%token PLUS TIMES DIV MOD 
%token EQUALS INF INFEQ SUP SUPEQ DIFFEQ AND OR 
%token IN
%token NULL THIS
%token <string> STRING UIDENT LIDENT
%token <int> INT
%token <bool> BOOLEAN

%start compile_list
%type <Types.class_or_expr Located.t list> compile_list

/*%left PLUS MINUS
%left TIMES DIV MOD*/

%%

/* Add location information to an element */
loc(X) :
 | x = X { Located.mk_elem x (Location.symbol_loc $startpos $endpos) }

compile_list:
 | e=loc(class_or_expr)* EOF { e }
 | error /* This rule is automatically detected by menhir when the 
 			current token doesn't correspond to the grammar */
 	{ raise (Errors.PError (Errors.SyntaxError, (Location.symbol_loc $startpos $endpos))) }

class_or_expr:
 | c=classdef { c } 
 | e=loc(expr) { Expr(e) }

classdef:
 | CLASS n=loc(UIDENT) EXTENDS p=loc(classname) LBRAK l=loc(attr_or_method)* RBRAK 
 	{ ClassdefWithParent(n, p, l) }
 | CLASS n=loc(UIDENT) LBRAK l=loc(attr_or_method)* RBRAK 
 	{ Classdef(n, l) }

classname:
 | n=loc(UIDENT) { Classname(n) }

attr_or_method:
 | a=attribute { a }

attribute:
 | t=loc(classname) n=loc(LIDENT) PTVIRGULE { Attr(t, n) }
 | t=loc(classname) n=loc(LIDENT) AFFECT e=loc(expr) PTVIRGULE { AttrWithValue(t, n, e) }

expr:
 | i=loc(INT) { Int(i) }
 | b=loc(BOOLEAN) { Boolean(b) } 
 | s=loc(STRING) { String(s) }
 | NULL { Null }
 | THIS { This }
 | u=loc(unop) e=loc(expr) { Unop(u, e) }
 /*| e1=loc(expr) b=loc(bop) e2=loc(expr) { Binop(b, e1, e2) }*/
 | t=loc(classname) n=loc(LIDENT) AFFECT e1=loc(expr) IN e2=loc(expr) 
 	{ Instance(t, n, e1, e2) }

unop:
 | DIFF 	{ Udiff }
 | MINUS 	{ Uminus }

%inline bop:
 | PTVIRGULE { Bptvirg }
 | INF 		{ Binf }
 | INFEQ	{ BinfEq }
 | SUP		{ Bsup }
 | SUPEQ	{ Bsupeq }
 | DIFFEQ	{ Bdiff }
 | EQUALS	{ Beq } 
 | MINUS    { Bsub }
 | PLUS     { Badd }
 | TIMES    { Bmul }
 | DIV      { Bdiv }
 | MOD      { Bmod }
 | AND		{ Band }
 | OR 		{ Bor }

%%