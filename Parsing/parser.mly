%{
  open Types
  open Errors
  open Location
  open Located
%}

%token EOF
%token CLASS EXTENDS 
%token LBRAK RBRAK
%token DIFF SEMICOL AFFECT
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

%left EXPR 	/* The continued definition of an expression is prioritary to the definition of a new one */
%left AFF 	/* The rule of affectation precedes the one of defining a new expression. */
%left SEMICOL		/* Allows to link expressions before defining a new one (in compile_list) */
%left MINUS PLUS 	/* The usual calc precedence levels */
%left TIMES DIV MOD
%left OR
%left AND
%left INF INFEQ SUP SUPEQ DIFFEQ EQUALS
%right UNOPS	/* Resolves the -1-1 type conflict: what is the middle MINUS ? */

%%

/* Add location information to an element */
loc(X) :
 | x = X { Located.mk_elem x (Location.symbol_loc $startpos $endpos) }

compile_list:
 | e=loc(class_or_expr)* EOF { e }
 | error /* This rule is automatically detected by menhir when the 
 			current token doesn't fit in the grammar */
 	{ raise (Errors.PError (Errors.SyntaxError, (Location.symbol_loc $startpos $endpos))) }

class_or_expr:
 | c=classdef { c } 
 | e=loc(expr) %prec EXPR { Expr(e) }

classdef:
 | CLASS n=loc(UIDENT) EXTENDS p=loc(classname) LBRAK l=loc(attr_or_method)* RBRAK 
 	{ ClassdefWithParent(n, p, l) }
 | CLASS n=loc(UIDENT) LBRAK l=loc(attr_or_method)* RBRAK 
 	{ Classdef(n, l) }

classname:
 | n=loc(UIDENT) { Classname(n) }

attr_or_method:
 | t=loc(classname) n=loc(LIDENT) { Attr(t, n) }
 | t=loc(classname) n=loc(LIDENT) AFFECT e=loc(expr) { AttrWithValue(t, n, e) }
 /* Change in the grammar: attributes don't end with a semicolon */

expr:
 | u=loc(unop) e=loc(expr) %prec UNOPS { Unop(u, e) }
 | e1=loc(expr) b=loc(bop) e2=loc(final_expr) { Binop(b, e1, e2) }
 | t=loc(classname) n=loc(LIDENT) AFFECT e1=loc(expr) IN e2=loc(expr) %prec AFF
 	{ Instance(t, n, e1, e2) }
 | e=final_expr { e }

 final_expr:
 | i=loc(INT) { Int(i) }
 | b=loc(BOOLEAN) { Boolean(b) } 
 | s=loc(STRING) { String(s) }
 | NULL { Null }
 | THIS { This }

%inline unop:
 | DIFF 	{ Udiff }
 | MINUS  	{ Uminus }

%inline bop:
 | SEMICOL  { Bsemicol }
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