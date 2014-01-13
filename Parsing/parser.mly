%{
  open Structure
  open Errors
  open Location
  open Located
%}

/* This token is defined to signal a lexical error. It is never used in this 
parser on purpose, because when raised, the "error" litteral defined by menhir 
will be called, thus raising a syntax exception. */
%token ERROR 

%token EOF
%token CLASS EXTENDS 
%token LBRAK RBRAK LPAR RPAR
%token DIFF SEMICOL AFFECT COMMA POINT
%token MINUS 
%token PLUS TIMES DIV MOD 
%token EQUALS INF INFEQ SUP SUPEQ DIFFEQ AND OR 
%token IN
%token NEW STATIC
%token INSTANCEOF
%token IF ELSE
%token NULL THIS

%token <string> STRING UIDENT LIDENT
%token <int> INT
%token <bool> BOOLEAN

%start structure_tree

/* This parser returns a list of located classes and expressions. */
%type <Structure.class_or_expr Located.t list> structure_tree


/* These priorities follow the Java priorities, as found at http://bmanolov.free.fr/javaoperators.php */

%left EXPR 	/* The continued definition of an expression is prioritary to the definition of a new one */
%left SEMICOL		/* Allows to link expressions before defining a new one (in structure_tree) */
%left AFF 	/* The rule of affectation precedes the one of defining a new expression. */
%left ATTRAFFECT /* The semicolon at the end of an attribute affectation ends the affectation */
%left OR
%left BOPSBOOL
%left AND
%left INF INFEQ SUP SUPEQ DIFFEQ EQUALS
%left MINUS PLUS
%left BOPSNUM
%left TIMES DIV MOD
%left BOPSOTHER
%right UNOPS	/* Resolves the -1-1 type conflict: what is the middle MINUS ? */

%%

/* Add location information to an element */
loc(X) :
 | x = X { Located.mk_elem x (Location.symbol_loc $startpos $endpos) }

structure_tree:
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
 | t=loc(classname) n=loc(LIDENT) SEMICOL { Attr(t, n) }
 | STATIC t=loc(classname) n=loc(LIDENT) SEMICOL { StaticAttr(t, n) }
 | t=loc(classname) n=loc(LIDENT) AFFECT e=loc(terminal_expr) SEMICOL { AttrWithValue(t, n, e) }
 	/* Only terminal expressions in an attribute definition, to suppress conflicts */
 | STATIC t=loc(classname) n=loc(LIDENT) AFFECT e=loc(terminal_expr) SEMICOL { StaticAttrWithValue(t, n, e) }
 | r=loc(classname) n=loc(LIDENT) LPAR p=separated_list(COMMA,loc(param)) RPAR LBRAK e=loc(expr) RBRAK
 	{ Method(r, n, p, e) }
 | STATIC r=loc(classname) n=loc(LIDENT) LPAR p=separated_list(COMMA,loc(param)) RPAR LBRAK e=loc(expr) RBRAK
 	{ StaticMethod(r, n, p, e) }

param:
 | c=loc(classname) n=loc(LIDENT) { Param(c, n) }

expr:
 | a=loc(LIDENT) AFFECT e=loc(expr) %prec ATTRAFFECT { AttrAffect(a, e) }
 | u=loc(unop) e=loc(expr) %prec UNOPS { Unop(u, e) }
 | e1=loc(expr) b=loc(bopnum) e2=loc(expr) %prec BOPSNUM { Binop(b, e1, e2) }
 | e1=loc(expr) b=loc(bopbool) e2=loc(expr) %prec BOPSBOOL { Binop(b, e1, e2) }
 | e1=loc(expr) b=loc(bopother) e2=loc(expr) %prec BOPSOTHER { Binop(b, e1, e2) }
 | e1=loc(expr) b=loc(SEMICOL) e2=loc(expr) %prec SEMICOL 
 	{ Binop(Located.mk_elem Bsemicol (Located.loc_of b), e1, e2) }
 | IF LPAR e1=loc(expr) RPAR LBRAK e2=loc(expr) RBRAK ELSE LBRAK e3=loc(expr) RBRAK 
 	{ Condition(e1, e2, e3) }
 | e=middle_expr { e }

middle_expr:
 | t=loc(classname) n=loc(LIDENT) AFFECT e1=loc(expr) IN e2=loc(expr) %prec AFF
 	{ Local(t, n, e1, e2) }
 | e1=loc(terminal_expr) POINT m=loc(LIDENT) LPAR args=separated_list(COMMA,loc(expr)) RPAR
 	{ MethodCall(e1, m, args) } 
 	/* Method calls are applied to final expressions only, so that:
 		a+b.m() == a+(b.m())
 	*/
 | t=loc(classname) POINT m=loc(LIDENT) LPAR args=separated_list(COMMA,loc(expr)) RPAR
 	{ StaticMethodCall(t, m, args) }  
 | e=loc(terminal_expr) INSTANCEOF t=loc(classname) { Instanceof(e,t) }
 	/* "instanceof" is applied to terminal expressions only */
 | e=terminal_expr { e }

terminal_expr:
 | i=loc(INT) { Int(i) }
 | b=loc(BOOLEAN) { Boolean(b) } 
 | s=loc(STRING) { String(s) }
 | v=loc(LIDENT) { Var(v) }
 | NULL { Null }
 | THIS { This }
 | NEW t=loc(classname) { Instance(t) }
 | LPAR t=loc(classname) RPAR e=loc(terminal_expr) { Cast(t, e) }
 	/* Cast is performed on terminal expressions only */
 | LPAR e=expr RPAR { e }

%inline unop:
 | DIFF 	{ Udiff }
 | MINUS  	{ Uminus }

%inline bopnum:
 | MINUS    { Bsub }
 | PLUS     { Badd }
 | TIMES    { Bmul }
 | DIV      { Bdiv }
 | MOD      { Bmod }

%inline bopbool:
 | AND		{ Band }
 | OR 		{ Bor }

%inline bopother:
 | INF 		{ Binf }
 | INFEQ	{ Binfeq }
 | SUP		{ Bsup }
 | SUPEQ	{ Bsupeq }
 | DIFFEQ	{ Bdiff }
 | EQUALS	{ Beq }


%%