{
  open Parser
  open Location
}

let upperletter = ['A'-'Z']
let lowerletter = ['a'-'z']
let letter = upperletter | lowerletter
let digit = ['0'-'9']
let uident = upperletter (letter|digit|'_')*
let lident = lowerletter (letter|digit|'_')*
let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\t' '\r']

let str = [^'"']+

rule nexttoken = parse
  | newline { incr_line lexbuf; nexttoken lexbuf }
  | space+        { nexttoken lexbuf }
  | eof           { EOF }
  | "class"	{ CLASS }
  | "extends" { EXTENDS }
  | "true" { BOOLEAN true }
  | "false" { BOOLEAN false }
  | "null" { NULL }
  | "this" { THIS }
  | "in" { IN }
  | "\"" { parsestring "" lexbuf }
  | "{" { LBRAK }
  | "}" { RBRAK }
  | "!" { DIFF }
  | "-" { MINUS }
  | "+" { PLUS } 
  | "*" { TIMES }
  | "/" { DIV }
  | "%" { MOD }
  | "&&" { AND }
  | "||" { OR } 
  | "!=" { DIFFEQ }
  | "==" { EQUALS }
  | ">=" { SUPEQ }
  | ">" { SUP }
  | "<=" { INFEQ }
  | "<" { INF } 
  | "=" { AFFECT }
  | ";" { PTVIRGULE }
  | digit+ as nb  { INT (int_of_string nb) }
  | uident         { UIDENT (Lexing.lexeme lexbuf) }
  | lident { LIDENT (Lexing.lexeme lexbuf) }


and parsestring res = parse
  | str as s { parsestring s lexbuf }
  | "\"" { STRING res }