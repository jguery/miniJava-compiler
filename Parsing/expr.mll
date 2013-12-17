{
  open Parser
}

let upperletter = ['A'-'Z']
let lowerletter = ['a'-'z']
let letter = upperletter | lowerletter
let digit = ['0'-'9']
let uident = upperletter (letter|digit|'_')*
let lident = lowerletter (letter|digit|'_')*
let ident = letter (letter | digit | '_')*
let space = [' ' '\t' '\n']

rule nexttoken = parse
  | space+        { nexttoken lexbuf }
  | eof           { EOF }
  | "class"	{ CLASS }
  | "extends" {EXTENDS}
  | 
  | "+"           { PLUS } 
  | "-"           { MINUS } 
  | "/"           { DIV } 
  | "*"           { TIMES } 
  | "%"           { MOD } 
  | digit+ as nb  { INT (int_of_string nb) }
  | uident         { UIDENT (Lexing.lexeme lexbuf) }