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
  | "if" { IF }
  | "else" { ELSE }
  | "new" { NEW }
  | "/*" { parseLongcomment lexbuf }
  | "//" { parseShortcomment lexbuf }
  | "\"" { parsestring "" lexbuf }
  | "{" { LBRAK }
  | "}" { RBRAK }
  | "(" { LPAR }
  | ")" { RPAR }
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
  | ";" { SEMICOL }
  | "," { COMMA }
  | "." { POINT }
  | digit+ as nb  { INT (int_of_string nb) }
  | uident         { UIDENT (Lexing.lexeme lexbuf) }
  | lident { LIDENT (Lexing.lexeme lexbuf) }
  | _ { ERROR } (* This is just so any character is taken into account *)

and parsestring res = parse
  | str as s { parsestring s lexbuf }
  | "\"" { STRING res }

and parseLongcomment = parse
  | "*/" { nexttoken lexbuf }
  | newline { incr_line lexbuf; parseLongcomment lexbuf }
  | _ { parseLongcomment lexbuf }

and parseShortcomment = parse
  | newline { incr_line lexbuf; nexttoken lexbuf }
  | eof           { EOF }
  | _ { parseShortcomment lexbuf }