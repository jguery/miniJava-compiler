{
  open Parser
  open Location
  open Buffer
}

let upperletter = ['A'-'Z']
let lowerletter = ['a'-'z']
let letter = upperletter | lowerletter
let digit = ['0'-'9']
let uident = upperletter (letter|digit|'_')*
let lident = lowerletter (letter|digit|'_')*
let newline = ('\010' | '\013' | "\013\010")
let space = [' ' '\t' '\r']

rule nexttoken = parse
  | newline { incr_line lexbuf; nexttoken lexbuf }
  | space+        { nexttoken lexbuf }
  | eof           { EOF }
  | "instanceof" { INSTANCEOF }
  | "static" { STATIC }
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
  | "\"" { parsestring (create 16) lexbuf }
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
  | "\\\\" { parsestring (add_char res '\\'; res) lexbuf }
  | "\\n" { parsestring (add_char res '\n'; res) lexbuf }
  | "\"" { STRING (contents res) }
  | newline as c { incr_line lexbuf; parsestring res lexbuf } (* New line in the code are not considered *)
  | eof { ERROR }
  | _ as c { parsestring (add_char res c; res) lexbuf }

and parseLongcomment = parse
  | "*/" { nexttoken lexbuf }
  | newline { incr_line lexbuf; parseLongcomment lexbuf }
  | eof { ERROR }
  | _ { parseLongcomment lexbuf }

and parseShortcomment = parse
  | newline { incr_line lexbuf; nexttoken lexbuf }
  | eof           { EOF }
  | _ { parseShortcomment lexbuf }