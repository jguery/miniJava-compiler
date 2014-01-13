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
    (* This is a hack so that any character is matched with something *)
  | _ { ERROR } 

(* Builds a string which will be sent to the parser once quotes are closed. *)
and parsestring res = parse
  | "\\\\" { parsestring (Buffer.add_char res '\\'; res) lexbuf }
    (* Understand that a \n means indeed a newline. *)
  | "\\n" { parsestring (Buffer.add_char res '\n'; res) lexbuf }
    (* Send the string object to the parser *)
  | "\"" { STRING (Buffer.contents res) }
    (* New line in the code are not considered *)
  | newline as c { incr_line lexbuf; parsestring res lexbuf } 
    (* This will raise a syntax error if a string is not closed when reaching the end of a file *)
  | eof { ERROR } 
  | _ as c { parsestring (Buffer.add_char res c; res) lexbuf }

and parseLongcomment = parse
    (* End of the comment, go on to the next token *)
  | "*/" { nexttoken lexbuf }
  | newline { incr_line lexbuf; parseLongcomment lexbuf }
    (* This will raise a syntax error if a comment is not closed when reaching the end of a file *)
  | eof { ERROR }
  | _ { parseLongcomment lexbuf }

and parseShortcomment = parse
    (* End of the comment, go on to the next token *)
  | newline { incr_line lexbuf; nexttoken lexbuf }
  | eof           { EOF }
  | _ { parseShortcomment lexbuf }