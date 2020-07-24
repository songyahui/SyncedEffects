{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

(* part 1 *)
let int =  '-'? ['0'-'9'] ['0'-'9']*

(* part 2 *)
let digit = ['0'-'9']
let frac = '.' digit*
let exp = ['e' 'E'] ['-' '+']? digit+
let float = digit* frac? exp?

(* part 3 *)
let white = [' ' '\t']+
let newline = '\n' | '\r' | "\r\n" 
let id = ['a'-'v' 'x'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*


rule token = parse
| white    { token lexbuf }
| newline  { next_line lexbuf; token lexbuf }
| "nothing" { NOTHING }
| "pause" {PAUSE}  
| "loop" {LOOP}
| "signal" {SIGNAL}
| "emit" {EMIT}
| "present" {PRESENT}
| "trap" {TRAP}
| "exit" {EXIT}
| "emp" { EMPTY }
| "ensure" {ENSURE}
| '(' { LPAR }
| ')' { RPAR }
| ';' { SIMI }
| int      { INTE (int_of_string (Lexing.lexeme lexbuf)) }
| '.' { CONCAT }
| "||" { PAR }
| 'X' {NEXT}
| 'U' {UNTIL}
| id as str { VAR str }
| "|-" {ENTIL}
| "\\/" {DISJ}
| '_' {UNDERLINE}
| '[' { LBrackets }
| ']' { RBrackets }
| ',' { COMMA }

| '^' { POWER }
| 'w' { OMEGA }
| '*' {KLEENE}
| "<>" {FUTURE}  
| "[]" {GLOBAL}
| "->" {IMPLY}
| '!' {LTLNOT}

| "&&" {LILAND}
| "||" {LILOR}

| "/*" {LSPEC}
| "*/" {RSPEC}
| eof { EOF }

(*

| "TRUE" { TRUE }
| "FALSE" { FALSE }
| "if" {IF}
| "else" {ELSE}
| "require" {REQUIRE}

| "include" {INCLUDE}
| "true" { TRUEE (bool_of_string (Lexing.lexeme lexbuf))}
| "false" { FALSEE (bool_of_string (Lexing.lexeme lexbuf))}
| '"'      { read_string (Buffer.create 17) lexbuf }
| ">=" {GTEQ}
| "<=" {LTEQ}
| '>' {GT}
| '<' {LT}
| '=' {EQ}

| '|' { CHOICE }

| '"' { read_string (Buffer.create 17) lexbuf }

| '[' { LBrackets }
| ']' { RBrackets }
| '{' { LBRACK  }
| '}' { RBRACK }


| '+' { PLUS }
| '-' { MINUS }
| '#' { SHARP }


| '~' {NEGATION}


| "/\\" {CONJ}
| "==" {EQEQ}
| ">=" {GTEQ}
| "<=" {LTEQ}

*)
| _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }


(* part 5 
and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+
    { Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (SyntaxError ("String is not terminated")) }

  *)
