{
open Parser

exception Error of string

let str_to_int base str =
  let mult = Z.of_int base in
  let limit = String.length str in
  let rec loop s acc i =
    if i >= limit then
      if s then acc else Z.neg acc
    else
      match str.[i] with
        | '0' .. '9' as ch ->
          shift s acc (Char.code ch - Char.code '0') (i + 1)
        | 'a' .. 'z' as ch ->
          shift s acc (Char.code ch - Char.code 'a' + 10) (i + 1)
        | 'A' .. 'Z' as ch ->
          shift s acc (Char.code ch - Char.code 'A' + 10) (i + 1)
        | '-' -> loop false acc (i + 1)
        | _ -> loop s acc (i + 1)
  and shift s hi lo i =
    loop s (Z.add (Z.mul hi mult) (Z.of_int lo)) i in
  loop true Z.zero 0
}

let newline = '\n' | '\r' | "\r\n"
let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '0'-'9' '_']*

let digit_hex = ['a'-'f' 'A'-'F' '0'-'9']
let digit_dec = ['0'-'9']
let digit_oct = ['0'-'7']
let digit_bin = ['0' '1']

(* utf-8 decoding magic *)
let usv_1 = ['\x00'-'\x7F']
let usv_2 = ['\xC2'-'\xDF'] ['\x80'-'\xBF']
let usv_3 =  '\xE0' ['\xA0'-'\xBF'] ['\x80'-'\xBF']
  | (['\xE1'-'\xEC'] | ['\xEE'-'\xEF']) ['\x80'-'\xBF'] ['\x80'-'\xBF']
  | '\xED' ['\x80'-'\x9F'] ['\x80'-'\xBF']
let usv_4 = '\xF0' ['\x90'-'\xBF'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
  | ['\xF1'-'\xF3'] ['\x80'-'\xBF'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
  | '\xF4' ['\x80'-'\x8F'] ['\x80'-'\xBF'] ['\x80'-'\xBF']
let codepoint = usv_1 | usv_2 | usv_3 | usv_4

rule read = parse
  (* comments *)
  | '#' { skip_line lexbuf }

  | ' ' | '\t' { read lexbuf }
  | newline { Lexing.new_line lexbuf; read lexbuf }

  | '('     { LPAREN }
  | ')'     { RPAREN }
  | '+'     { ADD }
  | '-'     { SUB }
  | '='     { SET }
  | "let"   { LET }
  | "in"    { IN }

  | '\"' { read_string (Buffer.create 32) lexbuf }
  | ['+' '-']? ['1'-'9'] ('_'? digit_dec)* as tl { INT (str_to_int 10 tl) }
  | ['+' '-']? '0' ['x' 'X'] ('_'? digit_hex)* as tl { INT (str_to_int 16 tl) }
  | ['+' '-']? '0' ['c' 'C'] ('_'? digit_oct)* as tl { INT (str_to_int 8 tl) }
  | ['+' '-']? '0' ['b' 'B'] ('_'? digit_bin)* as tl { INT (str_to_int 2 tl) }
  | ['+' '-']? '0' { INT Z.zero }
  | ident { IDENT (Lexing.lexeme lexbuf) }

  | eof { EOF }
  | codepoint
    { raise (Error ("Illegal source character " ^ (Lexing.lexeme lexbuf))) }
  | _ { raise (Error "Illegal encoded character") }

and skip_line = parse
  | newline { Lexing.new_line lexbuf; read lexbuf }
  | codepoint { skip_line lexbuf }
  | _ { raise (Error ("Invalid encoded character")) }
  | eof { EOF }

and read_string buf = parse
  | '\"' { STR (Buffer.contents buf) }
  | '\\'
    {
      let ch = read_escape lexbuf in
      Buffer.add_utf_8_uchar buf ch;
      read_string buf lexbuf
    }
  | ['\r' '\n'] { raise (Error "Invalid line break in string literal") }
  | codepoint
    {
      Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (Error "Invalid encoded character") }
  | eof { raise (Error "Unterminated string") }

and read_escape = parse
  | [ '\\' '\'' '\"' ] as c { Uchar.of_char c }
  | 'b' { Uchar.of_char '\b' }
  | 't' { Uchar.of_char '\t' }
  | 'n' { Uchar.of_char '\n' }
  | 'r' { Uchar.of_char '\r' }
  | 'f' { Uchar.of_char '\x0c' }
  | 'u' (digit_hex digit_hex digit_hex digit_hex as v)
    { int_of_string ("0x" ^ v) |> Uchar.of_int }
  | 'U' (digit_hex digit_hex digit_hex digit_hex digit_hex digit_hex as v)
    { int_of_string ("0x" ^ v) |> Uchar.of_int }
  | 'u' { raise (Error "Expected four hex digits to encode upto U+FFFF") }
  | 'U' { raise (Error "Expected six hex digits to encode upto U+10FFFF") }
  | codepoint
    {
      raise (Error ("Unsupported escape character " ^ (Lexing.lexeme lexbuf)))
    }
  | _ { raise (Error "Illegal encoded character") }
  | eof { raise (Error "Missing escape character") }
