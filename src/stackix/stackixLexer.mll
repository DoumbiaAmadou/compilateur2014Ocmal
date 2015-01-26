{
  open Lexing
  open Error
  open Position
  open StackixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let digit = ['0'-'9']

let lowercase_alpha = ['a'-'z' '_']

let uppercase_alpha = ['A'-'Z' '_']

let alpha = lowercase_alpha | uppercase_alpha

let alphanum = alpha | digit

let identifier = alpha alphanum*

rule token = parse
  (** Layout *)
  | newline              { next_line_and token lexbuf }
  | blank+               { token lexbuf }
  | ";;" ([^'\n']* as c) { COMMENT c }

  (** Keywords *)
  | "add"                 { ADD }
  | "mul"                 { MUL }
  | "div"                 { DIV }
  | "sub"                 { SUB }
  | "gt"                  { GT  }
  | "gte"                 { GTE }
  | "lt"                  { LT  }
  | "lte"                 { LTE }
  | "eq"                  { EQ }
  | "swap"                { SWAP }
  | "conditional_jump"    { CJUMP }
  | "jump"                { JUMP }
  | "ujump"               { UJUMP }
  | "or"                  { OR }
  | "remember"            { REMEMBER }
  | "define"              { DEFINE }
  | "undefine"            { UNDEFINE }
  | "getvariable"         { GETVARIABLE }
  | "exit"                { EXIT }
  | "block_create"        { BLOCKCREATE }
  | "block_get"           { BLOCKGET }
  | "block_set"           { BLOCKSET }
  | identifier as i       { ID i }
  | '@' (identifier as i) { LABEL i }


  (** Literals *)
  | digit+ as d     { INT (int_of_string d) }

  (** Punctuation *)
  | ":"             { COLON }
  | eof             { EOF }

  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }
