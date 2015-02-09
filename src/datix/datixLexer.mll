{
  open Lexing
  open Error
  open Position
  open DatixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

}

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let digit = ['0'-'9']

let lowercase_alpha = ['_' 'a'-'z']

let uppercase_alpha = ['A'-'Z']

let alpha = lowercase_alpha | uppercase_alpha

let alphanum = alpha | digit | '_'

let identifier = lowercase_alpha alphanum*

let uidentifier = uppercase_alpha alphanum*

rule token = parse
  (** Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }
  | "/*"            { comment 1 lexbuf           }

  (** Keywords *)
  | "type"          { TYPE }
  | "val"           { VAL  }
  | "in"            { IN   }
  | "def"           { DEF  }
  | "end"           { END  }
  | "if"            { IF   }
  | "then"          { THEN }
  | "else"          { ELSE }
  | "eval"          { EVAL }
  | "case"          { CASE }
  | "with"          { WITH }
  | "mutate"        { MUTATE }

  (** Literals *)
  | digit+ as d     { INT (int_of_string d) }

  (** Symbols *)
  | "_"             { UNDERSCORE }
  | "?"             { QMARK     }

  (** Identifiers *)
  | identifier as i  { ID i  }
  | uidentifier as i { UID i }

  (** Infix operators *)
  | "."             { DOT        }
  | "|"             { PIPE       }
  | "="             { EQUAL      }
  | "+"             { PLUS       }
  | "*"             { STAR       }
  | "/"             { SLASH      }
  | "-"             { MINUS      }
  | ">"             { GT         }
  | ">="            { GTE        }
  | "<"             { LT         }
  | "<="            { LTE        }
  | "->"            { RIGHTARROW }
  | "&"             { UPPERSAND  }

  (** Punctuation *)
  | ","             { COMMA     }
  | ";"             { SEMICOLON }
  | ":"             { COLON     }
  | "{"             { LBRACE    }
  | "}"             { RBRACE    }
  | "("             { LPAREN    }
  | ")"             { RPAREN    }
  | "["             { LBRACKET  }
  | "]"             { RBRACKET  }
  | eof             { EOF       }

  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }

and comment level = parse
  | "*/" {
    if level = 1 then
      token lexbuf
    else
      comment (pred level) lexbuf
  }
  | "/*" {
    comment (succ level) lexbuf
  }
  | eof {
    error lexbuf "unterminated comment."
  }
  | newline {
    next_line_and (comment level) lexbuf
  }
  | _ {
    comment level lexbuf
  }
