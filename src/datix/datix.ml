(** The datix programming language. *)

module AST = DatixAST

type ast = DatixAST.t

let parse lexer_init input =
  SyntacticAnalysis.process
    ~lexer_init
    ~lexer_fun:DatixLexer.token
    ~parser_fun:DatixParser.program
    ~input

let parse_filename filename =
  parse Lexing.from_channel (open_in filename)

let extension =
  ".datix"

let parse_string =
  parse Lexing.from_string

let print_ast ast =
  DatixPrettyPrinter.(to_string program ast)

let print_expression ast =
  DatixPrettyPrinter.(to_string expression ast)

include DatixInterpreter

include DatixTypechecker
