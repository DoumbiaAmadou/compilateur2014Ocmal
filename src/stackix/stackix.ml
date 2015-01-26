(** The stackix programming language. *)

module AST = StackixAST

type ast =
    StackixAST.t

let parse lexer_init input =
  SyntacticAnalysis.process
    ~lexer_init
    ~lexer_fun:StackixLexer.token
    ~parser_fun:StackixParser.program
    ~input

let parse_filename filename =
  parse Lexing.from_channel (open_in filename)

let extension =
  ".stackix"

let parse_string =
  parse Lexing.from_string

let print_ast ast =
  StackixPrettyPrinter.(to_string program ast)

include StackixInterpreter
include StackixTypechecker
