(** The abstract syntax tree for fopix programs. *)

open Position

type program = definition list

and definition =
  | DefineValue    of identifier located * expression located
  | DefineFunction of function_identifier located * formals * expression located

and expression =
  | Literal of literal
  | Variable of identifier
  | Define of identifier located * expression located * expression located
  | FunCall of function_identifier * expression located list
  | IfThenElse of expression located * expression located * expression located
  | UnknownFunCall of expression located * expression located list


and literal =
  | LInt of int
  | LFun of function_identifier

and identifier =
  | Id of string

and formals =
    identifier list

and function_identifier =
  | FunId of string

and t = program
