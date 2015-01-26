(** The abstract syntax tree for stackix programs. *)

open Position

type t = labelled_instruction list

and labelled_instruction =
    label option * instruction located

and instruction =
  | Remember of int
  | RememberLabel of label
  | Swap
  | Binop of binop
  | Define of identifier
  | Undefine
  | GetVariable of int
  | UJump
  | Jump of label
  | ConditionalJump of label * label
  | Exit
  | Comment of string
  | BlockCreate
  | BlockGet
  | BlockSet

and binop = Add | Mul | Div | Sub | GT | LT | GTE | LTE | EQ

and label = Label of string

and identifier = Id of string
