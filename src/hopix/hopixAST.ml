(** The abstract syntax tree for hopix programs. *)

open Position

type program = definition located list

and definition =
  | DefineValue of
      pattern located * expression located

  | DefineType of
      type_identifier * type_definition

and expression =
  | Literal of literal
  | Variable of identifier
  | Define of pattern located * expression located * expression located
  | Apply of expression located * expression located
  | Fun of lambda
  | RecFuns of (typed_identifier located * expression located) list
  | Tuple of expression located list
  | Record of (label * expression located) list
  | RecordField of expression located * label
  | TaggedValues of tag * expression located list
  | IfThenElse of expression located * expression located * expression located
  | Case of expression located * branch list

  (* Only appears in the image of closure conversion. *)
  | MutateTuple of expression located * int * expression located

and lambda = typed_identifier * expression located

and typed_identifier = identifier * typ option

and tag =
  | Constructor of string

and branch =
  | Branch of pattern located * expression located

and pattern =
  | PWildcard
  | PVariable     of identifier
  | PTuple        of identifier list
  | PTaggedValues of tag * identifier list

and literal =
  | LInt of int

and identifier =
  | Id of string

and formals =
    typed_identifier list

and typ =
  | TyIdentifier of type_identifier
  | TyTuple      of typ list
  | TyArrow      of typ * typ

and type_definition =
  | RecordTy      of (label * typ) list
  | TaggedUnionTy of (tag * typ list) list

and label =
  | Label of string

and type_identifier =
  | TId of string

and t = program
