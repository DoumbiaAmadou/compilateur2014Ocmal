(** The abstract syntax tree for datix programs. *)

open Position

type program = definition located list

and definition =
  | DefineValue of
      pattern located * expression located
  (* FUNC : identifier{ position  , value } , formal , type option , expression Located *)
  | DefineFunction of
      function_identifier located
    * formals * typ option
    * expression located
(*TYPE : identidier , definition *)
  | DefineType of
      type_identifier * type_definition
      
and expression =
  | Literal of literal
  | Variable of identifier
  | Define of pattern located * expression located * expression located
  | FunCall of function_identifier * expression located list
  | IfThenElse of expression located * expression located * expression located
  | Tuple of expression located list
  | Record of (label * expression located) list
  | RecordField of expression located * label
  | TaggedValues of tag * expression located list
  | Case of expression located * branch list

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

and typed_identifier =
    identifier * typ option

and identifier =
  | Id of string

and formals =
    (identifier * typ) list

and function_identifier =
  | FunId of string

and typ =
  | TyIdentifier of type_identifier
  | TyTuple      of typ list

and type_definition =
  | RecordTy      of (label * typ) list
  | TaggedUnionTy of (tag * typ list) list

and label =
  | Label of string

and type_identifier =
  | TId of string

and t = program
