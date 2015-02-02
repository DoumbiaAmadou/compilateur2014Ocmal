(** This module offers a pretty-printer for Stackix programs. *)

open PPrint
open PPrintCombinators
open PPrintEngine

open StackixAST

let located f x = f (Position.value x)

let max_label_length =
  List.fold_left (fun m -> function
    | (Some (Label l), _) -> max m (String.length l)
    | (None, _) -> m
  ) 0

let rec program p =
  let lsize = max_label_length p in
  separate_map hardline (labelled_instruction lsize) p

and labelled_instruction lsize (l, i) =
  label lsize l ^^ instruction (Position.value i)

and label lsize = function
  | None -> string (String.make (lsize + 2) ' ')
  | Some (Label l) -> string (Printf.sprintf "%*s: " lsize l)

and instruction = function
  | Define (Id x) ->
    string ("define " ^ x)
  | Undefine ->
    string "undefine"
  | Remember i ->
    string "remember " ^^ string (string_of_int i)
  | RememberLabel (Label l) ->
    string ("remember @" ^ l)
  | Swap ->
    string "swap"
  | GetVariable i ->
    string "getvariable " ^^ string (string_of_int i)
  | Binop op -> string (binop op)
  | Exit ->
    string "exit"
  | UJump ->
    string "ujump"
  | Jump (Label l) ->
    string ("jump " ^ l)
  | ConditionalJump (Label tl, Label tf) ->
    string ("conditional_jump " ^ tl ^ " or " ^ tf)
  | Comment s ->
    string (";; " ^ s)
  | BlockCreate -> string "BlockCreate"
  | BlockGet -> string "BlockGet"
  | BlockSet -> string "BlockSet"


and binop = function
  | Add -> "add"
  | Mul -> "mul"
  | Div -> "div"
  | Sub -> "sub"
  | EQ  -> "eq"
  | GT  -> "gt"
  | LT  -> "lt"
  | GTE -> "gte"
  | LTE -> "lte"

let to_string f x =
  let b = Buffer.create 13 in
  ToBuffer.pretty 0.5 80 b (f x);
  Buffer.contents b
