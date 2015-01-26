open PPrint
open PPrintCombinators
open PPrintEngine

open FopixAST

let ( ++ ) x y =
  x ^^ break 1 ^^ y

let located f x = f (Position.value x)

let rec program p =
  separate_map hardline definition p

and definition = function
  | DefineValue (x, e) ->
    nest 2 (
      group (string "val" ++ located identifier x ++ string "=")
      ++ group (located expression e)
    )

  | DefineFunction (f, xs, e) ->
    nest 2 (
      group (string "def" ++ located function_identifier f
             ++ PPrintOCaml.tuple (List.map identifier xs)
             ++ string "=")
      ++ group (located expression e)
    )

and identifier (Id x) =
  string x

and function_identifier (FunId x) =
  string x

and expression = function
  | Literal l ->
    literal l
  | Variable x ->
    identifier x
  | FunCall (FunId f, es) ->
    funcall f es
  | IfThenElse (c, t, f) ->
    nest 2 (
      group (string "if"
             ++ group (located expression c)
             ++ string "then"
      )
      ++ group (located expression t)
      ++ string "else"
      ++ group (located expression f)
    )
    ++ string "end"
  | Define (x, e1, e2) ->
    nest 2 (
      group (
        group (string "val"
               ++ located identifier x
               ++ string "="
        )
        ++ group (located expression e1)
        ++ string "in"
      )
    )
    ++ group (located expression e2)
    ++ string "end"
  | UnknownFunCall (e, es) ->
    string "?" ++ parens (located expression e)
    ++ PPrintOCaml.tuple (List.map expression' es)

and expression' e = expression (Position.value e)

and funcall f es =
  match f, es with
    | ("=" | "*" | "/" | "+" | "-" | "%" | "<" | ">" | "<=" | ">="), [ lhs; rhs ] ->
      group (parens (expression' lhs ++ string f ++ expression' rhs))
    | _, _ ->
      let ts = PPrintOCaml.tuple (List.map expression' es) in
      string f ++ ts

and literal = function
  | LInt x -> string (string_of_int x)
  | LFun (FunId f) -> string ("&" ^ f)

let to_string f x =
  let b = Buffer.create 13 in
  ToBuffer.pretty 0.5 80 b (f x);
  Buffer.contents b
