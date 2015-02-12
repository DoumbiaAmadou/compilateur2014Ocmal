open PPrint
open PPrintCombinators
open PPrintEngine

open HopixAST

let int i = string (string_of_int i)

let ( ++ ) x y = x ^^ break 1 ^^ y

let located f x = f (Position.value x)

let rec program p =
  separate_map hardline definition' p

and definition = function
  | DefineValue (x, e) ->
    nest 2 (
      group (string "val" ++ pattern' x ++ string "=")
      ++ group (located expression e)
    )

  | DefineType (tid, _, tdef) ->
    nest 2 (
      group (string "type" ++ type_identifier tid ++ string "=")
      ++ group (type_definition tdef)
    )

and definition' d = definition (Position.value d)

and pattern = function
  | PVariable x -> identifier x
  | PWildcard -> string "_"
  | PTuple ps -> PPrintOCaml.tuple (List.map identifier ps)
  | PTaggedValues (t, ps) -> tag t ++ PPrintOCaml.tuple (List.map identifier ps)

and pattern' p = pattern (Position.value p)

and tag = function
  | Constructor k -> string k

and type_identifier (TId x) =
  string x

and type_definition = function
  | RecordTy ls ->
    string "{" ++ separate_map (string "; ") fieldty ls ++ string "}"

  | TaggedUnionTy ks ->
    separate_map (string "| ") tag_declaration ks

  | DefTy ty -> typ ty

and tag_declaration (t, tys) =
  tag t ++ PPrintOCaml.tuple (List.map typ tys)

and fieldty (l, ty) =
  label l ++ string ":" ++ typ ty

and label (Label x) =
  string x

and type_annotation ty =
  string ":" ++ typ ty

and binding (x, ty) =
  identifier x ++ string ":" ++ typ ty

and typ = function
  | TyBase (x,l) ->
    type_identifier x (* TODO : print l *)
  | TyTuple ts ->
    parens (separate_map (string " * ") typ ts)
  | TyArrow (ity, oty) ->
    parens_at_left_arrow ity (typ ity) ++ string "->" ++ typ oty

and parens_at_left_arrow = function
  | TyTuple _ | TyArrow _ -> parens
  | _ -> fun x -> x

and identifier (Id x) =
  string x

and typed_identifier (x, ty) =
  match ty with
    | Some ty ->
      parens (identifier x ++ type_annotation ty)
    | None ->
      identifier x

and function_identifier (Id x) =
  string x

and expression = function
  | RecordField (e, l) ->
    parens (expression' e) ++ string "." ++ label l

  | Record fs ->
    nest 2 (
      string "{"
      ++ separate_map (string "; ") field fs
      ++ string "}"
    )

  | Literal l ->
    literal l

  | Variable x ->
    identifier x

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
      group (string "val"
             ++ pattern' x
             ++ string "="
      )
      ++ group (located expression e1)
    )
    ++ string "in"
    ++ group (located expression e2)
    ++ string "end"

  | Tuple es ->
    PPrintOCaml.tuple (List.map expression' es)

  | TaggedValues (t, es) ->
    tag t ++ PPrintOCaml.tuple (List.map expression' es)

  | Case (e, bs) ->
    nest 2 (
      group (string "case" ++ expression' e ++ string "with")
      ++ separate_map (break 0) branch bs
    )
    ++ string "end"

  | Apply (a, b) ->
    parens_at_left_of_application a (expression' a)
    ++ parens_at_right_of_application b (expression' b)

  | Fun (x, e) ->
    nest 2 (group (
      group (string "{" ++ typed_identifier x ++ string "->")
      ++ expression' e ++ string "}")
    )

  | RecFuns fs ->
    string "fix"
    ++ separate_map (break 1 ++ string "and" ^^ break 1) recfun fs
    ++ string "end"


and recfun (fty, e) =
  group (typed_identifier (Position.value fty) ++ string "=" ++ expression' e)

and parens_at_left_of_application e =
  match Position.value e with
  | Apply _ | Variable _ | Literal _ -> fun x -> x
  | _ -> parens

and parens_at_right_of_application e =
  match Position.value e with
  | Variable _ | Literal _ -> fun x -> x
  | _ -> parens

and field (l, e) =
  group (label l ++ string "=" ++ expression' e)

and branch (Branch (p, e)) =
  group (string "|" ++ pattern' p ++ string "->" ++ nest 2 (expression' e))

and expression' e = group (expression (Position.value e))

and funcall f es =
  match f, es with
    | ("*" | "/" | "+" | "-" | "%"), [ lhs; rhs ] ->
      group (parens (expression' lhs ++ string f ++ expression' rhs))
    | _, _ ->
      let ts = PPrintOCaml.tuple (List.map expression' es) in
      string f ++ ts

and literal = function
  | LInt x -> string (string_of_int x)

let to_string f x =
  let b = Buffer.create 13 in
  ToBuffer.pretty 0.5 80 b (f x);
  Buffer.contents b
