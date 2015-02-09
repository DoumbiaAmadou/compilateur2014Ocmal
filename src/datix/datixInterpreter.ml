open Position
open Error
open DatixAST

(** [error pos msg] reports runtime error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of datix evaluates into a [value]. *)
type value =
  | VInt      of int
  | VBool     of bool
  | VTuple     of value list
  | VRecord   of (label * value) list
  | VTagged   of tag * value list

let print_value v_root =
  let marks = ref [] in
  let mark v = marks := v :: !marks in
  let seen v = List.memq v !marks in
  let max_depth = 20 in
  let rec print_value d v =
    if seen v || d > max_depth then "..." else (
      mark v;
      match v with
      | VInt x          ->
        string_of_int x
      | VBool true      ->
        "true"
      | VBool false     ->
        "false"
      | VTuple vs       ->
        "(" ^ String.concat ", " (List.map (print_component (d + 1)) vs) ^ ")"
      | VRecord r       ->
        "{" ^ String.concat "; " (List.map (print_field (d + 1)) r) ^ "}"
      | VTagged (t, vs) ->
        tag t ^ "(" ^ String.concat ", " (List.map (print_value (d + 1)) vs) ^ ")"
    )
  and print_component d v = print_value d v
  and print_field d (Label l, v) = l ^ " = " ^ print_value d v
  and tag (Constructor id) = id
  in
  print_value 0 v_root

type 'a coercion = value -> 'a option
let value_as_int      = function VInt x -> Some x | _ -> None
let value_as_bool     = function VBool x -> Some x | _ -> None
let value_as_record   = function VRecord x -> Some x | _ -> None
let value_as_tagged   = function VTagged (t, x) -> Some (t, x) | _ -> None
let value_as_tuple    = function VTuple vs -> Some vs | _ -> None

type 'a wrapper = 'a -> value
let int_as_value x  = VInt x
let bool_as_value x = VBool x
let record_as_value x = VRecord x
let tagged_as_value t x = VTagged (t, x)
let tuple_as_value ts = VTuple ts

(** Binary operators *)

let lift_binop coerce wrap op v1 v2 =
  match coerce v1, coerce v2 with
  | Some li, Some ri -> Some (wrap (op li ri))
  | _, _ -> None

let lift_arith_op op = lift_binop value_as_int int_as_value op
let lift_cmp_op op = lift_binop value_as_int bool_as_value op

let arith_op_of_symbol = function
  | "+" -> ( + )
  | "-" -> ( - )
  | "/" -> ( / )
  | "*" -> ( * )
  | _ -> assert false

let cmp_op_of_symbol = function
  | "<" -> ( < )
  | ">" -> ( > )
  | "<=" -> ( <= )
  | ">=" -> ( >= )
  | "=" -> ( = )
  | _ -> assert false

let evaluation_of_binary_symbol = function
  | ("+" | "-" | "*" | "/") as s -> lift_arith_op (arith_op_of_symbol s)
  | ("<" | ">" | "<=" | ">=" | "=") as s -> lift_cmp_op (cmp_op_of_symbol s)
  | _ -> assert false

let is_binary_primitive = function
  | "+" | "-" | "*" | "/" | "<" | ">" | "<=" | ">=" | "=" -> true
  | _ -> false

(** Execution environment *)

module Environment : sig
  type t
  val initial : t
  val bind    : t -> identifier -> value -> t
  exception UnboundIdentifier of identifier
  val lookup  : identifier -> t -> value
  val last    : t -> (identifier * value * t) option
  val print   : t -> string
end = struct
  type t = (identifier * value) list

  let initial = []

  let bind e x v = (x, v) :: e

  exception UnboundIdentifier of identifier

  let lookup x e =
    try
      List.assoc x e
    with Not_found ->
      raise (UnboundIdentifier x)

  let last = function
    | [] -> None
    | (x, v) :: e -> Some (x, v, e)

  let print_binding (Id x, v) =
    x ^ " = " ^ print_value v

  let print env =
    String.concat "\n" (List.map print_binding env)

end

type formals = identifier list

type runtime = {
  environment : Environment.t;
}

type observable = {
  new_environment : Environment.t;
}

let initial_runtime () = {
  environment = Environment.initial;
}

(** 640k ought to be enough for anybody -- B.G. *)
let memory : value Memory.t = Memory.create (640 * 1024)


let rec evaluate runtime ast =
  let runtime' = List.fold_left declaration runtime ast in
  (runtime', extract_observable runtime runtime')

and declaration runtime d =
  match Position.value d with
  | DefineValue (pat, e) ->
    bind_pattern runtime pat (expression' runtime e)

  | DefineFunction _ | DefineType _ ->
    runtime

and expression' runtime e =
  expression (position e) runtime (value e)

and expression position runtime = function
  | RecordField (e, l) ->
    failwith "Student! This is your job!"

  | Tuple es ->
    failwith "Student! This is your job!"

  | Record rs ->
    failwith "Student! This is your job!"

  | TaggedValues (k, es) ->
    failwith "Student! This is your job!"

  | Case (e, bs) ->
    branches runtime (expression' runtime e) bs

  | Literal l ->
    literal l

  | Variable x ->
    Environment.lookup x runtime.environment

  | Define (pat, ex, e) ->
    let v = expression' runtime ex in
    expression' (bind_pattern runtime pat v) e

  | FunCall (FunId s, [e1; e2]) when is_binary_primitive s ->
    binop runtime s e1 e2

  | IfThenElse (c, t, f) ->
    failwith "Student! This is your job!"

and binop runtime s e1 e2 =
  let v1 = expression' runtime e1 in
  let v2 = expression' runtime e2 in
  match evaluation_of_binary_symbol s v1 v2 with
  | Some v -> v
  | None -> error [position e1; position e2] "Invalid binary operation."

and branches runtime v = function
  | [] ->
    failwith "Student! This is your job!"

  | Branch (pat, e) :: bs ->
    failwith "Student! This is your job!"

and bind_variable runtime x v =
  { environment = Environment.bind runtime.environment x v }

and bind_pattern runtime pat v : runtime =
  match Position.value pat, v with
    | PWildcard, _ ->
      failwith "Student! This is your job!"

    | PVariable x, _ ->
      failwith "Student! This is your job!"

    | PTuple xs, VTuple vs ->
      failwith "Student! This is your job!"

    | PTaggedValues (k, xs), VTagged (k', vs) ->
      failwith "Student! This is your job!"

    | _, _ ->
      assert false (* By typing. *)

and literal = function
  | LInt x -> VInt x

and extract_observable runtime runtime' =
  let rec substract new_environment env env' =
    if env == env' then new_environment
    else
      match Environment.last env' with
        | None -> assert false (* Absurd. *)
        | Some (x, v, env') ->
          let new_environment = Environment.bind new_environment x v in
          substract new_environment env env'
  in
  {
    new_environment =
      substract Environment.initial runtime.environment runtime'.environment
  }

let print_observable runtime observation =
  Environment.print observation.new_environment
