open Position
open Error
open HopixAST

(** [error pos msg] reports runtime error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of datix evaluates into a [value]. *)
type 'e gvalue =
  | VInt       of int
  | VBool      of bool
  | VTuple     of 'e gvalue list
  | VRecord    of (label * 'e gvalue) list
  | VTagged    of tag * 'e gvalue list
  | VClosure   of 'e * lambda
  | VPrimitive of ('e gvalue -> 'e gvalue)

type ('a, 'e) coercion = 'e gvalue -> 'a option
let value_as_int      = function VInt x -> Some x | _ -> None
let value_as_bool     = function VBool x -> Some x | _ -> None
let value_as_record   = function VRecord x -> Some x | _ -> None
let value_as_tagged   = function VTagged (t, x) -> Some (t, x) | _ -> None
let value_as_tuple    = function VTuple vs -> Some vs | _ -> None

type ('a, 'e) wrapper = 'a -> 'e gvalue
let int_as_value x  = VInt x
let bool_as_value x = VBool x
let record_as_value x = VRecord x
let tagged_as_value t x = VTagged (t, x)
let tuple_as_value ts = VTuple ts

let primitive ?(error = fun () -> assert false) coercion wrapper f =
  VPrimitive (fun x ->
    match coercion x with
      | None -> error ()
      | Some x -> wrapper (f x)
  )

let print_value v =
  let max_depth = 20 in

  let rec print_value d v =
    if d >= max_depth then "..." else
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
        | VClosure (_, _)
        | VPrimitive _    ->
          "<fun>"

  and print_component d v =
     print_value d v

  and print_field d (Label l, v) =
    l ^ " = " ^ print_value d v

  and tag (Constructor id) =
    id
  in
  print_value 0 v

module Environment : sig
  type t
  val empty : t
  val bind    : t -> identifier -> t gvalue -> t
  val update  : identifier -> t -> t gvalue -> unit
  exception UnboundIdentifier of identifier
  val lookup  : identifier -> t -> t gvalue
  val last    : t -> (identifier * t gvalue * t) option
  val print   : t -> string
end = struct

  type t =
    | EEmpty
    | EBind of identifier * t gvalue ref * t

  let empty = EEmpty

  let bind e x v =
    EBind (x, ref v, e)

  exception UnboundIdentifier of identifier

  let lookup' x =
    let rec aux = function
      | EEmpty -> raise (UnboundIdentifier x)
      | EBind (y, v, e) ->
        if x = y then v else aux e
    in
    aux

  let lookup x e = !(lookup' x e)

  let update x e v =
    lookup' x e := v

  let last = function
    | EBind (x, v, e) -> Some (x, !v, e)
    | EEmpty -> None

  let print_binding (Id x, v) =
    x ^ " = " ^ print_value !v

  let print e =
    let b = Buffer.create 13 in
    let rec aux = function
      | EEmpty -> Buffer.contents b
      | EBind (x, v, e) -> Buffer.add_string b (print_binding (x, v) ^ "\n"); aux e
    in
    aux e

end

type value = Environment.t gvalue

type formals = identifier list

type runtime = {
  environment : Environment.t;
}

type observable = {
  new_environment : Environment.t;
}

(** [primitives] is an environment that contains the implementation
    of all primitives (+, <, ...). *)
let primitives = Environment.empty (* "Student! This is your job!" *)

let initial_runtime () = {
  environment = primitives;
}

(** 640k ought to be enough for anybody -- B.G. *)
let memory : value Memory.t = Memory.create (640 * 1024)

exception MatchFailure

let rec evaluate runtime ast =
  let runtime' = List.fold_left declaration runtime ast in
  (runtime', extract_observable runtime runtime')

and declaration runtime d =
  match Position.value d with
  | DefineValue (pat, e) ->
       failwith "Student! This is your job!"

  | DefineType _ ->
       failwith "Student! This is your job!"

and expression' runtime e =
  expression (position e) runtime (value e)

and expression position runtime = function
  | Fun (x, e) ->
       failwith "Student! This is your job!"

  | Apply (a, b) ->
       failwith "Student! This is your job!"

  | RecFuns fs ->
       failwith "Student! This is your job!"

  | RecordField (e, l) ->
    failwith "Student! This is your job!"

  | Tuple es ->
    failwith "Student! This is your job!"

  | Record rs ->
    failwith "Student! This is your job!"

  | TaggedValues (k, es) ->
    failwith "Student! This is your job!"

  | Case (e, bs) ->
       failwith "Student! This is your job!"

  | Literal l ->
       failwith "Student! This is your job!"

  | Variable x ->
       failwith "Student! This is your job!"

  | Define (pat, ex, e) ->
       failwith "Student! This is your job!"

  | IfThenElse (c, t, f) ->
    failwith "Student! This is your job!"


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
      substract Environment.empty runtime.environment runtime'.environment
  }

let print_observable runtime observation =
  Environment.print observation.new_environment
