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
    bind_pattern runtime pat (expression' runtime e)
      (* failwith "Student! This is your job!" *)

  | DefineType _ -> runtime
      (* failwith "Student! This is your job!" *)

and expression' runtime e =
  expression (position e) runtime (value e)

and expression position runtime = function
  | Fun (x, e) -> 
       failwith "Student! This is your job!" 

  | Apply (a, b) -> 
    let v = (expression' runtime b) in
    begin
      match (expression' runtime a) with
      | VClosure (env, lambda) -> 
        begin
         match lambda with
          |(x, body) -> assert false (* List.combine (x, v)::env body *)
          | _ -> assert false
        end
      | VPrimitive f -> f v 
      | _ -> assert false
    end 
    (* failwith "Student! This is your job!" *)

  | RecFuns fs -> 
  begin
    match fs with
    |[] -> tuple_as_value []
    |(id, body)::tail-> assert false (* il faut rajouter *)
  end 
  (*  failwith "Student! This is your job!" *)
  | RecordField (e, l) ->
    begin
       match (expression' runtime e) with 
       |VRecord(lv_list) -> List.assoc l lv_list
       |_ -> failwith "this expression is not a VRecord"
    end
  (*  failwith "Student! This is your job!" *)

  | Tuple es ->
   begin
    match es with
    | [] -> tuple_as_value []
    | h::tail -> tuple_as_value (List.map (expression' runtime) es)
  end 

  | Record rs ->
  begin
       match rs with
       |[] -> record_as_value []
       |(l,e)::tail -> let (label_list,expr_list) = List.split rs in
           let value_list = (List.map (expression' runtime) expr_list) in
           record_as_value (List.combine label_list value_list) 
  end
   (* failwith "Student! This is your job!" *)

  | TaggedValues (k, es) ->
    tagged_as_value k (List.map (expression' runtime) es) 
  (*  failwith "Student! This is your job!" *)

  | Case (e, bs) ->
    branches runtime (expression' runtime e) bs
     (*  failwith "Student! This is your job!" *)

  | Literal l -> literal l
(*  failwith "Student! This is your job!" *)

  | Variable x ->
       Environment.lookup x runtime.environment 
(*  failwith "Student! This is your job!" *)

  | Define (pat, ex, e) ->
  let v = expression' runtime ex in
    expression' (bind_pattern runtime pat v) e
(*  failwith "Student! This is your job!" *)

  | IfThenElse (c, t, f) ->  
  begin
    match value_as_bool (expression' runtime c) with
      | Some true -> expression' runtime t
      | Some false  -> expression' runtime f
      | None -> assert false
  end 
(*  failwith "Student! This is your job!" *)

and branches runtime v = function
  | [] ->
    failwith "error! branches are not exhaustive"

  | Branch (pat, e) :: bs ->
    begin
       match (value pat), v with
       |PWildcard,_ -> expression' runtime e
       |PVariable(id),_ -> expression' (bind_pattern runtime pat v) e
       |PTuple(id_list),VTuple(val_list) -> 
   if ((List.length id_list) = (List.length val_list)) then 
     expression' (bind_pattern runtime pat v) e
   else
     failwith "error: this tuple doesn't match this kind of pattern"
       
       |PTaggedValues(tag,id_list), VTagged (tag',val_list) when tag = tag' -> 
   if ((List.length id_list) = (List.length val_list)) then 
     expression' (bind_pattern runtime pat v) e
   else
     failwith "error: this tag is not associated with this kind of pattern"

       |_ -> branches runtime v bs
     end
(*  failwith "Student! This is your job!" *)

and bind_variable runtime x v =
  { environment = Environment.bind runtime.environment x v }
  (*  failwith "Student! This is your job!" *)

and bind_pattern runtime pat v : runtime =
  match Position.value pat, v with
    | PWildcard, _ -> runtime

    | PVariable x, _ -> bind_variable runtime x v

    | PTuple xs, VTuple vs ->
      if ((List.length xs) = (List.length vs)) then 
        let new_runtime = runtime in
        (List.map2 
          (fun id v -> new_runtime = (bind_variable new_runtime id v))
          xs
          vs
        );
        new_runtime
      else
        failwith "error! cannot match Tuple pattern (not the same length)"
        (*  failwith "Student! This is your job!" *)

    | PTaggedValues (k, xs), VTagged (k', vs) when k = k' ->
      if ((List.length xs) = (List.length vs)) then        
        let new_runtime = runtime in
        (List.map2 
          (fun id v -> new_runtime = (bind_variable new_runtime id v))
          xs
          vs
        );
        new_runtime
      else
        failwith "error! cannot match TaggedValue pattern (not the same length)"
        (*  failwith "Student! This is your job!" *)

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
