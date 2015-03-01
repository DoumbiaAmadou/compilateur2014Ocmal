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
  | VFun of function_identifier

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
      | VFun (FunId f)  ->
        f
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
     begin
       match (expression' runtime e) with 
       |VRecord(lv_list) -> List.assoc l lv_list
       |_ -> failwith "this expression is not a VRecord"
     end

  | Tuple es -> 
     begin
       match es with
       |[]-> tuple_as_value []
       |h::tail -> tuple_as_value (List.map (expression' runtime) es)
     end

  | Record rs ->
     begin
       match rs with
       |[] -> record_as_value []
       |(l,e)::tail -> let (label_list,expr_list) = List.split rs in
		       let value_list = (List.map (expression' runtime) expr_list) in
		       record_as_value (List.combine label_list value_list)
     end

  | TaggedValues (k, es) -> tagged_as_value k (List.map (expression' runtime) es)

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
     begin
       match value_as_bool (expression' runtime c) with
       |Some true -> expression' runtime t
       |Some false-> expression' runtime f
       |_ -> assert false
     end

and binop runtime s e1 e2 =
  let v1 = expression' runtime e1 in
  let v2 = expression' runtime e2 in
  match evaluation_of_binary_symbol s v1 v2 with
  | Some v -> v
  | None -> error [position e1; position e2] "Invalid binary operation."

and branches runtime v = function
  | [] -> failwith "error! branches are not exhaustive"

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

and bind_variable runtime x v =
  { environment = Environment.bind runtime.environment x v }

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
