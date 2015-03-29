open Position
open Error
open FopixAST

(** [error pos msg] reports runtime error messages. *)
let error positions msg =
  errorN "execution" positions msg

(** Every expression of fopi evaluates into a [value]. *)
type value =
  | VUnit
  | VInt      of int
  | VBool     of bool
  | VLocation of Memory.location

let print_value = function
  | VInt x      -> string_of_int x
  | VBool true  -> "true"
  | VBool false -> "false"
  | VUnit       -> "()"
  | VLocation l -> Memory.print_location l

type 'a coercion = value -> 'a option
let value_as_int      = function VInt x -> Some x | _ -> None
let value_as_bool     = function VBool x -> Some x | _ -> None
let value_as_location = function VLocation x -> Some x | _ -> None
let value_as_unit     = function VUnit -> Some () | _ -> None

type 'a wrapper = 'a -> value
let int_as_value x  = VInt x
let bool_as_value x = VBool x
let location_as_value x = VLocation x
let unit_as_value () = VUnit

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
    (* Identifiers starting with '_' are reserved for the compiler.
       Their values must not be observable by users. *)
    if x.[0] = '_' then
      ""
    else
      x ^ " = " ^ print_value v

  let print env =
    String.concat "\n" (
      List.(filter (fun s -> s <> "") (map print_binding env))
    )

end

type func= {
  arglist : formals; (* The parameter(s) of the function *)  
  expression: expression located; (* The body of the function *)
}

type runtime = {
  environment : Environment.t;
   funcs    : (function_identifier * func) list
}

type observable = {
  new_environment : Environment.t;
}

let initial_runtime () = {
  environment = Environment.initial;
  funcs = []
}

(** 640k ought to be enough for anybody -- B.G. *)
let memory : value Memory.t = Memory.create (640 * 1024)

let rec evaluate runtime ast =
  let runtime' = List.fold_left declaration runtime ast in
  (runtime', extract_observable runtime runtime')


and declaration runtime = function
  | DefineValue (i, e) ->
    let v = expression' runtime e in
    let i = Position.value i in
    { environment = Environment.bind runtime.environment i v ; 
     funcs = runtime.funcs
    }

  | DefineFunction (f , formals,e)-> 
    let funname = Position.value f in 
    let myfunc = (funname, {arglist=formals; expression =e} ) in  
    { environment = runtime.environment ; 
     funcs = myfunc :: runtime.funcs
    }  
    
  

and expression' runtime e =
  expression (position e) runtime (value e)

and expression position runtime = function
  | Literal l ->
    literal l

  | Variable x ->
    Environment.lookup x runtime.environment

  | IfThenElse (c, t, f) -> begin 
			    match value_as_bool  (expression' runtime c)  with 
			    |Some true -> expression' runtime t
			    |Some false  -> expression' runtime f 		
			    |None -> error [position]  ("Expression :"^(FopixPrettyPrinter.to_string FopixPrettyPrinter.expression' c )^" is not a Bool expression ")
			  end 
  | Define (x, ex, e) ->
    let v = expression' runtime ex in
    let runtime ={  runtime with environment = Environment.bind runtime.environment (Position.value x) v }
    in
    expression' runtime e

  | FunCall (FunId "block_create", [size; init]) ->
    let vs = expression' runtime size in
    begin
      match vs with
      | VInt size_int -> VLocation (Memory.allocate memory size_int (expression' runtime init))
      | _ -> assert false
    end
(**    failwith "Student! This is your job!" **)

  | FunCall (FunId "block_get", [location; index]) ->
  begin
  match expression' runtime location, expression' runtime index with
    | VLocation p, VInt i -> Memory.read (Memory.dereference memory p) i
    | _ -> assert false
    (**    failwith "Student! This is your job!" **)
  end

  | FunCall (FunId "block_set", [location; index; e]) ->
  begin
    match expression' runtime location, expression' runtime index with
      | VLocation p, VInt i -> Memory.write (Memory.dereference memory p) i (expression' runtime e); VUnit
      | _ -> assert false
    (**    failwith "Student! This is your job!" **)
  end

  | FunCall (FunId s, [e1; e2]) when is_binary_primitive s ->
     binop runtime s e1 e2

  | FunCall (fun_id,exp_list) ->

     let fct = List.assoc fun_id runtime.funcs
     in
     let new_env = List.fold_left2 (fun env param e ->
				    Environment.bind 
				      env
				      param
				      (expression' {runtime with environment = env} e)
				   )
				   runtime.environment
				   fct.arglist
				   exp_list
     in
     expression' {runtime with environment = new_env} fct.expression
     

and binop runtime s e1 e2 =
  let v1 = expression' runtime e1 in
  let v2 = expression' runtime e2 in
  match evaluation_of_binary_symbol s v1 v2 with
  | Some v -> v
  | None -> error [position e1; position e2] "Invalid binary operation."

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
