(** This module implements the interpreter of the Stackix programming
    language. *)

open Error
open StackixAST

let error msg =
  global_error "stackix execution" msg

(**

   The Stackix programming language is a low-level programming language
   for a stack machine composed of two stacks.

   The first stack contains intermediate values (see {!data}).

   The second stack contains the values of variables.

   A program for the Stackix machine is a linear sequence of labelled
   instructions (see {!StackixAST.t}). Therefore, the machine must:

   (i) decode and execute the instruction in the right order ;
       (see {!execute_instruction})

   (ii) be able to relate each label with an instruction.
       (see {!load})

*)


(** ----------------------- *)
(** {1 Runtime definition } *)
(** ----------------------- *)

(** The following module implements a data structure for imperative
    stacks. *)
module Stack : sig
  type 'a t
  exception EmptyStack
  exception UnboundStackElement of int
  exception CannotSwap

  (** [create ()] returns a fresh stack. *)
  val create : unit -> 'a t

  (** [push x s] modifies [s] by putting [x] on top of
      its elements. *)
  val push : 'a -> 'a t -> unit

  (** [pop s] modifies [s] by removing the element at
      the top of it.
      Raise [EmptyStack] if there is no such element. *)
  val pop  : 'a t -> unit

  (** [get i s] returns the i-th element of [s], counting
      from the top, i.e. 0 is top.
      Raise [UnboundStackElement i] is there is no such
      element. *)
  val get : int -> 'a t -> 'a

  (** [sub k s] returns a fresh stack holding the first [k]
      elements of [s]. (Again, counting from the top of [s].)
      [s] is not modified by this operation. *)
  val sub : int -> 'a t -> 'a t

  (** [swap s] exchanges the first two elements of [s].
      Raise [CannotSwap] if there are no such elements in [s]. *)
  val swap : 'a t -> unit

  (** [depth s] returns the number of elements of [s]. *)
  val depth : 'a t -> int

  (** [print f s] returns a human-readable representation of [s]
      using [f] as a printer for the elements of [s]. *)
  val print : ('a -> string) -> 'a t -> string
end = struct

  (* The following implementation is VERY naive.
     Bonus: Can you optimize it? *)
  type 'a t = 'a list ref

  let create () = ref []

  let depth s = List.length !s

  let push x l =
    l := (x :: !l)

  exception EmptyStack
  exception UnboundStackElement of int
  exception CannotSwap

  let swap l = match !l with
    | [] | [_] -> raise CannotSwap
    | x :: y :: xs -> l := y :: x :: xs

  let pop l = match !l with
    | [] ->
      raise EmptyStack
    | _ :: xs ->
      l := xs

  let get k l =
    let rec aux i = function
      | [] -> raise (UnboundStackElement k)
      | x :: _ when i = 0 -> x
      | _ :: xs -> aux (pred i) xs
    in
    aux k !l

  let sub k s =
    let rec aux i s =
      if i = 0 then [] else
        match s with
          | [] -> raise (UnboundStackElement i)
          | x :: xs -> x :: (aux (pred i) xs)
    in
    ref (aux k (!s))

  let print printer s =
    String.concat "\n" (
      List.(rev (filter (fun s -> s <> "") (map printer !s)))
    )

end

(** This exception is raised to stop the machine. *)
exception ExitNow

(** *)
type data =
  | DUnit
  | DInt   of int
  | DBool  of bool
  | DLabel of label
  | DLocation of Memory.location

let print_data = function
  | DUnit -> "()"
  | DInt x -> string_of_int x
  | DBool true -> "true"
  | DBool false -> "false"
  | DLabel (Label l) -> "@" ^ l
  | DLocation l -> Memory.print_location l

let type_of = function
  | DUnit -> "unit"
  | DInt _ -> "int"
  | DBool _ -> "bool"
  | DLabel _ -> "label"
  | DLocation _ -> "location"

let coercion_error expectation v =
  error ("Expecting " ^ expectation ^ " get " ^ type_of v)

let as_unit = function DUnit -> () | v -> coercion_error "unit" v
let as_int  = function DInt x -> x   | v -> coercion_error "int" v
let as_bool = function DBool x -> x  | v -> coercion_error "bool" v
let as_lbl  = function DLabel x -> x | v -> coercion_error "label" v
let as_loc  = function DLocation x -> x | v -> coercion_error "location" v

let from_unit ()    = DUnit
let from_int x      = DInt x
let from_lbl x      = DLabel x
let from_bool x     = DBool x
let from_location x = DLocation x

type runtime = {
  values    : data Stack.t;
  variables : (identifier * data) Stack.t;
  memory    : data Memory.t;
}

type observable = {
  new_variables : (identifier * data) Stack.t
}

let initial_runtime () = {
  values    = Stack.create ();
  variables = Stack.create ();
  memory    = Memory.create (640 * 1024)
}

let show_runtime runtime =
  Printf.printf "=== Values ===\n%s\n=== Variables ===\n%s\n"
    (Stack.print print_data runtime.values)
    (Stack.print (fun (Id x, d) -> x ^ " = " ^ print_data d) runtime.variables)

(** -------------------------- *)
(** {1 Instruction execution } *)
(** -------------------------- *)

let evaluate runtime (ast : t) =

  (** Shortcuts to the runtime components. *)
  let variables = runtime.variables in
  let values    = runtime.values    in
  let memory    = runtime.memory    in

  (** We store the initial number of variables. This will
      be used at the end to compute the number of new
      variables that were introduced by this evaluation. *)
  let initial_variable_number = Stack.depth variables in

  (** We now store the entry points of basic blocks. *)
  let blocks : (label, instruction list) Hashtbl.t = Hashtbl.create 13 in

  (** The program entry point will be the first label that we cross. *)
  let entry = ref None in

  (** The following function goes through the program and stores
      the entry points of each basic block. (Remember that a basic block
      is a sequence of instructions, starting with a label and ended by a
      jump to a label. (This jump can unconditional or conditional). *)
  let rec load cl cblocks = function
    | [] ->
      Hashtbl.add blocks cl (List.rev cblocks)
    | (None, i) :: is ->
      load cl (Position.value i :: cblocks) is
    | (Some l, i) :: is ->
      if !entry = None then
        entry := Some l
      else
        Hashtbl.add blocks cl (List.rev cblocks);
      load l [Position.value i] is
  in
  load (Label "") [] ast;

  (** [execute_block b] goes through the instructions of [b] and
      execute each of them. *)
  let rec execute_block = function
    | [] ->
      ()
    | [i] ->
      execute_instruction i
    | i :: is ->
      execute_instruction i;
      execute_block is

  (** [execute_instruction implements the semantics of the
      machine instructions. *)
  and execute_instruction i =
    match i with
      | Define x ->
        Stack.(push (x, get 0 values) variables);
        Stack.pop values

      | Undefine ->
        Stack.pop variables

      | GetVariable i ->
        Stack.(push (snd (get i variables)) values)

      | Remember k ->
        Stack.push (DInt k) values

      | RememberLabel l ->
        Stack.push (DLabel l) values

      | Swap ->
        Stack.swap values

      | Binop op ->
        let x = Stack.get 0 values
        and y = Stack.get 1 values
        in
        Stack.pop values;
        Stack.pop values;
        Stack.push (binop op x y) values

      | Exit ->
        raise ExitNow

      | Jump l ->
        jump l

      | UJump ->
        let l = as_lbl (Stack.get 0 values) in
        Stack.pop values;
        jump l

      | ConditionalJump (tl, fl) ->
        let b = Stack.get 0 values in
        Stack.pop values;
        if as_bool b then jump tl else jump fl

      | Comment _ ->
        ()

      | BlockCreate -> failwith "Student! This is your job!"
      | BlockSet -> failwith "Student! This is your job!"
      | BlockGet -> failwith "Student! This is your job!"

  and jump (Label x as l) =
    let block =
      try
        Hashtbl.find blocks l
      with Not_found -> error ("Unbound label " ^ x)
    in
    execute_block block

  and binop = function
    | Add -> arith_binop ( + )
    | Mul -> arith_binop ( * )
    | Div -> arith_binop ( / )
    | Sub -> arith_binop ( - )
    | EQ  -> cmp_binop (  =  )
    | GT  -> cmp_binop (  >  )
    | GTE -> cmp_binop (  >= )
    | LT  -> cmp_binop (  <  )
    | LTE -> cmp_binop (  <= )

  and arith_binop op = fun x y -> from_int (op (as_int x) (as_int y))

  and cmp_binop op = fun x y -> from_bool (op (as_int x) (as_int y))

  (** To run the program on the machine, we just execute the block
      of the program entry point. *)
  and run () =
    match !entry with
      | None -> ()
      | Some l -> jump l
  in
  begin try
          run ();
    with ExitNow -> ();
  end;

  (** Finally we extract the new variables from the variables stack. *)
  let new_variable_number =
    Stack.depth runtime.variables - initial_variable_number
  in
  let observable =
    { new_variables = Stack.sub new_variable_number runtime.variables }
  in
  (runtime, observable)

let print_observable runtime obs =
  Stack.print (fun (Id x, v) ->
    (* Identifier starting with '_' are reserved by the compiler.
       So their values are hidden to the user. *)
    if x.[0] = '_' then
      ""
    else
      x ^ " = " ^ print_data v
  ) obs.new_variables
