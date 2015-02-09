module Source = Hopix
module S = Source.AST
module Target = Datix
module T = Target.AST
open Position

let is_binary_primitive = function
  | "+" | "-" | "*" | "/" | "<" | ">" | "<=" | ">=" | "=" -> true
  | _ -> false

(** A closure compilation environment relates an identifier to the way
    it is accessed in the compiled version of the function's
    body.

    Indeed, consider the following example. Imagine that the following
    function is to be compiled:

    fun x -> x + y

    In that case, the closure compilation environment will
    contain:

    x -> x
    y -> "the code that extract the value of y from the closure environment"

    Indeed, "x" is a local variable that can be accessed directly in
    the compiled version of this function's body whereas "y" is a free
    variable whose value must be retrieved from the closure's
    environment.

*)
type closure_environment = {
  variables  : (S.identifier * S.expression) list;
}

let empty_environment = {
  variables = [];
}

let lookup_environment env x =
  List.assoc x env.variables

let bind env x e = {
  variables = (x, e) :: env.variables
}

let bind_local env x =
  bind env x (S.Variable x)

(** We do not try to produce a well-typed compiled program.
    Therefore, we put a dummy type at every place where a type
    is required.
*)
let tydummy = T.(TyIdentifier (TId "d"))

(** There is no need for a global environment for this
    compilation pass. *)
type environment = ()

let initial_environment _ = ()

(** [fresh_var ?prefix ()] produces a fresh identifier starting
    with prefix. (prefix = "x" is the default value of prefix if
    unspecified.) *)
let fresh_var =
  let c = ref 0 in
  fun ?(prefix="x") () -> incr c; S.Id (prefix ^ string_of_int !c)

let fresh_env_var =
  fresh_var ~prefix:"_env"

let fresh_vars =
  let rec aux accu i =
    if i = 0 then accu else aux (fresh_var () :: accu) (pred i)
  in
  aux []

type application_kind =
  | PrimitiveApplication of HopixAST.identifier * HopixAST.expression located list
  | GeneralApplication of HopixAST.expression located * HopixAST.expression located

(** [classify_application e] determines if the application [e] is
    a primitive application or a general application. *)
let classify_application e =
  match e with
    | S.Apply (e1, e2) ->
      begin  match Position.value e1 with
        | S.Apply (e0, e1') ->
          begin match Position.value e0 with
            | S.Variable (S.Id x) when is_binary_primitive x ->
              PrimitiveApplication (S.Id x, [e1'; e2])
            | _ ->
              GeneralApplication (e1, e2)
          end
        | _ ->
          GeneralApplication (e1, e2)
      end
    | _ ->
      assert false (* By precondition. *)

let locate = Position.with_pos

(** [applys pos f [e1; ...; eN]] builds a chain of applications corresponding
    to [f e1 ... eN]. *)
let applys pos f es =
  let rec aux = S.(function
    | [] ->
      locate pos (Variable f)
    | e :: es ->
      locate pos (Apply (aux es, e)))
  in
  Position.value (aux (List.rev es))

(** Computation of free variables *)

module VariableSet = Set.Make (struct
    type t = S.identifier
    let compare (S.Id s1) (S.Id s2) = String.compare s1 s2
end)

let free_variables : S.expression -> S.identifier list =
  fun e -> failwith "Student! This is your job!"


(** [closure_conversion p] turns a Hopix program [p] that contains
    anonymous functions into a Hopix program [p'] where each anonymous
    function has been changed into a closure, that is a pair
    consisting in an environment and a closed anonymous function. (A
    function is closed if it does not contain any free variables). *)
let closure_conversion : HopixAST.t -> HopixAST.t = HopixAST.(

  let located f x = Position.(map (f (position x)) x) in

  (** [proj pos what idx n] is the code that extracts from [what] the
      component [idx] of a tuple of size [n]. *)
  let proj pos what idx over =
       failwith "Student! This is your job!"
  in


  let rec program p =
    List.map (located definition) p

  and definition pos = function
  | DefineValue (p, e) ->
       failwith "Student! This is your job!"

  | DefineType (tid, tdef) ->
       failwith "Student! This is your job!"

  and expression e =
    expression_aux empty_environment e

  (** [expression_aux env pos e] translates an expression [e]
      into a compiled expression [e]. If [e] is inside the
      body of a function then [env] is not empty and contains
      the compiled code for the identifier occurring in [e]. *)
  and expression_aux env pos = function
  | Literal l ->
       failwith "Student! This is your job!"

  | Variable x ->
       failwith "Student! This is your job!"

  | Define (p, e1, e2) ->
       failwith "Student! This is your job!"

  | Tuple es ->
       failwith "Student! This is your job!"

  | Record rs ->
       failwith "Student! This is your job!"

  | RecordField (e, f) ->
       failwith "Student! This is your job!"

  | TaggedValues (k, es) ->
       failwith "Student! This is your job!"

  | IfThenElse (a, b, c) ->
       failwith "Student! This is your job!"

  | Case (e, bs) ->
       failwith "Student! This is your job!"

  | Apply (e1, e2) as e ->
       failwith "Student! This is your job!"

  | Fun ((x, ty), e) as l ->
       failwith "Student! This is your job!"

  | RecFuns rfs ->
       failwith "Student! This is your job!"
    (**

          rec f0 = fun y1 -> e1 and ... and fN = fun yN -> eN

       is compiled into:

          let e = (dummyf1, ..., dummyfN, x1, .., xM) in
          let f0 = (e, fun env y1 -> C[e0]) in
          ...
          let fN = (e, fun env yN -> C[eN]) in
          e[0] <- f0;
          ...
          e[N] <- fN;
          (f0, ..., fN)

       where :

       - dummyfI are dummy values put temporarily at the location where
         the final closures will be stored ;

       - x1 ... XM are all the free variables of the mutually
         recursive functions (minus the names of the currently
         defined functions).

       - C[.] is a recursive call to the closure conversion function
         (with the appropriate environment).

    *)


  and branch env (Branch (p, e)) =
       failwith "Student! This is your job!"

  and bind_pattern env p =
       failwith "Student! This is your job!"


  in
  program
)

(** [hoist p] returns a Datix program from a closed Hopix program [p].

    It goes through [p] to give a name to every anonymous function.
    These functions are defined at toplevel in the target Datix
    programs.
*)
let hoist : HopixAST.t -> DatixAST.t =
  fun p ->
    let located f x = Position.(map (f (position x)) x) in
    let locate = Position.with_pos in

    (** We store the newly defined functions in a list of declarations. *)
    let function_counter = ref 0 in
    let function_definitions = ref [] in
    let push_new_function pos xs e =
      let fid = incr function_counter; T.FunId ("_f" ^ string_of_int !function_counter) in
      let fdef = T.DefineFunction (locate pos fid, xs, None, e) in
      function_definitions := locate pos fdef :: !function_definitions;
      fid
    in

    let rec program p =
      (** We first translate the definition of the input program... *)
      let pc = List.(flatten (map definition p)) in
      (** ... and we put the newly defined functions in the preamble. *)
      !function_definitions
      @ pc

    and definition e =
      let pos = Position.position e in
      match Position.value e with
      | S.DefineValue (p, e) ->
           failwith "Student! This is your job!"

      | S.DefineType (tid, tdef) ->
           failwith "Student! This is your job!"

    and expression e =
      expression_aux e

  (** [expression_aux pos e] translates an expression [e]
      into a compiled expression [e]. *)
    and expression_aux pos = function
      | S.Literal l ->
          failwith "Student! This is your job!"

      | S.Variable (S.Id x) ->
         failwith "Student! This is your job!"

      | S.Define (p, e1, e2) ->
           failwith "Student! This is your job!"

      | S.Tuple es ->
           failwith "Student! This is your job!"

      | S.Record rs ->
           failwith "Student! This is your job!"

      | S.RecordField (e, S.Label f) ->
          failwith "Student! This is your job!"

      | S.TaggedValues (S.Constructor k, es) ->
          failwith "Student! This is your job!"

      | S.IfThenElse (a, b, c) ->
       failwith "Student! This is your job!"

      | S.Case (e, bs) ->
          failwith "Student! This is your job!"

      | S.Apply (e1, e2) as e ->
          failwith "Student! This is your job!"

      | S.Fun ((env, _), e) ->
           failwith "Student! This is your job!"

      | S.RecFuns rfs ->
           failwith "Student! This is your job!"


  and literal = function
    | S.LInt l ->
      T.LInt l

  and branch (S.Branch (p, e)) =
       failwith "Student! This is your job!"

  and pattern pos p =
       failwith "Student! This is your job!"

  and identifier (S.Id x) = T.Id x

  in
  program p

let translate p env =
  let closed_p = closure_conversion p in
  (** To see the result of closure conversion:
  print_endline ("CC: " ^ Hopix.print_ast closed_p ^ "\n");
  flush stdout;
  *)
  (hoist closed_p, ())
