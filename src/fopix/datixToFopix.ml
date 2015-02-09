(** This module implements a compiler from Datix to Fopix. *)

let error pos msg =
  Error.error "compilation" pos msg

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)
module Source = Datix
module S = Source.AST
module Target = Fopix
module T = Target.AST

type environment = {
  tag_representation   : (S.tag * int) list;
  label_representation : (S.label * int) list;
}

let initial_environment () = {
  tag_representation = [];
  label_representation = [];
}

let bind_tag_representation env m =
  { env with tag_representation = m :: env.tag_representation }

let bind_label_representation env m =
  { env with label_representation = m :: env.label_representation }

let lookup_label_representation env l =
  List.assoc l env.label_representation

let lookup_tag_representation env t =
  List.assoc t env.tag_representation

let fresh_identifier =
  let r = ref 0 in
  fun () -> incr r; T.Id ("_" ^ string_of_int !r)

(** [translate p env] turns a Datix program [p] into a Fopix program
    using [env] to retrieve contextual information. *)
let translate (p : S.t) env =

  (** Compilation is done in two steps:

      1. Choose a low-level representation for data and store this
      choice in env.

      2. Use this environment to translate Datix high-level data into
      Fopix blocks.
  *)
  let rec program env p =
    let env = choose_data_representation env p in
    let defs = List.(flatten (map (definition' env) p)) in
    (defs, env)

  and definition' env d =
    definition env (Position.value d)

  and definition env =  function    
  |  S.DefineValue (pat, e) ->   (* begin     end *****)
  (* fopix defineValues (x , e ) 
  val x = e 
  val  a  = fst x 
  val b = snd x 
  toplevel_pattern x pat 
  define( pat , e1 , e2 ) ->
  val put = e1 in e2 end 
  case ( e , branch)
    

  top level pattern *)
    failwith "Student! This is your job!"

    | S.DefineFunction (f, xs, _, e) ->
         failwith "Student! This is your job!"

    | S.DefineType (t, tdef) ->
      []


  and expression pos env e =
    let locate = Position.with_pos pos in
    match e with
      | S.Literal l ->
           failwith "Student! This is your job!"

      | S.Variable x ->
           failwith "Student! This is your job!"

      | S.Define (pat, e1, e2) ->
           failwith "Student! This is your job!"

      | S.FunCall (f, es) ->
           failwith "Student! This is your job!"

      | S.IfThenElse (c, et, ef) ->
           failwith "Student! This is your job!"

      | S.Tuple es ->
           failwith "Student! This is your job!"

      | S.Record rs ->
           failwith "Student! This is your job!"

      | S.RecordField (e, l) ->
           failwith "Student! This is your job!"

      | S.TaggedValues (k, es) ->
           failwith "Student! This is your job!"

      | S.Case (e, bs) ->
           failwith "Student! This is your job!"


  and expression' env e =
    Position.map (expression (Position.position e) env) e

  and branches env x = function
    | [] ->
         failwith "Student! This is your job!"

    | S.Branch (pat, e) :: bs ->
         failwith "Student! This is your job!"

  and toplevel_pattern pos env x p =
    match p with
    | S.PWildcard ->
         failwith "Student! This is your job!"

    | S.PVariable y ->
         failwith "Student! This is your job!"

    | S.PTuple ys ->
         failwith "Student! This is your job!"

    | S.PTaggedValues (k, ys) ->
         failwith "Student! This is your job!"


  and pattern pos env x pat e =
    match pat with
      | S.PWildcard ->
           failwith "Student! This is your job!"

      | S.PVariable y ->
           failwith "Student! This is your job!"

      | S.PTuple ys ->
           failwith "Student! This is your job!"

      | S.PTaggedValues (k, ys) ->
           failwith "Student! This is your job!"

  and pattern' env x pat e =
    pattern (Position.position pat) env x (Position.value pat) e

  and literal = function
    | S.LInt x -> T.LInt x

  and identifier (S.Id x) =
    T.Id x

  and function_identifier (S.FunId x) =
    T.FunId x

  and function_identifier' x =
    Position.map function_identifier x

  and formals xs =
    List.(map identifier (fst (split xs)))

  and choose_data_representation env defs =
       failwith "Student! This is your job!"

  in
  program env p

