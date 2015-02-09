(** This module implements a type checker for Datix. *)

open DatixAST

(** Type checker error message producer. *)
let error = Error.error "during type checking"

(** Basic types. *)
let tyint  = TyIdentifier (TId "int")
let tybool = TyIdentifier (TId "bool")

(** A well-typed function has a signature. *)
type signature = Signature of typ list * typ

(** During typechecking, we thread an environment that contains
    the type of variables, the signature of functions and the
    type definitions. *)
module TypingEnvironment : sig
  (** The type of typing environment. *)
  type t

  (** The empty environment. *)
  val empty : t

  (** [bind env x ty] returns an environment that assigns [ty]
      the variable [x] and extends [env]. *)
  val bind
    : t -> identifier -> typ -> t

  (** [UnboundIdentifier x] is raised if [x] is unbound. *)
  exception UnboundIdentifier of identifier

  (** [lookup env x] returns the type assigned to [x] in [env].
      Raise {!UnboundIdentifier x} if no such variable exists. *)
  val lookup
    : t -> identifier -> typ

  (** [bind_function env f s] assigns the signature [s] to [f]
      in [env] and extends [env]. *)
  val bind_function
    : t -> function_identifier -> signature -> t

  (** [defined_function env f] returns [true] iff [f] is bound in [env]. *)
  val defined_function
    : t -> function_identifier -> bool

  (** [UnboundFunctionIdentifier f] is raised if [f] is unbound. *)
  exception UnboundFunctionIdentifier of function_identifier

  (** [lookup_function env f] returns the signature assigned to [f]
      in [env]. Raise {!UnboundFunctionIdentifier f] if no such
      [f] exists. *)
  val lookup_function
    : t -> function_identifier -> signature

  (** [bind_type_definition env t tdef] introduces a new type definition
      in [env]. *)
  val bind_type_definition
    : t -> type_identifier -> type_definition -> t

  (** [UnboundTypeIdentifier t] is raised if no such type [t] exists. *)
  exception UnboundTypeIdentifier of type_identifier

  (** [lookup_type_definition env t] looks for the definition of [t] in
      [env]. May raise {!UnboundTypeIdentifier t} if no such definition
      exists. *)
  val lookup_type_definition
    : t -> type_identifier -> type_definition

  (** [UnboundLabel l] is raised if no record type contains [l] as a label. *)
  exception UnboundLabel of label

  (** [lookup_recordtype_from_label env l] returns the type identifier
      of the record type that contains [l] as well as its definition.
      May raise {!UnboundLabel l}. *)
  val lookup_recordtype_from_label
    : t -> label -> type_identifier * (label * typ) list

  (** This exception is raised when a type identifier is defined but
      it is not a record type. *)
  exception NotRecordType of type_identifier

  (** [lookup_recordtype env t] returns all the field types of
      the record type [t] in [env].
      May raise {!UnboundTypeIdentifier l} or {!NotRecordType t}.*)
  val lookup_recordtype
    : t -> type_identifier -> (label * typ) list

  (** [UnboundTag t] is raised if no such tag [t] exists. *)
  exception UnboundTag of tag

  (** [lookup_tagged_union_type_from_tag env t] returns the type
      identifier of the union type that contains [t] as a tag as well
      as all the types of the tag parameters.
      May raise {!UnboundTag t}. *)
  val lookup_tagged_union_type_from_tag
    : t -> tag -> type_identifier * (tag * typ list) list

  (** This exception is raised if a type identifier is defined but it
      is not a tagged union. *)
  exception NotTaggedUnion of type_identifier

  (** [lookup_tagged_union_typ env t] returns type definition of
      the tagged union type [t] in [env].
      May raise {!UnboundTypeIdentifier t} or {!NotTaggedUnion t}. *)
  val lookup_tagged_union_type
    : t -> type_identifier -> (tag * typ list) list

end = struct
  type t = {
    variables : (identifier * typ) list;
    functions : (function_identifier * signature) list;
    typedefs  : (type_identifier * type_definition) list;
  }

  let empty = {
    variables = [];
    functions = [];
    typedefs  = [];
  }

  let bind e x ty = { e with
    variables = (x, ty) :: e.variables
  }

  exception UnboundIdentifier of identifier

  let lookup e x =
    try
      List.assoc x e.variables
    with Not_found ->
      raise (UnboundIdentifier x)

  let bind_function e f s = { e with
    functions = (f, s) :: e.functions
  }

  let defined_function e f =
    List.mem_assoc f e.functions

  exception UnboundFunctionIdentifier of function_identifier

  let lookup_function e f =
    try
      List.assoc f e.functions
    with Not_found ->
      raise (UnboundFunctionIdentifier f)

  let bind_type_definition env t tdef =
    { env with typedefs = (t, tdef) :: env.typedefs }

  exception UnboundTypeIdentifier of type_identifier

  let lookup_type_definition env t =
    try
      List.assoc t env.typedefs
    with Not_found -> raise (UnboundTypeIdentifier t)

  exception NotRecordType of type_identifier

  let lookup_recordtype env t =
    match lookup_type_definition env t with
      | RecordTy fs -> fs
      | _ -> raise (NotRecordType t)

  exception UnboundLabel of label

  let lookup_recordtype_from_label env l =
    try
      match List.find (fun (_, tdef) ->
        match tdef with
          | RecordTy fs -> List.exists (fun (l', _) -> l' = l) fs
          | _ -> false
      ) env.typedefs
      with
        | (i, RecordTy fs) -> (i, fs)
        | _ -> assert false (* Because of the predicate below. *)
    with Not_found ->
      raise (UnboundLabel l)

  exception UnboundTag of tag

  let lookup_tagged_union_type_from_tag env t =
    try
      match List.find (fun (_, tdef) ->
        match tdef with
          | TaggedUnionTy ts -> List.exists (fun (t', _) -> t' = t) ts
          | _ -> false
      ) env.typedefs
      with
        | (i, TaggedUnionTy ts) -> (i, ts)
        | _ -> assert false (* Because of the predicate below. *)
    with Not_found ->
      raise (UnboundTag t)

  exception NotTaggedUnion of type_identifier

  let lookup_tagged_union_type env t =
    match lookup_type_definition env t with
      | TaggedUnionTy ks -> ks
      | _ -> raise (NotTaggedUnion t)

end

type typing_environment = TypingEnvironment.t

(** The initial environment contains the type of the primitive functions. *)
let initial_typing_environment () =
     failwith "Student! This is your job!"

(** [typecheck tenv ast] checks that [ast] is a well-formed program
    under the typing environment [tenv]. *)
let typecheck tenv ast =
  let rec program tenv p =
    List.fold_left definition tenv p


  and definition tenv def =
    match Position.value def with
    | DefineValue (p, e) ->
      define_value tenv p e

    | DefineFunction (f, xs, _, e) ->
         failwith "Student! This is your job!"

    | DefineType (t, tdef) ->
      well_formed_type_definition (Position.position def) tenv tdef;
      TypingEnvironment.bind_type_definition tenv t tdef

  and well_formed_type_definition pos tenv = function
    | RecordTy ltys ->
         failwith "Student! This is your job!"

    | TaggedUnionTy ktys ->
         failwith "Student! This is your job!"


  (** [define_value tenv p e] returns a new environment that associates
      a type to each of the variables bound by the pattern [p]. *)
  and define_value tenv p e =
    let ty = infer_expression_type tenv e in
    check_pattern tenv ty p

  (** [infer_expression_type tenv e] returns the type of the expression
      [e] under the environment [tenv] if [e] is well-typed. *)
  and infer_expression_type tenv e =
    let pos = Position.position e in
    match Position.value e with
      | Literal l ->
        infer_literal_type l

      | Variable x ->
        (try
           TypingEnvironment.lookup tenv x
         with TypingEnvironment.UnboundIdentifier (Id x) ->
           error
             (Position.position e)
             (Printf.sprintf "Identifier `%s' is unbound." x)
        )

      | Define (p, e1, e2) ->
        let tenv = define_value tenv p e1 in
        infer_expression_type tenv e2

      | FunCall (f, es) ->
           failwith "Student! This is your job!"

      | IfThenElse (c, te, fe) ->
           failwith "Student! This is your job!"

      | Tuple es ->
        failwith "Student! This is your job!"

      | Record [] ->
        assert false (* By parsing. *)

      | Record fs ->
        failwith "Student! This is your job!"

      | RecordField (e, (Label lid as l)) ->
        failwith "Student! This is your job!"

      | TaggedValues (k, es) ->
        failwith "Student! This is your job!"

      | Case (e, bs) ->
        failwith "Student! This is your job!"



  (** [check_exhaustiveness pos ks bs] ensures that there is no
      forgotten cases in a case analysis assuming that [ks]
      are the only tags that can appear in the patterns of
      branches [bs]. *)
  and check_exhaustiveness pos ks = function
    | [] ->
         failwith "Student! This is your job!"
    | Branch (pat, _) :: bs ->
         failwith "Student! This is your job!"

  (** [infer_branches tenv pty previous_branch_type (Branch (p, e))]
      checks that the pattern [p] has type [pty] and that the type of
      [e] (if it exists) is the same as the one of the previous
      branch (unless this is the first branch). *)
  and infer_branches tenv pty previous_branch_type = function
    | [] ->
      begin match previous_branch_type with
        | None -> assert false (* By parsing. *)
        | Some ty -> ty
      end
    | Branch (pat, e) :: bs ->
         failwith "Student! This is your job!"

  (** [check_pattern tenv pty pat] checks that [pat] can be assigned
      the type [pty] and, if so, returns an extension of [tenv] with
      the variables of [pat] bound to their respective types. *)
  and check_pattern tenv pty pat =
    match Position.value pat, pty with
      | PVariable x, _ ->
           failwith "Student! This is your job!"

      | PTuple xs, TyTuple tys ->
           failwith "Student! This is your job!"

      | PWildcard, _ ->
           failwith "Student! This is your job!"

      | PTaggedValues (k, xs), TyIdentifier t ->
           failwith "Student! This is your job!"

      | _, _ ->
        error (Position.position pat) (
          Printf.sprintf "This pattern has not type: %s\n"
            (DatixPrettyPrinter.(to_string typ pty))
        )


  and check_variable tenv ty x =
    TypingEnvironment.bind tenv x ty

  and check_expression_type tenv xty e : unit =
    let ity = infer_expression_type tenv e in
    if ity <> xty then
      error (Position.position e) (
        Printf.sprintf "Incompatible types.\n  Expected: %s\n  Inferred: %s\n"
          (DatixPrettyPrinter.(to_string typ xty))
          (DatixPrettyPrinter.(to_string typ ity))
      )

  and check_same_length : Position.t -> 'a list -> 'b list -> unit =
    fun pos a b ->
    let aln = List.length a and bln = List.length b in
    if (aln <> bln) then (
      error pos
        (Printf.sprintf
           "Invalid number of arguments.\n  Expected: %d\n  Given: %d\n"
           aln bln
        )
    )

  and infer_literal_type = function
    | LInt _ ->
      tyint

  in
  program tenv ast
