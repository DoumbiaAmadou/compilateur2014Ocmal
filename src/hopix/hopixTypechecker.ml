(** This module implements a type checker for Datix. *)

open HopixAST

(** Type checker error message producer. *)
let error = Error.error "during type checking"
let incrID : int ref = ref 0 

(** Basic types. *)
let tyint  = TyBase (TId "int", [])
let tybool = TyBase (TId "bool", [])

 type  standard_typ = 
    |STInteger
    |STBoolean
    |STCstTyp of string * standard_typ list
    |STArr of standard_typ * standart_typ
    |STVar of standard_typvar
    |STUnit

type standard_typvar =
    {
      id : string;
      mutable content : standard_typ option
    }
let newtyvar () : tyvar =
   incrID := !incrID+1 ;  
   let id = !incrID in
   {id = string_of_int(id) ;content= None}
(** During typechecking, we thread an environment that contains
    the type of variables and the type definitions. *)
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
    typedefs  : (type_identifier * type_definition) list;
  }

  let empty = {
    variables = [];
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

  let bind_type_definition env t tdef =
    { env with typedefs = (t, tdef) :: env.typedefs }

  exception UnboundTypeIdentifier of type_identifier

  let lookup_type_definition env t =
    try
      List.assoc t env.typedefs
    with Not_found ->
      raise (UnboundTypeIdentifier t)

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
  (*                             begin       MGU part                      *)

let rec get_standard_typ typ : standard_typ = match typ with
    |TyBase(tid,tList) -> begin
        match tid with
        |TId("int") -> STInteger
        |TId("bool") -> STBoolean
        |TId(_) -> begin
             match tList with
             |[] -> failwith "error: TyBase type undefined!"
             |_ -> failwith "error: TyBase type undefined! (TODO)"
        end
    |TyTuple(typ_list) -> STCstTyp("tuple",(get_standard_typ_list typ_list))
    |TyArrow(t1,t2) -> STArr((get_standard_typ t1),(get_standard_typ t2))
   end       

  let rec get_standard_typ_list typ_list : standard_typ list = match typ_list with
    |[] -> []
    |a::tail -> get_standard_typ(a)::(get_standard_typ_list tail)
    
 let rec standard_mgu list : unit = match list with
    |[] -> ()
    |(a,b)::tail -> match a, b with
        |STInteger, STInteger -> ()
        |STBoolean, STBoolean -> ()
        |STUnit,STUnit -> ()
        |STCstTyp(id1,st_typ_list1), STCstTyp(id2,st_typ_list2) -> 
          if (id1<>id2) then failwith "error: not the same type!"
          else
      begin
        match st_typ_list1, st_typ_list2 with
        |[], [] -> ()
        |[t1],[t2] -> standard_mgu ((t1,t2)::tail)
        |t1::tail1, t2::tail2 -> standard_mgu ((t1,t2)::(StCstTyp(id1,tail1),StCstTyp(id2,tail2))::tail);
        |_, _ -> failwith "error: not the same type!"
      end                  
        |STArr(t1,t2),STArr(t3,t4) -> standard_mgu ((t1,t3)::(t2,t4)::tail)
        |STVar(tv1),STVar(tv2) when tv1.id = tv2.id -> standard_mgu tail
        |TVar(tv1),t | t,TVar(tv1) ->
            (*rajouter verif tv1 n'appartient pas a t*)
            begin
              match tv1.content with
              |None -> tv1.content <- Some(b); standard_mgu tail
              |Some(t1) -> standard_mgu ((t1,b)::tail)
            end
        |_ -> failwith "error: not the same type!"

 let rec mgu list : unit = match list with
    |[] -> ()
    |(a,b)::tail -> standard_mgu ((get_standard_typ a),(get_standard_typ b));
        mgu tail



        (*                             END       MGU part                      *)


type typing_environment = TypingEnvironment.t

(** The initial environment contains the type of the primitive functions. *)
let initial_typing_environment () =
  TypingEnvironment.empty (* TODO: add the primitive functions here *)

let rec newVariablelist s = if s =0 then [] else  newtyvar()::newlistvariable (s-1) 


(** [typecheck tenv ast] checks that [ast] is a well-formed program
    under the typing environment [tenv]. *)
let typecheck tenv ast =

  let rec program tenv p =
    List.fold_left definition tenv p

  and definition tenv def =
    match Position.value def with
      | DefineValue (p, e) -> 
        define_value tenv p e
      | DefineType (t, param, tdef) ->
        let tenv' = TypingEnvironment.bind_type_definition tenv t (TaggedUnionTy []) in
        well_formed_type_definition (
        Position.position def) tenv' tdef;
        TypingEnvironment.bind_type_definition tenv t tdef

  and well_formed_type_definition pos tenv = function
    | RecordTy ltys -> check_unicity pos ltys " Record" ;
         List.map (fun (Label x,y) -> lookup tenv (well_formed_type_definition pos tenv y) ) ltys  
         (*     failwith "Student! This was your job!" *)

    | TaggedUnionTy ktys -> 
              check_unicity pos ltys " TaggedUnionTy" ; 
              List.map (fun (Constructor x,y) -> lookup tenv (well_formed_type_definition pos tenv y) ) ktys  
              (*failwith "Student! This was your job!" *)

      
  

  (** [define_value tenv p e] returns a new environment that associates
      a type to each of the variables bound by the pattern [p]. *)
  
  and define_value tenv p e =
    

  match (p , infer_expression_type tenv e ) with 
  | PWilCard , _  -> ()  
  | (PVariable i), t   -> bind  tenv i  t 
  |(PTuple li) , t  -> let a = (newlistvariable List.length li ) in  
     mgu(PTuple(a) ,t) ;  
     bind tenv li  PTuple(a)   
  | (PTuple  l1) , t -> if ( List.length l1  = List.length l2) then  bind tenv i t 
  | (PTaggedValues  il) , u ->  List.fold_left (bind tenv e) p.variable 
  
  (* to change *)

 (* failwith " student this your job" * )

  | PTuple  l  ->  PTuple l
  | PTaggedValues  il
  List.fold_left (bind tenv e) p.variables
 *
 match p with 
  |pWilCard  ->   

and newlistvariable List.length li = 
   *)



  (** [infer_expression_type tenv e] returns the type of the expression
      [e] under the environment [tenv] if [e] is well-typed. *)
  and infer_expression_type tenv e =
    let pos = Position.position e in
    match Position.value e with
      | Fun (x, e) -> let tyx = match snd x with
                      |Some(ty) -> ty 
                      |None ->  newtyvar() 
                    in  TyArrow( tyx ,(infer_expression_type  (bind (fst x)  tyx tenv) e))        
      | RecFuns fs ->
       let newEnv =    List.fold_left (fun x y -> bind (fst y)  newtyvar()  x )   env fs 
       in List.fold_left  (fun x y  -> mgu( lookup (fst y)  , infer_expression_type x snd y )) newEnv fs 

 
        (*   failwith "Student! This is your job!" *)
      | Apply (a, b) -> 
        let et1 = w context t1  in 
        let et2 = w context t2 in 
           failwith "Student! This is your job!"
      | Literal l ->
           failwith "Student! This is your job!"
      | Variable x ->
           lookup tenv x
      | Define (p, e1, e2) ->
           failwith "Student! This is your job!"

      | IfThenElse (c, te, fe) ->
         (* match   infer_expression_type 

             Source.AST.IfThenElse (c, t, f) ->
    (* Label and block for the expression for the then*)
    let lt, bt = labelled_block "true" (expression' env t) in
    (* Label and block for the expression for the else *)
    let lf, bf = labelled_block "false" (expression' env f) in
    (* Label and block corresponding to the end *)
    let le, be = make_basic_block "end" [Target.AST.(Comment "end")] in
    let end_jump = single_instruction (Target.AST.(Jump le)) in 
    expression' env c
    @ single_instruction (Target.AST.(ConditionalJump (lt,lf)))
    @ bt
    @ end_jump
    @ bf
    @ end_jump
    @ be 

    
        *) 
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

      | PTaggedValues (k, xs), TyBase (t,_) ->
           failwith "Student! This is your job!"

      | _, _ ->
        error (Position.position pat) (
          Printf.sprintf "This pattern has not type: %s\n"
            (HopixPrettyPrinter.(to_string typ pty))
        )

  and check_irrefutable_pattern tenv pat : unit =
    match (Position.value pat) with
      | PWildcard | PVariable _ | PTuple _ -> ()
      | PTaggedValues (k, _) ->
        let t', ktys = TypingEnvironment.lookup_tagged_union_type_from_tag tenv k in
        if List.length ktys <> 1 then
          error (Position.position pat) "This pattern is not irrefutable."

    (*vérification de l'unicité des elements de la list*)
and checkList pos ls what ->
        let ls = List.(sort (fun (l1, _) (l2, _) -> compare l1 l2) ls) in
        let ls = fst (List.split ls) in
        if not (ExtStd.List.all_distinct ls) then
          error pos (Printf.sprintf "Each %s must appear exactly once." what)
  and check_variable tenv ty x =
    TypingEnvironment.bind tenv x ty

  and check_expression_type tenv xty e : unit =
    let ity = infer_expression_type tenv e in
    if ity <> xty then
      error (Position.position e) (
        Printf.sprintf "Incompatible types.\nExpected: %s\nInferred: %s\n"
          (HopixPrettyPrinter.(to_string typ xty))
          (HopixPrettyPrinter.(to_string typ ity))
      )

  and check_same_length : Position.t -> 'a list -> 'b list -> unit =
    fun pos a b ->
    let aln = List.length a and bln = List.length b in
    if (aln <> bln) then (
      error pos
        (Printf.sprintf
           "Invalid number of arguments.\nExpected: %d\nGiven: %d\n."
           aln bln
        )
    )

  and infer_literal_type = function
    | LInt _ ->
      tyint

  and check_unicity : Position.t -> ('a * 'b) list -> string -> unit =
    fun pos ls what ->
        let ls = List.(sort (fun (l1, _) (l2, _) -> compare l1 l2) ls) in
        let ls = fst (List.split ls) in
        if not (ExtStd.List.all_distinct ls) then
          error pos (Printf.sprintf "Each %s must appear exactly once." what)

  in
  program tenv ast
