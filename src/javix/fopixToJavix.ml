(** This module implements a compiler from Fopix to Javix. *)

let error pos msg =
  Error.error "compilation" pos msg

(** As in any module that implements {!Compilers.Compiler}, the source
    language and the target language must be specified. *)
module Source = Fopix
module Target = Javix

module S = Source.AST
module T = Target.AST

(** We will need the following pieces of information to be carrying
    along the translation: *)
type environment = {
  nextvar          : int;
  variables        : (S.identifier * T.var) list;
  function_labels  : (S.function_identifier * T.label) list;
  (** [function_formals] maintains the relation between function identifiers and their formal arguments. *)
  function_formals : (S.function_identifier * S.formals) list;
} 

(** Initially, the environment is empty. *)
let initial_environment () = {
  nextvar          = 0;
  variables        = [];
  function_labels  = [];
  function_formals = []}

 (** [lookup_function_label f env] returns the label of [f] in [env]. *)
let lookup_function_label f env =
  List.assoc f env.function_labels

(** [lookup_function_formals f env] returns the formal arguments of
    [f] in [env]. *)
let lookup_function_formals f env =
  List.assoc f env.function_formals

(** [fresh_function_label f] returns a fresh label starting with [f]
    that will be used for the function body instructions. *)
let fresh_function_label =
  let r = ref 0 in
  fun f ->
    incr r;
    T.Label (f ^ "_body_" ^ string_of_int !r)
(** Variables *)

(** [bind_variable env x] associates Fopix variable x to the next
    available Javix variable, and return this variable and the updated
    environment *)

let bind_variable env x =
  let v = T.Var env.nextvar in
  v,
  { env with
    nextvar = env.nextvar + 1;
    variables = (x,v) :: env.variables 
  }

let clear_all_variables env = {env with variables = []; nextvar = 0}

(** For return addresses (or later higher-order functions),
    we encode some labels as numbers. These numbers could then
    be placed in the stack, and will be used in a final tableswitch *)

module Labels :
 sig
   val encode : T.label -> int
   val all_encodings : unit -> (int * T.label) list
 end
=
 struct
   let nextcode = ref 0
   let allcodes = ref ([]:(int * T.label) list)
   let encode lab =
     let n = !nextcode in
     incr nextcode;
     allcodes := (n,lab) :: !allcodes;
     n
   let all_encodings () = !allcodes
 end

(*
Labels.encode m
*)
let basic_program code =
  { T.classname = "Fopix";
    T.code = code;
    T.varsize = 100;
    T.stacksize = 10000; 
  }

let located_instruction i =
  Position.unknown_pos i

let single_instruction i  =
  [(None, located_instruction i)]

type declaration_location =
  (** ... either before exit (because it must be executed). *)
  | BeforeExit of Target.AST.label
  (** ... or after exit (because it is executed only on demand). *)
  | AfterExit of Target.AST.label

(** [translate p env] turns a Fopix program [p] into a Javix program
    using [env] to retrieve contextual information. *)
let rec translate p env : T.t * environment =

  let  rec iter env after_exit = function
    | [] ->
    let allLabel = Labels.all_encodings() in 
 
    
    let (_ , block) = make_basic_block "return" 
                    ( T.([
                      Aload( Var(env.nextvar-1))
                      ;Unbox
                      ;Ireturn
                      ])) in 

    block 
    @ [ Some( T.Label "dispatch") , 
       located_instruction (T.Tableswitch(0,
                List.rev (List.map snd allLabel) ,
                (T.Label "dispatch"))
              )] 
    @ after_exit, env
      
    | d::ds -> 
    (** Process a declaration, get a block, a new environment and
          a location to put the block. *)
      let env, location, block = declaration env d in
      match location with
        | BeforeExit l ->
          let  bc , env =  iter env after_exit ds in
            (block@ bc , env)
        | AfterExit l ->
          let after_exit = block @ after_exit in
          iter env after_exit ds
      in
      let  corps, env = iter env [] p in
        basic_program   corps , env

and  declaration env = function
  | Source.AST.DefineValue (x, e) -> 
    let (Source.AST.Id i) as x = Position.value x in
    let (curidex ,env) = bind_variable env x  in  
    let instructions =
      (** 1. Insert the compiled code for the expression [e]. *)
      expression (Position.position e) env  (Position.value e)
      (** 2. Box and store some variable *)
    @ single_instruction(T.Box)
    @ single_instruction(T.Astore  curidex)
    in
    (** 3. We insert a label at the beginning of the block. *)
    let l, block = labelled_block i instructions in
    (** The variable is inserted in the environment. *)
      (env, BeforeExit l, block)

  | Source.AST.DefineFunction(  floc, lesformals, e) ->
  let (S.FunId id) as  f = Position.value floc  in  
   let l = lookup_function_label  f env  in 
    let newEnv = clear_all_variables env  in 
    let funEnv = List.fold_left  (fun  env x -> snd (bind_variable env x)) newEnv lesformals  in 
    let insts = expression  (Position.position floc) funEnv (Position.value e) 
      @(single_instruction (T.Swap))
      @(single_instruction (T.Goto (T.Label "dispatch"))) in 
    let block = label_block l insts  in 
      (env, AfterExit l,block)
   
  and bind_fun_formals env idfun f =
    { env with function_formals = (idfun,f)::env.function_formals}
  and bind_fun_label env idfun l =
    { env with function_labels = (idfun,l)::env.function_labels}

  (** [expression pos env e] compiles [e] into a block of Stackix
    instructions that *does not* start with a label. *)

  and expression pos env =  function 
   | Source.AST.Literal l -> 
    let lint = (fun (S.LInt i) -> i) l in   
     single_instruction (T.Box)     
    @single_instruction (T.Bipush lint)
 
  | Source.AST.Variable (Source.AST.Id x as i) ->      
    single_instruction (T.Aload (List.assoc i env.variables ))
    @single_instruction (T.Unbox)  

  | Source.AST.Define ( x  , e1, e2) ->
    (* pas sur mais S.Id ==T.Id *)
    let (i, envBinding) = bind_variable env ( Position.value x)  in

    expression   (Position.position  e1) env (Position.value e1)  
    @ single_instruction (T.Box)
    @ single_instruction T.(Astore (List.assoc (Position.value x) envBinding.variables) ) 
    @ expression (Position.position e2) envBinding (Position.value e2)

  | Source.AST.IfThenElse (c, t, f) -> 
    
    let label1 ,block1 = labelled_block "true" (expression pos  env (Position.value t)) in
    let label2 , block2 = labelled_block "false" (expression pos env (Position.value f)) in 
    let label3 , block3 = labelled_block "end" (single_instruction (T.Comment "end")) in 
    
    let jump = begin 
      match Position.value c with 
        | Source.AST.FunCall (Source.AST.FunId fid ,[ et ;ef])   when is_noIcomp(fid)  ->
                expression pos env (Position.value et)
                @expression pos env (Position.value ef)
                @ single_instruction( T.If_icmp((binop_to_noIcomp fid ) , label2))
        | _ -> 
            expression (Position.position c) env ( Position.value c )
            @single_instruction(T.Bipush 1)
            @single_instruction(T.If_icmp(T.NE , label2))
      end 
  in 
   let gotoend = single_instruction(T.Goto label2) in  
    jump 
    @ block1 
    @ gotoend 
    @ block2
    @ block3
  
  | Source.AST.FunCall (Source.AST.FunId f, [e1; e2])
    when is_binop( f)  -> 
      expression pos env (Position.value e1)
      @expression pos env (Position.value e2) 
      @single_instruction( to_binop(f) ) 

  | Source.AST.FunCall (S.FunId "block_set", [location;index;e]) ->
     expression (Position.position e ) env (Position.value e ) 
     @expression (Position.position index ) env (Position.value index )
      @expression (Position.position location ) env (Position.value location ) 
      @(single_instruction (T.Box))
      @(single_instruction (T.AAstore))

  | Source.AST.FunCall (S.FunId "block_get", [location; index]) -> 

      expression (Position.position index ) env (Position.value index ) 
      @expression (Position.position location ) env (Position.value location ) 
      @(single_instruction (T.Box))
      @(single_instruction (T.AAload))
      @single_instruction (T.Unbox)

  | Source.AST.FunCall (S.FunId "block_create" , [size; init]) ->  
      expression (Position.position init) env (Position.value init) 
      @expression (Position.position size) env (Position.value size) 
      @ single_instruction( T.Anewarray) 

 | S.FunCall (f, actuals) ->
    let formals =lookup_function_formals f env in  
    let blockList = List.flatten ( 
          List.map2 ( fun (id ) vals -> 
                        (expression (Position.position vals) env (Position.value vals)) 
                        @(single_instruction (T.Box)) 
                        @(single_instruction (T.Astore (T.Var id)))
                    )
         (gen (List.length actuals))  
          actuals) in 
   let labelfunc = lookup_function_label f env in 
  let labelID  = Labels.encode labelfunc in 
  blockList 
  @(single_instruction (T.Bipush labelID))
  @(single_instruction (T.Goto (lookup_function_label f env)))
  
and gen i = match i with 
|0 -> [0] 
|_ -> gen (i-1)@[i-1] 

and label_of_block = function
  | (l, _) :: _ -> l
  | _ -> None

and label_block l =
  fun instructions ->
    match instructions with
    | [] -> assert false 
    | (Some l, _) :: _ -> assert false
    | (None, i) :: is -> (Some l, i) :: is

  and labelled_block =
  let c = ref 0 in
  fun prefix instructions ->
    match label_of_block instructions with
    | None ->
      let l = incr c; Target.AST.Label (prefix ^ string_of_int !c) in
      (l, label_block l instructions)
    | Some l ->
      (l, instructions)
 and is_binop = function
  | "+" | "-" | "*" | "/" | "<" | ">" | "=" | "<=" | ">=" -> true
  | _ -> false
and to_binop = function
  | "+" -> Binop T.Add
  | "-" -> Binop T.Sub
  | "*" -> Binop T.Mul
  | "/" -> Binop T.Div
  | _ -> failwith "Call to no binop operator." 
and binop_to_noIcomp = function
  | "<"  -> T.GE
  | ">"  -> T.LE
  | "<=" -> T.GT
  | ">=" -> T.LT
  | "="  -> T.NE 
  | "!=" -> T.EQ
  | _ -> assert false
  
and is_noIcomp = function
  | "<" | ">"  | "<="  | ">=" | "=" | "!=" -> true
  | _ -> false; 
and make_basic_block =
  fun prefix instructions ->
    assert (instructions <> []);
    labelled_block prefix (
      List.map (fun i -> (None, located_instruction i))
       instructions
    )

and located_instruction i =
  Position.unknown_pos i
