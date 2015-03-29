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

let fresh_tag_id =
  let r = ref 0 in
  fun () -> incr r; !r

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

  and definition env = function
    | S.DefineValue (pat, e) ->
       toplevel_pattern (Position.position pat) env (Position.value (expression' env e)) (Position.value pat)

    | S.DefineFunction (f, xs, _, e) -> 
       [T.DefineFunction (
	    Position.with_pos (Position.position f) (function_identifier (Position.value f)),
	    formals xs,
	    expression' env e)]  
			 
    | S.DefineType (t, tdef) ->
       []


  and expression pos env e =
    let locate = Position.with_pos pos in
    match e with
      | S.Literal l -> Position.unknown_pos(T.Literal (literal l))

      | S.Variable x -> Position.unknown_pos(T.Variable (identifier x))
          
      | S.Define (pat, e1, e2) -> 
          pattern' env (Position.value (expression' env e1)) pat e2

      | S.FunCall (f, es) -> 
	 Position.unknown_pos(
	     T.FunCall (
		 (function_identifier f),
		 (List.map (expression' env) es)
	       )
	   )

      | S.IfThenElse (c, et, ef) -> 
	 Position.unknown_pos(
	     T.IfThenElse (
		 (expression' env c),
		 (expression' env et),
		 (expression' env ef)
	       )
	   )

      | S.Tuple es ->
	 let ptr = T.FunCall (T.FunId "block_create",
			      [(Position.unknown_pos (T.Literal(T.LInt(List.length(es)))));
			       (Position.unknown_pos (T.Literal(T.LInt(0)))) ]
			     )
	 in  
	 let id = fresh_identifier ()
	 in
	 begin	 
	   match es with
	   |[] -> failwith "Error: tuple is empty"
	   |e::tail -> 
	       let rec app_tuple_def i e_list = 
		 match e_list with
		 |[] -> failwith "error"
		 |[e] -> T.FunCall(T.FunId "block_set",
				   [
				     (Position.unknown_pos (ptr));
				     (Position.unknown_pos (T.Literal(T.LInt(i))));
				     (expression' env e)
				  ])
				  
		 |e::tail -> T.Define(Position.unknown_pos id,
				      Position.unknown_pos 
					(T.FunCall(T.FunId "block_set",
						   [Position.unknown_pos ptr;
						    Position.unknown_pos (T.Literal(T.LInt(i)));
						    (expression' env e)]
						  )
					),
				      Position.unknown_pos (app_tuple_def (i+1) tail)
				     )
	       in
	       Position.unknown_pos(
		   T.Define(Position.unknown_pos id,
			    Position.unknown_pos ptr,
			    Position.unknown_pos (app_tuple_def 0 es)
			   )
		 )
	 end


      | S.Record rs ->
	 let ptr = T.FunCall (T.FunId "block_create",
			      [(Position.unknown_pos (T.Literal(T.LInt(List.length(rs)))));
			       (Position.unknown_pos (T.Literal(T.LInt(0)))) ]
			     )
	 in  
	 let id = fresh_identifier ()
	 in
	 begin	 
	   match rs with
	   |[] -> failwith "Error: record is empty"
	   |(lab,e)::tail -> 
	       let rec app_record_def i le_list = 
		 match le_list with
		 |[] -> failwith "error"
		 |[(lab,e)] -> bind_label_representation env (lab,i);
			       T.FunCall(T.FunId "block_set",
					 [
					   (Position.unknown_pos (ptr));
					   (Position.unknown_pos (T.Literal(T.LInt(i))));
					   (expression' env e)
					])
					
		 |(lab,e)::tail -> bind_label_representation env (lab,i);
				   T.Define(Position.unknown_pos id,
					    Position.unknown_pos 
					      (T.FunCall(T.FunId "block_set",
							 [Position.unknown_pos ptr;
							  Position.unknown_pos (T.Literal(T.LInt(i)));
							  (expression' env e)]
							)
					      ),
					    Position.unknown_pos (app_record_def (i+1) tail)
					   )
	       in
	       Position.unknown_pos(
		   T.Define(Position.unknown_pos id,
			    Position.unknown_pos ptr,
			    Position.unknown_pos (app_record_def 0 rs)
			   )
		 )
	 end
		  
      | S.RecordField (e, l) ->
	 match (Position.value e) with
	 |S.Record le_list -> expression' env (List.assoc l le_list)
		  
      | S.TaggedValues (k, es) ->
	 let ptr = T.FunCall (T.FunId "block_create",
			      [(Position.unknown_pos (T.Literal(T.LInt(List.length(es)+1))));
			       (Position.unknown_pos (T.Literal(T.LInt(0)))) ]
			     )
	 in  
	 let id = fresh_identifier ()
	 in
	 begin	 
	   match es with
	   |[] -> failwith "Error: taggedValues is empty"
	   |e::tail -> 
	       let rec app_tag_def i le_list = 
		 match le_list with
		 |[] -> failwith "error"
		 |[e] -> T.FunCall(T.FunId "block_set",
				   [
				     (Position.unknown_pos (ptr));
				     (Position.unknown_pos (T.Literal(T.LInt(i))));
				     (expression' env e)
				  ])
				  
		 |e::tail -> T.Define(Position.unknown_pos id,
				      Position.unknown_pos 
					(T.FunCall(T.FunId "block_set",
						   [Position.unknown_pos ptr;
						    Position.unknown_pos (T.Literal(T.LInt(i)));
						    (expression' env e)]
						  )
					),
				      Position.unknown_pos (app_tag_def (i+1) tail)
				     )
	       in
	       let tag_representation = fresh_tag_id ()
	       in
	       bind_tag_representation env (k,tag_representation);
	       Position.unknown_pos(
		   T.Define(Position.unknown_pos id,
			    Position.unknown_pos ptr,
			    
			    Position.unknown_pos(
				T.Define(Position.unknown_pos id,
					 Position.unknown_pos 
					   (T.FunCall(T.FunId "block_set",
						      [Position.unknown_pos ptr;
						       Position.unknown_pos (T.Literal(T.LInt(tag_representation)));
						       (expression' env e)]
						     )
					   ),
					 Position.unknown_pos (app_tag_def 0 es)
					)
			      )
			   )
		 )
	 end
		  
      | S.Case (e, bs) -> branches env (Position.value (expression' env e)) bs
		  
  and expression' env e =
    expression (Position.position e) env (Position.value e)

  and branches env x = function
    | [] ->
         failwith "error: any pattern associated to the expression"

    | S.Branch (pat, e) :: bs -> 
       begin
       match (Position.value pat), x with
       |S.PWildcard,_ |S.PVariable(_),_ -> pattern' env x pat e

       |S.PTaggedValues(tag,id_list),T.Define(id,e1,e2) ->
	 
	 begin     
	   match (Position.value e1), (Position.value e2) with
	   |T.FunCall (T.FunId "block_create",[lgth;init_val]), 
	    T.Define (id,tag_rep,_) ->
	     begin
	       match (Position.value lgth),(Position.value tag_rep) with
	       |T.Literal(T.LInt(length)),
		T.FunCall(T.FunId "block_set",[_;tag_id;_]) ->
			 if(List.length(id_list) = length-1)
			 then begin
			     match (Position.value tag_id) with 
			     |T.Literal(T.LInt(tag_i)) -> 
			       if((lookup_tag_representation env tag) = tag_i)
			       then pattern' env x pat e 
			       else branches env x bs
			     |_ -> branches env x bs
			   end
			 else branches env x bs
	       |_ -> branches env x bs
	     end
	   |_ -> branches env x bs
	 end	   

       |S.PTuple(id_list),T.Define(id,e1,e2) -> 
	 
	 begin
	   match (Position.value e1) with
	   |T.FunCall (T.FunId "block_create",[lgth;init_val])
	    ->
	     begin
	       match (Position.value lgth) with
	       |T.Literal(T.LInt(length)) ->
		 if (List.length(id_list) = length)
		 then pattern' env x pat e
		 else branches env x bs
	       |_ -> failwith "error: the block's length is not a int value"
	     end
	   |_ -> branches env x bs 
	 end
	   
       |_ -> branches env x bs
       end 		      
(*/////*)

  and bind_es_pat yss exp =
    match yss, exp with
    |y::tail, T.Define(id,e1,e2) ->
      
      begin
	match (Position.value e1) with
	|T.FunCall(T.FunId "block_create",_) ->
	  bind_es_pat yss (Position.value e2)
	|T.FunCall(T.FunId "block_set", [ptr;index;e]) ->
	  (T.DefineValue (
	       Position.unknown_pos (identifier y),
	       Position.unknown_pos (T.FunCall(T.FunId "block_get",[ptr;index]))
	  ))::(bind_es_pat tail (Position.value e2))
      end
	
    |[y], T.FunCall(T.FunId "block_set",[ptr;index;e]) ->
      [T.DefineValue (
	   Position.unknown_pos (identifier y),
	   Position.unknown_pos (T.FunCall(T.FunId "block_get",[ptr;index]))
      )]
	
    |_ -> failwith "error: not the same number of element in the tuple"
		   
  and toplevel_pattern pos env x p =
    (* Auxiliary function for dealing with DefineValue(p,e0):
       The identifier x should contain at runtime the value of e0.
       We then construct here some code to destructurate this value
       and assign all the variables occuring in pattern p. *)
    match p with
    | S.PWildcard -> []
		       
    | S.PVariable y -> let id_loc = 
			 Position.unknown_pos (identifier y) in
		       [T.DefineValue (id_loc, Position.unknown_pos x)]
			 
    | S.PTuple ys -> bind_es_pat ys x
		       
    | S.PTaggedValues (k, ys) ->
       
       match ys, x with
       |y::tail, T.Define(id,e1,e2) ->
	 begin
	   match (Position.value e2) with
	   |T.FunCall(T.FunId "block_set",e3) -> failwith "error"
	   |T.Define(id,e21,e22) -> bind_es_pat ys (Position.value e22)
	 end
       |_ -> failwith "error: not the same number of element in the tagged expressions"
		      
  and pattern pos env x pat e =
    (* Auxiliary function for dealing with patterns in Define(pat,e0,e)
       or Case(e0,[(pat,e);...]).
       The identifier x should contain at runtime the value of e0.
       We then construct here some code to destructurate this value
       and assign all the variables occuring in pattern p, before
       launching the computation of e. *)
    match pat with
      | S.PWildcard -> expression' env e

      | S.PVariable y -> Position.unknown_pos(
			     T.Define(Position.unknown_pos (identifier y) ,
				      Position.unknown_pos x,
				      (expression' env e)
				     )
			   )
      
      | S.PTuple ys -> let rec bind_tuple_pat yss exp =
		       match yss, exp with
		       |y::tail, T.Define(id,e1,e2) ->
			 
			 begin
			   match (Position.value e1) with
			   |T.FunCall(T.FunId "block_create",_) ->
			     bind_tuple_pat yss (Position.value e2)
			   |T.FunCall(T.FunId "block_set", [ptr;index;e3]) ->
			     T.Define(
				 Position.unknown_pos (identifier y),
				 Position.unknown_pos (T.FunCall(T.FunId "block_get",[ptr;index])),
				 Position.unknown_pos (bind_tuple_pat tail (Position.value e2))
			       )
			 end
			   
		       |[y], T.FunCall(T.FunId "block_set",[ptr;index;e3]) ->
			 T.Define(
			     Position.unknown_pos (identifier y),
			     Position.unknown_pos (T.FunCall(T.FunId "block_get",[ptr;index])),
			     (expression' env e)
			   )
			   
		       |_ -> failwith "error: not the same number of element in the tuple"
		       in
		       Position.unknown_pos (bind_tuple_pat ys x)
					    
      | S.PTaggedValues (k, ys) -> let rec bind_tag_pat yss exp =
		       match yss, exp with
		       |y::tail, T.Define(id,e1,e2) ->
			 
			 begin
			   match (Position.value e1) with
			   |T.FunCall(T.FunId "block_create",_) ->
			     bind_tag_pat yss (Position.value e2)
			   |T.FunCall(T.FunId "block_set", [ptr;index;e3]) ->
			     T.Define(
				 Position.unknown_pos (identifier y),
				 Position.unknown_pos (T.FunCall(T.FunId "block_get",[ptr;index])),
				 Position.unknown_pos (bind_tag_pat tail (Position.value e2))
			       )
			 end
			   
		       |[y], T.FunCall(T.FunId "block_set",[ptr;index;e3]) ->
			 T.Define(
			     Position.unknown_pos (identifier y),
			     Position.unknown_pos (T.FunCall(T.FunId "block_get",[ptr;index])),
			     (expression' env e)
			   )
			   
		       |_ -> failwith "error: not the same number of element in the tuple"
		       in
		       Position.unknown_pos (bind_tag_pat ys x)

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

