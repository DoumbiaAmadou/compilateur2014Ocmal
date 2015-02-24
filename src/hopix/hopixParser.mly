%{

  open HopixAST

  let funcall f args =
    let locate a b x =
      let apos = Position.position a
      and bpos = Position.position b
      in
      Position.(with_pos (join apos bpos) x)
    in
    Position.value (
      List.fold_left (fun t arg -> locate t arg (Apply (t, arg))) f args
    )

  let lambda xs e =
    let locate x = Position.map (fun _ -> x) e in
    locate
      (List.fold_left (fun e x -> Fun (x, locate e))
         (Position.value e)
         (List.rev xs))

  let make_arrow_opt o1 o2 = match o1, o2 with
    | Some t1, Some t2 -> Some (TyArrow (t1,t2))
    | _ -> None

  let arrow_type ins out =
    List.fold_left make_arrow_opt out (List.rev ins)

  let recfuns fs =
    let recfun (f, xs, out_ty, e) =
      let ins = List.map snd xs in
      let fty = arrow_type ins out_ty in
      (Position.map (fun f -> (f, fty)) f, lambda xs e)
    in
    RecFuns (List.map recfun fs)

%}

%token REC AND VAL DEF IN END IF THEN ELSE EVAL WITH CASE TYPE
%token PLUS MINUS STAR SLASH GT GTE LT LTE EQUAL FIX
%token UNDERSCORE DRIGHTARROW RIGHTARROW PIPE DOT
%token LPAREN RPAREN LBRACE RBRACE COLONEQUAL
%token COMMA SEMICOLON COLON EOF
%token<int> INT
%token<string> ID UID

%right SEMICOLON
%nonassoc GT GTE LT LTE EQUAL
%left PLUS MINUS
%right DRIGHTARROW
%left STAR SLASH
%left DOT

%start<HopixAST.t> program

%%

program: ds=located(definition)* EOF
{
  ds
}
| error {
  let pos = Position.lex_join $startpos $endpos in
  Error.error "parsing" pos "Syntax error."
}

definition: VAL x=located(pattern) EQUAL e=located(expression)
{
  DefineValue (x, e)
}
| DEF f=located(function_identifier)
  xs=formals
  EQUAL e=located(expression)
{
  DefineValue (Position.map (fun f -> PVariable f) f, lambda xs e)
}
| REC
  fs=located(separated_nonempty_list(AND, frec))
{
  let pos = Position.position fs in
  let fs  = Position.value fs in
  let pat = PTuple (List.map (fun (f, _, _, _) -> Position.value f) fs) in
  DefineValue (Position.with_pos pos pat, Position.with_pos pos (recfuns fs))
}
| EVAL e=located(expression)
{
  DefineValue (Position.map (fun _ -> PVariable (Id "res")) e, e)
}
| TYPE t=type_identifier l=type_params EQUAL td=type_definition
{
  DefineType (t, l, td)
}
| TYPE t=type_identifier l=type_params COLONEQUAL ty = typ
{
  DefineType (t, l, DefTy ty)
}


frec:
  f=located(function_identifier)
  xs=tbinding*
  COLON out_ty=typ
  EQUAL e=located(expression)
{
  (f, xs, Some out_ty, e)
}
| f=located(function_identifier)
  xs=identifier*
  EQUAL e=located(expression)
{
  (f, List.map (fun id -> (id,None)) xs, None, e)
}

type_definition:
  LBRACE fs=separated_nonempty_list(SEMICOLON, fielddef) RBRACE
{
  RecordTy fs
}
| PIPE? ts=separated_nonempty_list(PIPE, tagdef)
{
  TaggedUnionTy ts
}

tagdef:
  k=tag LPAREN ts=separated_list(COMMA, typ) RPAREN
{
  (k, ts)
}

fielddef:
  l=label COLON t=typ
{
  (l, t)
}

%inline formals: xs=binding+ {
  xs
}

tbinding: LPAREN x=identifier COLON ty=typ RPAREN
{
  (x, Some ty)
}

binding: LPAREN x=identifier COLON ty=typ RPAREN
{
  (x, Some ty)
}
| x=identifier
{
  (x, None)
}

%inline type_params: /* empty */
{
 []
}
| LPAREN l = separated_nonempty_list(COMMA, type_identifier) RPAREN
{
  l
}

%inline type_args: /* empty */
{
 []
}
| LPAREN l = separated_nonempty_list(COMMA, typ) RPAREN
{
  l
}

expression:
  l=literal
{
  Literal l
}
| x=identifier
{
  Variable x
}
| VAL x=located(pattern)
  EQUAL
    e1=located(expression)
  IN
    e2=located(expression)
  END
{
  Define (x, e1, e2)
}
| IF
  c=located(expression)
  THEN t=located(expression)
  ELSE f=located(expression)
  END
{
  IfThenElse (c, t, f)
}
| l=located(expression) b=located(binop) r=located(expression) {
  funcall (Position.map (fun x -> (Variable (Id x))) b) [l; r]
}
| e1=located(expression) SEMICOLON e2=located(expression) {
  Define (Position.map (fun _ -> PWildcard) e1, e1, e2)
}
| t=tuple
{
  t
}
| CASE e=located(expression)
  WITH
  PIPE? bs=separated_nonempty_list(PIPE, branch)
  END
{
  Case (e, bs)
}
| LBRACE fs=separated_nonempty_list(SEMICOLON, field) RBRACE
{
  Record fs
}
| LBRACE xs=formals RIGHTARROW b=located(expression) RBRACE
{
  Position.value (lambda xs b)
}
| FIX fs=separated_list(AND, frec) END
{
  recfuns fs
}
| REC fs=located(separated_list(AND, frec)) IN e=located(expression) END
{
  let pos = Position.position fs in
  let fs  = Position.value fs in
  let pat = PTuple (List.map (fun (f, _, _, _) -> Position.value f) fs) in
  Define (Position.with_pos pos pat, Position.with_pos pos (recfuns fs), e)
}
| e=located(expression) DOT l=label
{
  RecordField (e, l)
}
| k=tag LPAREN es=separated_list(COMMA, located(expression)) RPAREN
{
  TaggedValues (k, es)
}
| a=located(left_application_expression) b=located(right_application_expression)
{
  Apply (a, b)
}

tuple:
  LPAREN es=separated_nonempty_list(COMMA, located(expression)) RPAREN {
  match es with
    | [] -> assert false
    | [e] -> Position.value e
    | es -> Tuple es
}

left_application_expression:
  l=literal
{
  Literal l
}
| x=identifier
{
  Variable x
}
| a=located(left_application_expression) b=located(right_application_expression)
{
  Apply (a, b)
}
| e=tuple
{
  e
}

right_application_expression:
  l=literal
{
  Literal l
}
| x=identifier
{
  Variable x
}
| IF
  c=located(expression)
  THEN t=located(expression)
  ELSE f=located(expression)
  END
{
  IfThenElse (c, t, f)
}
| CASE e=located(expression)
  WITH
  PIPE? bs=separated_nonempty_list(PIPE, branch)
  END
{
  Case (e, bs)
}
| LBRACE fs=separated_nonempty_list(SEMICOLON, field) RBRACE
{
  Record fs
}
| LBRACE xs=formals RIGHTARROW b=located(expression) RBRACE
{
  Position.value (lambda xs b)
}
| FIX fs=separated_list(AND, frec) END
{
  recfuns fs
}
| t=tuple
{
  t
}


field: l=label EQUAL e=located(expression)
{
  (l, e)
}

label: x=ID
{
  Label x
}

branch: p=located(pattern) RIGHTARROW e=located(expression)
{
  Branch (p, e)
}

pattern: x=identifier
{
  PVariable x
}
| UNDERSCORE
{
  PWildcard
}
| LPAREN ps=separated_nonempty_list(COMMA, identifier) RPAREN
{
  PTuple ps
}
| k=tag LPAREN ps=separated_list(COMMA, identifier) RPAREN
{
  PTaggedValues (k, ps)
}

tag: k=UID
{
  Constructor k
}

typ:
  x=type_identifier l=type_args
{
  TyBase (x,l)
}
| LPAREN ts=separated_nonempty_list(STAR, typ) RPAREN {
  match ts with
    | [] -> assert false
    | [t] -> t
    | ts -> TyTuple ts
}
| lhs=typ DRIGHTARROW rhs=typ
{
  TyArrow (lhs, rhs)
}

type_identifier: x=ID
{
  TId x
}

%inline binop:
  PLUS  { "+"  }
| MINUS { "-"  }
| STAR  { "*"  }
| SLASH { "/"  }
| GT    { ">"  }
| GTE   { ">=" }
| LT    { "<"  }
| LTE   { "<=" }
| EQUAL { "="  }

%inline literal:
  x=INT
{
  LInt x
}

%inline identifier: x=ID {
  Id x
}

%inline function_identifier: x=ID {
  Id x
}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
