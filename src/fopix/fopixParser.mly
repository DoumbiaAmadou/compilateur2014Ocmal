%{

  open FopixAST

%}

%token VAL DEF IN END IF THEN ELSE EVAL UPPERSAND
%token PLUS MINUS STAR SLASH GT GTE LT LTE EQUAL
%token LPAREN RPAREN LBRACKET RBRACKET ASSIGNS COMMA SEMICOLON EOF
%token<int> INT
%token<string> ID

%right SEMICOLON
%nonassoc ASSIGNS
%nonassoc GT GTE LT LTE EQUAL
%left PLUS MINUS
%left STAR SLASH
%nonassoc LBRACKET

%start<FopixAST.t> program

%%

program: ds=definition* EOF
{
  ds
}
| error {
  let pos = Position.lex_join $startpos $endpos in
  Error.error "parsing" pos "Syntax error."
}

definition: VAL x=located(identifier) EQUAL e=located(expression)
{
  DefineValue (x, e)
}
| DEF f=located(function_identifier)
  LPAREN xs=separated_list(COMMA, identifier) RPAREN
  EQUAL e=located(expression)
{
  DefineFunction (f, xs, e)
}
| EVAL e=located(expression)
{
  DefineValue (Position.map (fun _ -> Id "_") e, e)
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
| VAL x=located(identifier)
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
| f=function_identifier
  LPAREN es=separated_list(COMMA, located(expression)) RPAREN
{
  FunCall (f, es)
}
| l=located(expression) b=binop r=located(expression) {
  FunCall (FunId b, [l; r])
}
| e=located(expression) LBRACKET i=located(expression) RBRACKET {
  FunCall (FunId "block_get", [e; i])
}
| e=located(expression)
  LBRACKET i=located(expression) RBRACKET
  ASSIGNS v=located(expression) {
  FunCall (FunId "block_set", [e; i; v])
}
| e1=located(expression) SEMICOLON e2=located(expression) {
  Define (Position.map (fun _ -> Id "_") e1, e1, e2)
}
| LPAREN e=expression RPAREN {
  e
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
| UPPERSAND f=function_identifier
{
  LFun f
}

%inline identifier: x=ID {
  Id x
}

%inline function_identifier: x=ID {
  FunId x
}

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
