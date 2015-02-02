%token BLOCKCREATE BLOCKGET BLOCKSET
%token UJUMP JUMP SWAP CJUMP OR GETVARIABLE
%token REMEMBER DEFINE UNDEFINE ADD MUL DIV SUB GT GTE LT LTE EQ EXIT
%token COLON EOF
%token<int> INT
%token<string> ID COMMENT LABEL

%start<StackixAST.t> program

%%

program: p=labelled_instruction* EOF
{
  p
}
| error {
  let pos = Position.lex_join $startpos $endpos in
  Error.error "parsing" pos "Syntax error."
}


labelled_instruction: l=label? i=located(instruction) {
  (l, i)
}

label: l=ID COLON {
  StackixAST.Label l
}

instruction:
  REMEMBER i=INT       { StackixAST.Remember i }
| REMEMBER i=LABEL     { StackixAST.RememberLabel (StackixAST.Label i) }
| DEFINE x=ID          { StackixAST.Define (StackixAST.Id x) }
| UNDEFINE             { StackixAST.Undefine }
| EXIT                 { StackixAST.Exit }
| ADD                  { StackixAST.Binop StackixAST.Add }
| SUB                  { StackixAST.Binop StackixAST.Sub }
| MUL                  { StackixAST.Binop StackixAST.Mul }
| DIV                  { StackixAST.Binop StackixAST.Div }
| GT                   { StackixAST.Binop StackixAST.GT }
| GTE                  { StackixAST.Binop StackixAST.GTE }
| LT                   { StackixAST.Binop StackixAST.LT }
| LTE                  { StackixAST.Binop StackixAST.LTE }
| EQ                   { StackixAST.Binop StackixAST.EQ }
| BLOCKCREATE          { StackixAST.BlockCreate }
| BLOCKGET             { StackixAST.BlockGet }
| BLOCKSET             { StackixAST.BlockSet }
| GETVARIABLE i=INT    { StackixAST.GetVariable i }
| JUMP l=ID            { StackixAST.Jump (StackixAST.Label l) }
| UJUMP                { StackixAST.UJump }
| SWAP                 { StackixAST.Swap }
| x=COMMENT            { StackixAST.Comment x }
| CJUMP l1=ID OR l2=ID { StackixAST.ConditionalJump
                         (StackixAST.Label l1, StackixAST.Label l2) }

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
