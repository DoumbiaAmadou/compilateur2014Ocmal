%token ADD MUL DIV SUB IFEQ IFNE IFLT IFLE IFGT IFGE
%token PUSH POP SWAP BOX UNBOX
%token ASTORE AASTORE
%token ALOAD AALOAD
%token JUMP ANEWARRAY IRETURN TABLESWITCH DEFAULT
%token COLON EOF
%token<int> INT
%token<string> ID COMMENT

%start<JavixAST.t> program

%%

program: p=labelled_instruction* EOF
{
  { JavixAST.classname = "Flap";
    JavixAST.code = p;
    JavixAST.varsize = 100;
    JavixAST.stacksize = 10000
  }
}
| error {
  let pos = Position.lex_join $startpos $endpos in
  Error.error "parsing" pos "Syntax error."
}


labelled_instruction: l=label? i=located(instruction) {
  (l, i)
}

label: l=ID COLON {
  JavixAST.Label l
}

instruction:
  PUSH i=INT           { JavixAST.Bipush i }
| ADD                  { JavixAST.Binop JavixAST.Add }
| SUB                  { JavixAST.Binop JavixAST.Sub }
| MUL                  { JavixAST.Binop JavixAST.Mul }
| DIV                  { JavixAST.Binop JavixAST.Div }
| IFEQ l=ID            { JavixAST.If_icmp (JavixAST.EQ, JavixAST.Label l) }
| IFNE l=ID            { JavixAST.If_icmp (JavixAST.NE, JavixAST.Label l) }
| IFLE l=ID            { JavixAST.If_icmp (JavixAST.LE, JavixAST.Label l) }
| IFLT l=ID            { JavixAST.If_icmp (JavixAST.LT, JavixAST.Label l) }
| IFGE l=ID            { JavixAST.If_icmp (JavixAST.GE, JavixAST.Label l) }
| IFGT l=ID            { JavixAST.If_icmp (JavixAST.GT, JavixAST.Label l) }
| JUMP l=ID            { JavixAST.Goto (JavixAST.Label l) }
| POP                  { JavixAST.Pop }
| SWAP                 { JavixAST.Swap }
| ASTORE i=INT         { JavixAST.Astore (JavixAST.Var i) }
| AASTORE              { JavixAST.AAstore }
| ALOAD i=INT          { JavixAST.Aload (JavixAST.Var i) }
| AALOAD               { JavixAST.AAload }
| ANEWARRAY ID         { JavixAST.Anewarray }
| IRETURN              { JavixAST.Ireturn }
| BOX                  { JavixAST.Box }
| UNBOX                { JavixAST.Unbox }
| TABLESWITCH i=INT l=ID* DEFAULT COLON lab=ID
                       { let l = List.map (fun lab -> JavixAST.Label lab) l in
                         JavixAST.Tableswitch (i,l,JavixAST.Label lab) }
| x=COMMENT            { JavixAST.Comment x }

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
