(** This module offers a pretty-printer for Stackix programs. *)

open PPrint
open PPrintCombinators
open PPrintEngine

open JavixAST

let located f x = f (Position.value x)

let header p =
".class public "^ p.classname ^"
.super java/lang/Object

.method public static main([Ljava/lang/String;)V
   .limit stack 2
   ; push System.out onto the stack
   getstatic java/lang/System/out Ljava/io/PrintStream;
   ; launch our code and push the int result onto the stack
   invokestatic "^p.classname^"/code()I
   ; call the PrintStream.println() method.
   invokevirtual java/io/PrintStream/println(I)V
   ; done
   return
.end method

;;; box : int --> Integer

.method public static box(I)Ljava/lang/Integer;
.limit locals 1
.limit stack 3
   new java/lang/Integer
   dup
   iload 0
   invokespecial java/lang/Integer/<init>(I)V
   areturn
.end method

;;; unbox : Integer --> int

.method public static unbox(Ljava/lang/Integer;)I
.limit locals 1
.limit stack 1
   aload 0
   invokevirtual java/lang/Integer/intValue()I
   ireturn
.end method

;;; the compiled code

.method public static code()I
.limit locals "^string_of_int p.varsize^"
.limit stack "^string_of_int p.stacksize^"
"

let rec program p =
  string (header p) ^^ code p p.code ^^ hardline ^^
  string ".end method" ^^ hardline

and code p c =
  separate_map hardline (labelled_instruction p) c

and labelled_instruction p (l, i) =
  label l ^^ string (instruction p (Position.value i))

and label lab =
  string (match lab with None -> "" | Some (Label l) -> l^":\n") ^^
  string "\t"

and instruction p = function
  | Box -> "invokestatic "^p.classname^"/box(I)Ljava/lang/Integer;"
  | Unbox -> "invokestatic "^p.classname^"/unbox(Ljava/lang/Integer;)I"
  | Bipush c -> "bipush " ^ string_of_int c
  | Pop -> "pop"
  | Swap -> "swap"
  | Binop op -> binop op
  | Astore v -> "astore " ^ var v
  | Aload v -> "aload " ^ var v
  | Goto (Label lab) -> "goto " ^ lab
  | If_icmp (op,Label lab) -> "if_icmp"^cmpop op^" "^lab
  | Anewarray -> "anewarray java/lang/Object"
  | AAstore -> "aastore"
  | AAload -> "aaload"
  | Ireturn -> "ireturn"
  | Comment s -> ";; " ^ s
  | Tableswitch (i,labs,Label dft) ->
    let labs = List.map (function Label l -> l) labs in
    "tableswitch "^string_of_int i^"\n\t"^
    (String.concat "\n\t" labs)^
    "\n\tdefault: "^dft

and var (Var v) = string_of_int v

and binop = function
  | Add -> "iadd"
  | Mul -> "imul"
  | Div -> "idiv"
  | Sub -> "isub"

and cmpop = function
  | EQ  -> "eq"
  | NE  -> "ne"
  | LT  -> "lt"
  | LE  -> "le"
  | GT  -> "gt"
  | GE  -> "le"

let to_string f x =
  let b = Buffer.create 13 in
  ToBuffer.pretty 0.5 80 b (f x);
  Buffer.contents b
