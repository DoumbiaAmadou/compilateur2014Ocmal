.class public test
.super java/lang/Object

.method public static main([Ljava/lang/String;)V
   .limit stack 2
   ; push System.out onto the stack
   getstatic java/lang/System/out Ljava/io/PrintStream;
   ; launch our code and push the int result onto the stack
   invokestatic test/code()I
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
.limit locals 100
.limit stack 10000

.end method
