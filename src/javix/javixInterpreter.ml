(** No interpreter of the Javix language:
    instead, we use the Jasmin program for turning our code into
    .class file, and then launch the real JVM virtual machine. *)

open JavixAST

let error msg =
  Error.global_error "javix execution" msg

type runtime = unit
type observable = unit

let initial_runtime () = ()

let evaluate runtime (ast : t) = (), ()

let print_observable runtime obs = ""
