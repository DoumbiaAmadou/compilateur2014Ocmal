(** Compilers. *)

open Languages

(** A compiler translates programs from a source language
    into programs of a target language. *)
module type Compiler = sig

  module Source : Language
  module Target : Language

  type environment
  val initial_environment : unit -> environment

  val translate : Source.ast -> environment -> Target.ast * environment

end

(** Compiler implementations are stored in the following
    hashing table. *)
let compilers : (string * string, (module Compiler)) Hashtbl.t =
  Hashtbl.create 31

let register source target m =
  Hashtbl.add compilers (source, target) m

let get source target =
  try
    Hashtbl.find compilers (source, target)
  with Not_found ->
    Error.global_error
      "during compilation"
      "Sorry, there is no such compiler in flap."

(** There is an easy way to compile a language into itself:
    just use the identity function :-). *)
module Identity (L : Language) : Compiler = struct
  module Source = L
  module Target = L
  type environment = unit
  let initial_environment () = ()
  let translate x () = (x, ())
end
