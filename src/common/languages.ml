module type Language = sig

  (** {1 Syntax} *)

  (** A syntax is defined by the type of abstract syntax trees. *)
  type ast

  (** [parse_filename f] turns the content of file [f] into an
      abstract syntax tree if that content is a syntactically valid
      input. *)
  val parse_filename : string -> ast

  (** Each language has its own extension for source code filenames. *)
  val extension : string

  (** [parse_string c] is the same as [parse_filename] except that the
      source code is directly given as a string. *)
  val parse_string : string -> ast

  (** [print ast] turns an abstract syntax tree into a human-readable
      form. *)
  val print_ast : ast -> string

  (** {2 Semantic} *)

  (** A runtime environment contains all the information necessary
      to evaluate a program. *)
  type runtime

  (** In the interactive loop, we will display some observable
      feedback about the evaluation. *)
  type observable

  (** The evaluation starts with an initial runtime. *)
  val initial_runtime : unit -> runtime

  (** [evaluate runtime p] executes the program [p] and
      produces a new runtime as well as an observation
      of this runtime. *)
  val evaluate : runtime -> ast -> runtime * observable

  (** [print_observable o] returns a human-readable
      representation of an observable. *)
  val print_observable : runtime -> observable -> string

  (** {3 Static semantic} *)

  type typing_environment

  val initial_typing_environment : unit -> typing_environment

  val typecheck : typing_environment -> ast -> typing_environment

end

(** We store all the language implementations in the following
    hashing table. *)
let languages : (string, (module Language)) Hashtbl.t =
  Hashtbl.create 13

let get_language l =
  try
    Hashtbl.find l languages
  with Not_found -> Error.global_error "There is no such language."

let add_language l m =
  Hashtbl.add languages l m
