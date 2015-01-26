(** Command line arguments analysis. *)

let options_list =
  ref []

let push local_options =
  options_list := !options_list @ local_options

let options names kind doc =
  let shortdoc =
    try String.sub doc 0 (String.index doc ' ') with Not_found -> doc
  in
  match names with
  | [] -> []
  | name::names ->
    (name,kind,doc)::(List.map (fun n -> (n,kind,shortdoc)) names)

let show_version_and_exits () =
  Printf.printf "flap %s\n%!" Version.number;
  exit 0

let generic_options = Arg.(align (List.flatten [
  options
    ["--version"; "-v"]
    (Unit show_version_and_exits)
    " Show the version number and exits.";

  options
    ["--source"; "-s"]
    (String Options.set_source_language)
    "<lang> Set the source programming language";

  options
    ["--target"; "-t"]
    (String Options.set_target_language)
    "<lang> Set the target programming language";

  options
    ["--interactive"; "-i"]
    (Unit (fun () -> Options.set_interactive_mode true))
    " Run the compiler in interactive mode";

  options
    ["--verbose"; "-V"]
    (Set Options.verbose_mode)
    " Ask the compiler to be verbose";

  options
    ["--dry"; "-d"]
    (Set Options.dry_mode)
    " Ask the compiler not to produce compiled file";

  options
    ["--unsafe"; "-u"]
    (Set Options.unsafe)
    " Ask the compiler not to typecheck";

  options
    ["--run"; "-r"]
    (Bool Options.set_running_mode)
    "(true|false) Ask the compiler to run the compiled code";

  options
    ["--bench"; "-B"]
    (Bool Options.set_benchmark)
    "(true|false) Ask the compiler to show evaluation time.";

]))

let usage_msg =
  "flap [options] input_filename"

let parse () =
  Arg.parse !options_list Options.set_input_filename usage_msg

let initialize =
  push generic_options
