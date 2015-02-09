let initialize () =
  Compilers.register "datix" "datix"
    (module Compilers.Identity (Datix) : Compilers.Compiler)
