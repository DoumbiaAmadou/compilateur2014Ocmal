let initialize () =
  Compilers.register "fopix" "fopix"
    (module Compilers.Identity (Fopix) : Compilers.Compiler);
