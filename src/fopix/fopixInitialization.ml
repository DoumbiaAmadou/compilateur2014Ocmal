let initialize () =
  Compilers.register "fopix" "fopix"
    (module Compilers.Identity (Fopix) : Compilers.Compiler);
  Compilers.register "datix" "fopix"
    (module DatixToFopix : Compilers.Compiler)
