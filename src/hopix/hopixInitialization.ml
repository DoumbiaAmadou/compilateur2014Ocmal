let initialize () =
  Compilers.register "hopix" "hopix"
    (module Compilers.Identity (Hopix) : Compilers.Compiler);
  Compilers.register "hopix" "datix"
    (module HopixToDatix : Compilers.Compiler)
