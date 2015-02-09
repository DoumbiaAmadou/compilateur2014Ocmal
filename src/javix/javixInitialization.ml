(** Register some compilers that have Javix as a target or source language. *)
let initialize () =
  Compilers.register "javix" "javix"
    (module Compilers.Identity (Javix) : Compilers.Compiler);
  Compilers.register "fopix"   "javix"
    (module FopixToJavix : Compilers.Compiler)
