open Lib
open Logic_interface

exception Impl_Unit of term

(* all_implied_lit lit: callects all lits implied by UP after asserting lit excluding lit itself *)
(* can raise Impl_Unit(lit) or Impl_Unit(compl_lit) if lit/compl_lit is implied without assumptions *)

val all_implied_lits : term  -> term list

(* TODO: extend *)
