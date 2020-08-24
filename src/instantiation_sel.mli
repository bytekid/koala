(*----------- solver/model based selection for instantiation_loop --------*)
(*------------------------- instantiation selection -----------------------*)
(* first arg is a func. which  *)
(* chooses candidate literals from the clause i.e. true in a model *)

open Logic_interface
open Instantiation_env

exception Activity_Check (* not yet on *)

val inst_selection : clause -> lit
val sel_consistent_with_solver : inst_cp -> bool
