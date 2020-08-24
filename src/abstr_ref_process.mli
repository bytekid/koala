(*----------------------------------------------------------------------(C)-*)
(*   This file is part of iProver - a theorem prover for first-order logic. *)
(*   see the LICENSE  file for the license                                  *)

open Lib

val ar_loop : time_limit:(float param) -> Options.abstr_ref_list_type -> Logic_interface.clause list -> unit
