(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2016 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 2 of the License, or 
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)


open Logic_interface
open Proof_search_loop 
open Proof_search_schedule


(* state of the MC process *)
type mc_state

val bmc1_input_transformation : unit -> unit

val result_handler_bmc1_preprocess : ps_result -> unit

val bmc1_init_solver_state : schedule -> schedule_clauses -> mc_state

val bmc1_loop : mc_state -> ps_result
val bmc1_mp_loop_init : mc_state -> ps_result
