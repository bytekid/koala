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


open Lib
open Logic_interface

exception PS_loop_time_out of int

val ps_full_loop : time_limit:float param -> clause list -> unit

(* ps_state is local and will be cleard automatically *)


(*
type prover_functions = {
    mutable inst_lazy_loop_body : (int ref -> int ref -> unit) param;
    mutable inst_add_clause : (clause -> unit) param;
    mutable inst_get_all_input_clauses : (unit -> clause list) param;
    mutable inst_clear_all : (unit -> unit) param;
    mutable res_discount_loop_exchange : (unit -> unit) param;
    mutable res_add_clause : (clause -> unit) param;
    mutable res_get_all_input_clauses : (unit -> clause list) param;
    mutable res_simplified_input : context param;
    mutable res_clear_all : (unit -> unit) param
  }

val create_provers : 
    inst_name_param:string Lib.param -> res_name_param:string Lib.param -> clause list -> prover_functions

val create_provers_current_options : clause list -> prover_functions
*)
(* can raise: exception PS_loop_time_out of int *)
(* 
val full_loop : prover_functions ->  time_limit:float Lib.param -> clause list ref -> unit

val provers_clear_and_remove_all : unit -> unit
val provers_clear_and_remove_top : unit -> unit

val clear_all_provers : prover_functions -> unit
*)


(*
val simplify_input : prover_functions -> clause list -> clause list
*)
