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
open Options
open Logic_interface
open Proof_search_loop
open Problem_properties

type res_model = Resolution_loop.res_model
type inst_pre_model = Instantiation_env.inst_pre_model


exception Schedule_Terminated

(*------------------*)

type ps_result = 
  | PS_result_empty_clause of clause 
  | PS_result_resolution_sat of res_model * inst_pre_model (* res_model * filtered_out_inst_pre_model *)
  | PS_result_prop_solver_unsat 
  | PS_result_prop_solver_unsat_na (* unsat without assumtions *)
  | PS_result_instantiation_sat of inst_pre_model * inst_pre_model  (* inst_pre_model * filtered_out_inst_pre_model *)
  | PS_result_unsat_multiple_cores of UnsatCore.unsat_core list

val result_handler_basic : ps_result -> unit

val proved_str : unit -> string
(*val unknown_str : unit -> string *)
val satisfiable_str : unit -> string

(*------------------*)

type time = float param

type schedule = (named_options * time) list

(* proof_clauses/finite_model_clauses may be simplified and replaced during proof/model search *)

type schedule_clauses = 
    {

(* clauses used for proof search *)
     mutable proof_clauses : clause list; 

(* clauses used for finite model search  (equality may be missing) *)
     mutable finite_model_clauses : clause list;  

(* clauses removed by sem_filter; needed for model building*)
     mutable filtered_out_inst_pre_model : inst_pre_model;  

   }

val schedule_run : 
 (*   ?prover_functions_param:(Proof_search_loop.prover_functions Lib.param) -> *)  schedule_clauses -> schedule -> ps_result

val default_schedule : prob_props -> schedule

(* just runs input_named_options *)
val trivial_schedule : unit -> schedule

val verification_epr_schedule_old : unit -> schedule

val verification_epr_schedule_tables : unit -> schedule 

val verification_epr_schedule : unit -> schedule

val sat_schedule : prob_props -> schedule

val abstr_ref_schedule : prob_props -> schedule
val abstr_ref_sat_schedule : prob_props -> schedule


val smac_tmp_schedule : unit -> schedule
