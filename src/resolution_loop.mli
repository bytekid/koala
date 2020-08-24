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
open Resolution_env

type res_state

(* res_model: active clauses with params *)
type res_model = res_cl_param BCMap.t

exception Res_satisfiable of res_model

val res_create_state : res_prep_only:bool -> res_state 

val resolution_loop_exchange     :  res_state -> unit

val res_add_clause : res_state -> clause -> unit 

val res_add_clause_list : res_state -> clause list -> unit

(* assume state is created with res_prep_only:true; *)
(* the state is used only for preprocessing clauses *)
val res_preprocess : res_state -> clause list

(*val start_discount : clause list -> unit  *)

(* for combination with e.g. instantiation *)

(* run it once with all initial clauses incl. additional axioms*)
(*val init_discount_input_clauses : clause list -> unit *)




(* in order to get the proof we need to pass the empty clause *)

(*val sel_fun_type : Selection.res_sel_type ref *)


(* discount_loop_exchange act_to_exch_flag  pass_to_exch_flag *)
(* makes one discount loop iteration  *)
(* returns generated clauses: for exchange*) 
(* if act_to_exch_flag  is true and pass_to_exch_flag = false *) 
(* then return the clause added to active if any  *)
(* if pass_to_exch_flag is true then returns all clauses added to passive*)

(*val discount_loop_exchange     :  bool -> bool -> clause list *)

 
 (* val get_all_input_clauses : unit -> clause list *)

(* the clause should be fresh *)
(*(it's better to copy the clause to a new one before adding )*)
(*val add_inst_exchange_clause_to_passive : clause -> unit*)
(*
  val add_new_clause_to_passive  : clause -> unit
 *)

(*  val simplified_input : res_state -> context  

  val res_prep: res_state -> clause list
*)

(* unassigns all structures related to discount and runs GC.full_major*)
(*  val clear_all                  : unit -> unit *)


(*debug*)
(*
  val try_matching_all : unit -> unit
  val try_subsumption_all : unit -> unit
 *)
