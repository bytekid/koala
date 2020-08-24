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

(* dbg version of simplify.ml *)


open Lib
open Options
open Statistics
open Logic_interface 

let _ = out_str "\n\n warning simplify dbg; replace with sanbox/restructure_2016_10/simplify.ml \n\n"

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  |D_trace

let dbg_gr_to_str = function 
  |D_trace -> "trace"

let dbg_groups =
  [
   D_trace;
 ]

let module_name = "simplify_dbg"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
  
(*----- debug -----*)


type sim_options = 
  {

(*   sim_copy_clauses : bool; *)
   (* if  sim_copy_clauses=true then a fresh copy of a clause is created before adding into the context *)
   (* this is needed if the same clause is used in different contexts with separate indexes  *)
   (* since clause paremeters such as ss index are set during adding into the sim_state *)

   sim_add_to_prop_solver            : bool;
   sim_use_ss_index                  : bool;
   sim_use_sub_index                 : bool; 
   sim_add_to_sub_index_test         : clause -> bool; (* tests whether clause should be added to subs index *)
 }


type sim_state = 
    {
     sim_context : context;
   }

let get_sim_state_clause sim_state clause = 
  context_find sim_state.sim_context clause

let sim_get_context sim_state = 
  sim_state.sim_context

let sim_is_dead sim_state c = 
  Clause.get_is_dead sim_state.sim_context c


let sim_mem_clause sim_state c = 
  context_mem sim_state.sim_context c


let sim_add_clause ?(after_bwd_ss=false) sim_state clause = 
  check_empty_clause clause;
  let added_clause = context_add sim_state.sim_context clause in 
  (added_clause,[])

let sim_create opts =  
 let sim_context = context_create () in 
 {
  sim_context = sim_context;
}
   
let remove_from_indexes sim_state clause = ()

let assign_dead_and_remove_from_indexes sim_state clause = ()
(*  Clause.assign_is_dead sim_state.sim_context true clause *)
    
let remove_from_indexes_and_context sim_state clause = 
  context_remove sim_state.sim_context clause
    
let remove_from_sub_index sim_state clause = ()

let add_to_sub_index sim_state clause = ()
    
let tautology_elim clause = clause
let eq_tautology_elim  clause = clause
let equality_resolution clause = clause
let equality_resolution_simp clause = clause
let self_simplify_prep clause = clause
let forward_prop_subsume clause = clause
let forward_subset_subsume sim_state clause = clause 
let backward_subset_subsume sim_state clause = []
let forward_subs_res sim_state clause = clause 
let forward_subs sim_state clause = clause 
let backward_subs_res sim_state clause = []
let backward_subs_full sim_state clause = []
let backward_subs_by_length sim_state i clause = [] 

