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



open Options
open Logic_interface

(*
type feature_list
val get_feature_list : clause -> feature_list
*)

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


type sim_state


(*
val sim_mem_bclause : sim_state -> clause ->  bool
*)

val sim_mem_clause : sim_state -> clause -> bool

(* sim_add_feat_clause sim_state feature_list_opt clause *)
(* if sim_use_sub_index=true then feature_list_opt=Some(feature_list) else None*)
(* can return clause that subset subsumes the given clause and the list of backward subsumed clauses *)
val sim_add_clause :  ?after_bwd_ss:bool -> sim_state -> clause -> clause * (clause list)

(* sim_create sim_options context_init_size *)
val sim_create : sim_options  -> sim_state 

(* new context is created; clauses may become dead during adding/not added due subsumption *)
(* val sim_create_from_context : sim_options -> context -> sim_state *)

(*
val sim_create_from_list : sim_options -> clause list -> sim_state
*)
(* in remove_from_indexes/assign_dead_and_remove_from_indexes *)
(* the context copy of the clause is removed, assigned_dead etc. *)


(*  if a module uses sim_state then one should always add clauses via sim_add_clause
                               otherwise clauses will not be added into simpl. indexes even at the next round *)
val sim_get_context : sim_state -> context

val sim_is_dead : sim_state -> clause -> bool

(*----- removes clause from sim_sate indexes (clause is not assigned is_dead) *)

val remove_from_indexes : sim_state -> clause -> unit

val assign_dead_and_remove_from_indexes : sim_state -> clause -> unit

val remove_from_indexes_and_context : sim_state -> clause -> unit

val remove_from_sub_index : sim_state -> clause -> unit

val add_to_sub_index : sim_state -> clause -> unit

val sim_state_num_clauses : sim_state -> non_dead:bool -> int


(* does not assign is_dead *)
(*
val remove_from_sim_state : sim_state -> clause -> unit
*)
(*
(* clauses are copied *)

val get_non_dead_clauses_list : sim_state -> clause list
*)

(*--- simplifications, can raise Eliminated, Empty_Clause *)


(* 1) self and forward simplifications can output new_clause that shoud be be added to the sim_state sparetely if needed *)
(* whether the clause is new should be checked by Clause.equal_basic_clause *)

(* 2) in backward simplifications subsumed clauses are removed and (copy of) the main clause is added to the sim_state automatically *)


val tautology_elim : clause -> clause

(* can not use eq_tautology elim with axiomtic equality! only  in preprocessing before eq axioms are added *)
val eq_tautology_elim : clause -> clause

val equality_resolution : clause -> clause

val equality_resolution_simp : clause -> clause

(* equality_resolution then tautology_elim; only use in preprocessing begore adding axioms of equality! *)
val self_simplify_prep : clause -> clause 

(* inconsistent with solver assumptions then raises Unsatisfiable_gr *)
val inconsistent_with_assumptions : clause -> unit

(*-- global subsume with prop. solver *)
val forward_prop_subsume : (* sim_state ->*) clause -> clause

val forward_subset_subsume :  sim_state -> clause -> clause

(* returns list of subsumed clauses; *)
val backward_subset_subsume : sim_state -> clause -> clause list

(* forward subset resolution *)
val forward_subs_res : sim_state -> clause -> clause

(* val forward_subs_feature : sim_state -> feature_list -> clause -> clause *)

val forward_subs :  ?pre_cond:(cl_in:clause ->cl_by:clause -> bool) -> sim_state -> clause -> clause 

val forward_subs_strict : sim_state -> clause -> clause 

(* val forward_subs : ?strict:bool -> sim_state -> clause -> clause *)
(* val forward_subs : sim_state -> clause -> clause*)

(* needs checking but should work
(* in forward_subs_by_length  we assume that the first feature is always length! *)
val forward_subs_by_length : sim_state -> feature -> feature_list -> clause -> clause
*)


(* backward_subs_res returns list of pairs (subsumed_clause list, new_clause)  *)
(* subsumed_clause is removed from indexes; declared dead; but remain in sim_sate *)	
(* new_clause are not added to sim_state and need to be added sparately *)

val backward_subs_res : sim_state -> clause ->  (clause list * clause) list

(* returns subsumed clauses; aut. removed from indexes in sim_state *)
val backward_subs_full : sim_state -> clause -> clause list

val backward_subs_by_length : sim_state -> int -> clause -> clause list

