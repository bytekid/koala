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

exception No_path_in_tr

val extend_one_bound : int -> clause list
val get_next_clauses_from_unsat_core : clause list -> int -> clause list * clause list

val prepare_model_tr : unit -> unit
val no_changes_in_next : TSet.t -> bool
val get_tr_predicates : Instantiation_env.inst_pre_model -> int -> TSet.t
val get_tr_from_model : Instantiation_env.inst_pre_model -> TSet.t -> int -> clause list

val has_new_next_segments : UnsatCore.unsat_core list -> bool
val clear_saved_assumptions : unit -> unit
val add_used_assumptions : term list -> unit

val print_transition_relation_size : unit -> unit
val clear_current_rel : int -> unit
val get_negative_assumptions : unit -> term list
val get_grounded_pos_assumptions : unit -> term list

(* get all the selected literals from the model *)
val get_model_literals : Instantiation_env.inst_pre_model -> term list

(* return [] or [lemma] *)
val get_lemma_by_uc : UnsatCore.unsat_core -> clause list

val set_full_rel : clause list -> unit
val get_cone_symb : unit -> clause list

val get_reduced_problem : unit -> clause list
val get_aig_pass_cone : unit -> clause list
val get_aig_restricted_cone : int -> clause list

val get_restricted_cone : int -> clause list
val max_depth_reached : int -> bool
