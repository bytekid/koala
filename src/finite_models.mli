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

exception Unsatisfiable_fm_na (* unsatisfiable without assumptions specific to finite models *)

type input_sig 
type fm_state 
type domain 

val init_fm_state : clause list -> fm_state 

val cyclic_types : fm_state -> SSet.t
val non_cyclic_types : fm_state -> SSet.t

val get_flat_clauses : fm_state -> clause list
val get_non_flat_eq_axioms : fm_state -> clause list

val get_domain : fm_state -> domain 
val get_domain_size : domain -> int

val get_diseq_axioms : domain -> clause list 
val get_active_range_axioms : domain -> clause list 

(* get_domain_assumptions domain -> (assumptions_list, adjoint_assumptions_list) *)

val get_domain_assumptions : domain -> (lit list * lit list)

(* assign_fp_range domain new_range_bound fp *)

val assign_fp_range : domain -> int -> symbol -> unit

val assign_all_fp_ranges : domain -> int -> unit

(* let incr_fp_ranges domain fp_switch_pred_list =  *)  

val incr_fp_ranges : ?incr:int -> domain -> symbol list -> int (* returns number of changed ranges*)

val incr_domain_unsat_core : domain -> clause list -> unit

(*-----------*)
val add_lemmas : fm_state -> clause list -> unit 
val get_lemmas : fm_state -> clause list 
