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
 

(** Return a formatter for writing into the file given in the option
    --bmc1_dump_file **)
val get_bmc1_dump_formatter : unit -> Format.formatter


(** Return list of clause assumptions for given bound 

    Currently return just one unit clause with the activation literal
    for bound dependant clauses *)
val get_bound_assumptions : int -> Clause.clause list 

val get_current_bound_assumptions : int -> term list
(** Initialise BMC1 axioms from input clauses, return the axioms
    generated for bound 0 and the modified input clauses *)
val init_bound : Clause.clause list -> Clause.clause list * Clause.clause list

(** Add BMC1 axioms incrementing the bound from given current bound to
    given next bound. Difference between current and next bound must
    be 1.

    If lemmas flag is true, also add target(prev) to axioms

    If the boolean flag is true, the bound increment is only
    simulated, that is, the function has no side effects. Otherwise,
    the assumptions in the SAT solver are modified.

    TODO: Fix this to arbitrary bound increments 
let increment_bound cur_bound next_bound lemmas simulate =
*)
(* val increment_bound : int -> int -> bool -> bool -> Clause.clause list *)

val get_mc_handlers : unit -> Bmc1Common.bmc_handlers

(** For all axioms that are dependent on the previous bound return a
    list of clauses for the given bound. *)
val extrapolate_to_bound : int -> Clause.clause list -> Clause.clause list 

 (** pre_instantiate_state_var_clauses_range low_bound upper_bound clauses *)
val pre_instantiate_state_var_clauses_range : int -> int -> Clause.clause list -> Clause.clause list

val pre_inst_reachable_state_clauses : int -> clause list -> clause list


val change_gr_by_map_state : term -> unit
