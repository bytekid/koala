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

type prop_lit = PropSolver.lit

(*------------Parameters that can be changed by other modules-----------*)

(* should be run before first use of prop_solver_exchange! *)
val init_solver_exchange : unit -> unit

(* can raise PropSolver.Unsatisfiable  when trivially unsat *)
val add_clause_to_solver : clause -> unit

(* solve with asssigned assumptions; soft assumptions and extra_assumptions *)
(* in extra_assumptions are fof lits, lits are not grounded before transforming to prop *)
(* (use get_grounded_lit  to get grounding of the lit if needed) *)
val solve : ?solver_in:PropSolver.solver -> ?soft:bool -> ?reset:bool -> ?extra_assumptions:lit list -> unit -> PropSolver.solver_out

val fast_solve : ?solver_in:PropSolver.solver ->  ?soft:bool -> lit list -> PropSolver.fast_solve

(** *)
val solver : PropSolver.solver
val solver_sim : PropSolver.solver
val solver_uc : PropSolver.solver_uc


(** Return an unsatisfiable core *)
(** last call to solve should be unsat with exactly the same extra_assumptions and soft flag *)
val get_unsat_core : soft:bool -> ?extra_assumptions:lit list -> unit -> UnsatCore.unsat_core

(* lit is not grounded before transforming to prop *)

val get_solver_lit_val : lit -> bool

(* val after grounding*)
val get_solver_lit_val_gr : lit -> bool

(* try to make lit vals true in the solver: true if success/false otherwise *)
val preserve_lits_vals_solver : ?soft:bool -> lits -> bool 
val preserve_lits_vals_solver_gr : ?soft:bool -> lits -> bool

(* returns None if success and Some(UnsatCore.unsat_core) if unsat under lits *)
(*
val preserve_lits_vals_solver_uc : lits -> UnsatCore.unsat_core option
val preserve_lits_vals_solver_gr_uc : lits -> UnsatCore.unsat_core option
*)
(*------- assumptions -------*)
val assign_solver_assumptions : term list -> unit
val assign_only_sim_solver_assumptions  : term list -> unit
val assign_only_norm_solver_assumptions : term list -> unit

val assign_sim_adjoint_lits     : term list -> unit
val add_sim_adjoint_lits : term list -> unit
val rm_sim_adjoint_lits : term list -> unit

(*let add_solver_assumptions ?(only_norm=false) ?(only_sim=false) ?(soft=false) ?(answer=false) lit_list =    *)

val add_solver_assumptions :  ?only_norm:bool -> ?only_sim:bool -> ?soft:bool -> ?answer:bool -> lits -> unit 

(* mem includes norm and soft *)
val mem_assumptions : term -> bool 

(* there are no norm nor soft assumptinos *)
val is_empty_assumptions : unit -> bool

(** Return literal assumptions for satisfiability solver *)
(* val get_assumptions_sat : unit -> term list *)

(** Return literal assumptions for simplification solver *)
(* val get_assumptions_sim : unit -> term list *)

(* return current assumtions; if sim true then sim solver assumptions otherwise normal solver assumptions *)
val get_solver_fof_assumptions : soft:bool -> sim:bool -> TSet.t


(* can raise Not_found *)
val get_next_implied_unit : unit -> term 

(* only make call to one of the "newly_implied" functions below *)
val get_all_newly_implied_lits : is_relevant:(term->bool)  -> term list
val get_all_newly_implied_unit_clauses : is_relevant:(term->bool) -> clause list
val get_all_impl_lits : unit -> TSet.t

(* can raise Not_found *)
val get_next_ass_implied_unit : solver_in:PropSolver.solver -> term 

(*--------------*)


(*exception Non_simplifiable*)
val prop_subsumption : (* context param -> *) clause -> clause 


(** Return a justification for propositional subsumption of the
    clause.

    The justification is a set of clauses, lifted from a minimal
    unsatisfiable core, that propositionally subsume the given
    clause. Only clauses whose propositional id is less or equal to
    the id given are considered as justifications, hence the
    justification can be done in retrospect. 
*)
val justify_prop_subsumption : int -> clause -> clause -> clause list 


(** Return the grounding of the clause with a TSTP source statement
    that documents the grounding, in particular the binding of the
    clause's variables.
*)
val ground_clause : clause -> clause


(*------*)
type gr_map = term Symbol.Map.t

val get_gr_by_map : unit -> gr_map
val change_gr_by_map : gr_map -> unit 

val init_gr_by : unit -> unit

val get_grounded_lit : lit -> lit 

(* replaces term associated with a prop lit with a new term; used e.g. after subtyping *)
val apply_prop_lit_to_fof : (term -> term) -> unit

(*------*)

val out_mem : unit -> unit


(*-------- bmc mode ------*)
val unsat_cores: UnsatCore.unsat_core list ref
exception MultipleUnsat of UnsatCore.unsat_core list
val set_max_unsat_cores_number : int -> unit
val reset_uc_session_timer : unit -> unit
val init_multiple_run_mode : term list -> term list -> unit
val clear_multiple_run_mode : unit -> unit
val process_unsat_result : ?soft:bool -> unit -> unit
val process_final_sat_result : unit -> unit
val set_soft_assumptions : term list -> unit
val add_soft_assumptions : term list -> unit 
val mem_soft_assumptions : term -> bool
val clear_soft_assumptions : unit -> unit

val remove_solver_assumptions : ?soft:bool -> ?answer:bool -> lit list -> unit
val soft_assumptions_is_empty : unit -> bool
val is_empty_model : unit -> bool




(* assign_new_grounding vtype gr_term  does not work since all terms are associated with a gronding and reasssigning breaks things...*)

(*
val assign_new_grounding : symbol ->  term -> unit
*)


(*val solver_assumptions_ref : (PropSolver.lit list) ref*)

(* solver assumptions are used for finite models *)


(*----------------- not tested/re-check  -----------*)

(* fully resets solver and removes all clauses; keeps variables *)
(* reset_solvers is not tested *)
val reset_solvers : unit -> unit 

(* set_decision_var is_decision literal: *)
(* if is_decision is false then in prop solvers variable corresponding to atom of this literal *)
(* is not used decisions; can change sematics of SAT *)
val set_decision_var : bool -> literal -> unit

(* assigns decision function which is applied each time a prop clause is created *)
val set_decision_var_test_hook : (literal -> bool) -> unit

(* assume solver is unsat*)
val out_answer : unit -> unit


(*--------  revisit ----------*)

(* clear_model should be called after each time instantiation loop is finished *)
(* model conatins clauses from active associated with the selected literal which needs to be cleared for the next instantiation loop *)
val clear_model : unit -> unit

val clear_model_and_move_to_passive : (Clause.clause -> unit) -> unit

val lit_activity_threshold :  int ref 


(*-----------------------------------*)

type var_entry
val get_prop_gr_var_entry : term -> var_entry
val get_prop_var_entry : term -> var_entry
val get_prop_var_var_entry : var_entry -> prop_lit
val get_prop_neg_var_var_entry : var_entry -> prop_lit

val get_var_entry_truth_val : var_entry -> PropSolver.lit_val param
val set_var_entry_truth_val : var_entry -> PropSolver.lit_val Lib.param -> unit
val get_var_entry_truth_val_def : var_entry -> PropSolver.lit_val
val get_var_entry_pos_activity : var_entry -> int
val get_var_entry_neg_activity : var_entry -> int


(*val fast_solve_main : unit -> PropSolver.fast_solve*)
