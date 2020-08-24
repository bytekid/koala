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

type k_induction_stage = IndBase | IndStep
val k_induction_stage_flip : k_induction_stage -> k_induction_stage
val stage_to_string : k_induction_stage -> string
type mc_phase = {
  mutable mc_cur_bound : int;
  mutable mc_alg_stage : k_induction_stage;
  mutable mc_deadlock_stay_base : bool;
}
val phase_to_string : mc_phase -> string
val get_initial_phase : unit -> mc_phase
type bmc_handlers = {
  mc_task_name : string;
  mc_update_phase : mc_phase -> unit;
  mc_after_sat : mc_phase -> unit;
  mc_after_unsat : mc_phase -> unit;
  mc_get_next_bound_axioms : mc_phase -> Logic_interface.clause list * Logic_interface.term list;
}
val cone_exclude_symbs : SSet.t ref

val print_clauses : string -> Clause.clause list -> unit
val current_task_name : unit -> string
val need_init_predicate : unit -> bool
val need_property_from_predicate : unit -> bool
val need_property_predicate : unit -> bool
val need_equal_to_predicate : unit -> bool
val need_equal_from_predicate : unit -> bool
val need_deadlock_predicate : unit -> bool
val address_type : Symbol.symbol
val state_type : Symbol.symbol
val bitindex_type : Symbol.symbol
val address_diff_symbol_name : string
val address_val_symbol_name : string
val address_symbol_name : string
val base_guard_symbol : string
val bound_symbol_format :
  (int -> string, unit, string, string, string, string) format6
val bitindex_symbol_format :
  (int -> string, unit, string, string, string, string) format6
val state_symbol_format :
  (int -> string, unit, string, string, string, string) format6
val var_n : Var.symbol -> int -> Var.var
val term_xn : Var.symbol -> int -> Logic_interface.term
val term_x0 : Var.symbol -> Logic_interface.term
val term_x1 : Var.symbol -> Logic_interface.term
val term_x2 : Var.symbol -> Logic_interface.term
val create_typed_equation :
  Logic_interface.symbol ->
  Logic_interface.term -> Logic_interface.term -> Logic_interface.term
val create_constant_term : string -> Symbol.symbol -> Logic_interface.term
val create_skolem_term :
  ('a -> string, unit, string, string, string, string) format6 ->
  Symbol.symbol -> 'a -> Logic_interface.term
val create_atom :
    ?is_special:bool ->
      string -> 
        Symbol.symbol list -> Logic_interface.term list -> Logic_interface.term
val create_atom_symb :
  Logic_interface.symbol -> Logic_interface.term list -> Logic_interface.term
val get_arg_types_list : Symbol.symbol -> Symbol.symbol list
val get_arg_var_list_of_types : Var.symbol list -> Logic_interface.term list
val get_arg_var_list : Symbol.symbol -> Logic_interface.term list
val create_state_term : int -> Logic_interface.term
val create_bound_atom : int -> Logic_interface.term
val create_bound_atom_list :
  Logic_interface.term list -> int -> int -> Logic_interface.term list
val create_step_guard : unit -> Logic_interface.term
val create_base_guard : unit -> Logic_interface.term
val create_base_assumption : unit -> Logic_interface.term
val create_step_assumption : unit -> Logic_interface.term
val create_full_r_guard : unit -> Logic_interface.term
val create_short_r_guard : unit -> Logic_interface.term
val create_full_r_assumption : unit -> Logic_interface.term
val create_short_r_assumption : unit -> Logic_interface.term
val create_bitindex_term : int -> Logic_interface.term
val create_bitvector_atom :
  string -> Logic_interface.term -> Logic_interface.term
val create_next_atom : term -> term -> term -> term
val create_auto_path_atom : term -> term -> term
val create_init_atom : term -> term -> term
val create_auto_init_atom : term -> term
val create_init_atom_b : int -> term
val create_property_atom : Logic_interface.term -> Logic_interface.term
val create_equal_state_atom :
  Logic_interface.term -> Logic_interface.term -> Logic_interface.term
val create_eligible_atom : Logic_interface.term -> Logic_interface.term
val create_deadlock_atom : Logic_interface.term -> Logic_interface.term
val create_address_diff_atom :
  Logic_interface.term ->
  Logic_interface.term -> Logic_interface.term -> Logic_interface.term
val create_address_val_atom :
  Logic_interface.term -> Logic_interface.term -> Logic_interface.term
val create_address_atom : Logic_interface.term -> Logic_interface.term
val create_path_atom : int -> term
val create_path_axiom : int -> Logic_interface.clause
val create_property_axiom : int -> Logic_interface.clause
val create_neg_property_axiom : int -> Logic_interface.clause
val create_guarded_init_axiom : int -> Logic_interface.clause
val create_neg_init_axiom : int -> clause
val create_non_equal_state_axiom : int -> int -> Logic_interface.clause

(* work with Cj *)
val get_next_state_consts : unit -> Term.Set.t
val rel_index_var : unit -> term

(* work with models *)

val get_model_lits : Instantiation_env.inst_pre_model -> use_clause:(clause -> bool) -> apply_grounding:bool -> Term.Set.t
