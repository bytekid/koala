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
open Options
open Bmc1Common


(* create a definition of $$eligibleDeadlock(S), i.e.*)
(* p1(S)/\.../\~q1(S)/\...->eligible(S), or *)
(* {~p1(S),...,~p_n(S),q1(S),...,q_m(S),eligible(S)}, where*)
(* p_i(S) has deadlock_state_val=1 and q_i(S) =0 *)
let get_eligible_predicate_terms predicates =
  (* get list of predicates that are in the given set *)
  let get_predicates_from_set predicates set =
    (* test whether a predicate is a member of a set *)
    let is_in set p = Symbol.Set.mem p set in
    (* keep only those predicates that are members of a set *)
    let members = List.filter (is_in set) predicates in
    (* return the members *)
    members
  in
  (* positive and negative eligible predicates *)
  let pos_predicates = get_predicates_from_set predicates !Parser_types.pos_deadlock_name_set in
  let neg_predicates = get_predicates_from_set predicates !Parser_types.neg_deadlock_name_set in
  (* create S *)
  let state = term_xn state_type 0 in
  (* create P(S,x) *)
  let create_pos_p_atom state p =
    (* create vector of free variables x *)
    let x = get_arg_var_list p in
    (* create P(S,x) *)
    let ps_atom = create_atom_symb p (state :: x) in
    (* return that atom *)
    ps_atom
  in
  (* create ~P(S,x) *)
  let create_neg_p_atom state p =
    let ps_atom = create_pos_p_atom state p in
    add_compl_lit ps_atom
  in

  (* create literals by predicates *)
  let pos_lits = List.rev_map (create_neg_p_atom state) pos_predicates in
  let neg_lits = List.rev_map (create_pos_p_atom state) neg_predicates in
  (* return those literals *)
  pos_lits @ neg_lits

let create_eligible_definition literals =
  (* create a literal $$eligible(S) *)
  let state = term_xn state_type 0 in
  let eligible_lit = create_eligible_atom state in
  (* TSTP source: FORNOW *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom 0) in
  (* create clause {\/ p(S), \/~q(S), eligible(S)} *)
  let clause = create_clause tstp_source (eligible_lit :: literals) in
  (* create an axiom only if there are some literals *)
  let definition =
    if list_is_empty literals
    then []
    else [clause]
  in
  (* return that list *)
  definition

(* define the predicate $$deadlock(S) and all the surroundings *)
let bmc1_add_deadlock_predicate clauses =
  assert (list_non_empty !Bmc1Equal.state_predicates);
  (* define $$eligble(S) *)
  let eligible_lits = get_eligible_predicate_terms !Bmc1Equal.state_predicates in
  let eligible_clauses = create_eligible_definition eligible_lits in
  if val_of_override !current_options.bmc1_verbose
  then print_clauses "in eligible deadlock definition" eligible_clauses;
  (* define $$deadlock(S) *)

  (* FIXME!! think about empty eligible *)
  (* let has_eligible = (list_non_empty eligible_lits) in *)

  (* return all those clauses *)
  eligible_clauses
