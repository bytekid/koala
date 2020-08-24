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
open Bmc1Common
open AigWitness
open Logic_interface


(* AIG result output  *)
let aig_pref = AigCommon.aig_pref

(* report the UNSAT problem *)
let print_unsat () =
  out_str (aig_pref^"0\n"^aig_pref^"b0\n"^aig_pref^".")

(* get all terms of the form [~]P(c) from the model *)
let get_unary_terms model =

  (* get all selected ground literals *)
  let sel_lit_set = get_model_lits model ~use_clause:(fun c -> true) ~apply_grounding:false in
 
  (* keep only unary predicates *)
  let is_unary_predicate lit =
    let atom = Term.get_atom lit in
    let args = Term.arg_to_list (Term.get_args atom) in
    let n_args = List.length args in
    n_args = 1
  in
  let unary_predicates = TSet.filter is_unary_predicate sel_lit_set in
  List.partition Term.is_ground (TSet.elements unary_predicates)

let print_witness_simple model max_bound =
  (* map between bound constants and corresponding index *)
  let bound_const_index = ref TMap.empty in
  (* fill the map *)
  let rec fill_map index bound =
    match bound with
    | -1 -> ()
    | _ ->
      (* map from bound_n into index *)
      let bound_n = create_state_term bound in
      bound_const_index := TMap.add bound_n index !bound_const_index;
      (* repeat for smaller bound *)
      fill_map (succ index) (pred bound)
  in
  fill_map 0 max_bound;
  (* get lists of grounded and non-grounded selected literals *)
  let grounded, non_grounded = get_unary_terms model in
  (* get input vars out of those symbols *)
  let grounded_vars = List.filter AigClausifier.aig_is_input_pred grounded in
  let non_grounded_vars = List.filter AigClausifier.aig_is_input_pred non_grounded in
  (* put a default value from non-ground vars *)
  let process_default_value lit =
    let atom = Term.get_atom lit in
    (* symbol to write *)
    let value = if (Term.is_neg_lit lit) then '0' else '1' in
    let symb = Term.get_top_symb atom in
    (* write the value as a default for all states *)
    for i = 0 to max_bound do
      AigWitness.add_input_value i symb value;
    done
  in
  (* add a value of a model symbol to the coresponding line *)
  let process_model_symbol lit =
    let atom = Term.get_atom lit in
    let state = List.hd (Term.arg_to_list (Term.get_args atom)) in
    try
      (* get index out of the state const bound_N *)
      let index = TMap.find state !bound_const_index in
      (* symbol to write *)
      let value = if (Term.is_neg_lit lit) then '0' else '1' in
      let symb = Term.get_top_symb atom in
      (* set the value to the index (if appropriate) *)
      AigWitness.add_input_value index symb value;
      (* try to use the latch if possible *)
      if index = 0
      then AigWitness.add_latch_value symb value;
    with (* const is not a state const -- nothing to do *)
    | Not_found -> ()
  in
  (* process all default model symbols *)
  List.iter process_default_value non_grounded_vars;
  (* process all grounded model symbols *)
  List.iter process_model_symbol grounded_vars;
  (* that's it *)
  ()

let print_witness_inst inst_pre_model inst_pre_model_filtered_out max_bound =
  (* build an INST-based model first *)
  let model = Model_inst.build_model ~inst_pre_model ~inst_pre_model_filtered_out in
  (* build a model representation, using input vars *)
  let aig_model = Model_inst.get_aig_model ~is_relevant_pred:AigClausifier.aig_is_input_var model in
  (* explore all model *)
  for i = 0 to max_bound do
    let f symbol =
      (* extract a value of a symbol *)
      let value = Model_inst.get_aig_val aig_model i symbol in
      (* add this value to a model *)
      AigWitness.add_input_value i symbol value
    in
    (* apply to all vars *)
    List.iter f !AigClausifier.input_vars_list_ref
  done;
  (* that's it *)
  ()


(* choose that model to use *)
(* use_simple_witness = true is aig based by-passing general model construction;  should work *)
(* use_simple_witness = false is constructing general model and then extracting AIG part; needs fixing *)

let use_simple_witness = true

let print_witness ~inst_pre_model ~inst_pre_model_filtered_out max_bound =
  (* header: problem is SAT, witness for the output 0 *)
  out_str (aig_pref^"1\n"^aig_pref^"b0");
  (* make proper number of input vectors *)
  AigWitness.set_input_max_bound max_bound;
  (* output the state/input information *)
  if use_simple_witness
  then print_witness_simple inst_pre_model max_bound
  else print_witness_inst inst_pre_model inst_pre_model_filtered_out max_bound;
  (* everything is done here; just print all *)
  (* print initial state *)
  AigWitness.print_initial_state ();
  (* print model *)
  AigWitness.print_input_vectors ();
  (* print the end of the witness *)
  out_str (aig_pref^".");
  (* that's it *)
  ()
