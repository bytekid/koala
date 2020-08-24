(*----------------------------------------------------------------------(C)-*)
(*   This file is part of iProver - a theorem prover for first-order logic. *)
(*   see the LICENSE  file for the license                                  *)

open Lib
open Options
open Logic_interface

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

let module_name = "abstr_ref_process"

(*----- debug fixed part --------*)
let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  dbg_env_set dbg_flag dbg_groups group f

(* ****************************** *)

let clear_solver_assumptions state = (* used after solving is finished *)
  let assumptions = TSet.elements (Abstr_ref.get_all_assumptions state) in
  Prop_solver_exchange.remove_solver_assumptions assumptions

let estimate_time_limit ~start_time ~time_limit =
  match time_limit with
  | Undef -> Undef
  | Def time_limit ->
    let used_time = (Unix.gettimeofday ()) -. start_time in
    let estimate_time_limit =  time_limit -. used_time in
    Def(estimate_time_limit) (* can be negative *)

let rec abstr_ref_procedure time_limit abstraction state =
  let start_time = Unix.gettimeofday () in
  let left_time = estimate_time_limit ~start_time ~time_limit in
  try
    Statistics.incr_int_stat 1 Statistics.abstr_arg_filter_cycles;
    Prop_solver_exchange.clear_soft_assumptions ();
    (* dbg D_trace(lazy ("\n\n\t -+-+-> all assumptions: " ^
     *                   (Term.term_list_to_string (TSet.elements (
     *                        Prop_solver_exchange.get_solver_fof_assumptions ~soft:false ~sim:false))
     *                   ))); *)
    let all_clauses =
      if !current_options.abstr_ref_prep then(
        let clauses_before_prep = Abstr_ref.get_all_clauses state in
        let prep_state =
          Preprocess.prep_create_state ~clause_list:(CSet.elements clauses_before_prep)
            ~extra_side_atoms:[] (*(List.map Term.get_atom ar_all_assumptions_list) *)
        in
        (* TODO: fix add inst_pre_model *)
        Preprocess.preprocess_sim ~before_eq_axioms:false prep_state;
        Preprocess.prep_get_clauses prep_state
      )
      else
        CSet.elements (Abstr_ref.get_all_clauses state)
    in
    (* dbg D_trace(lazy ("\n\n\t**** all input clauses for ps_full_loop *****"));
     * dbg D_trace(lazy (Clause.clause_list_to_string all_clauses)); *)
    Proof_search_loop.ps_full_loop ~time_limit:left_time all_clauses;
    state
  with
  | Unsatisfiable_gr_na ->
    clear_solver_assumptions state;
    raise Unsatisfiable_gr_na
  | Unsatisfiable_gr ->
    assert (Prop_solver_exchange.soft_assumptions_is_empty ());
    let uc = Prop_solver_exchange.get_unsat_core ~soft:false () in
    let uc_assumptions = UnsatCore.get_assumptions uc in
    let uc_ass_set = TSet.of_list uc_assumptions in
    let all_ass_set = Abstr_ref.get_all_assumptions state in
    let swp_assumptions = TSet.inter uc_ass_set all_ass_set in
    clear_solver_assumptions state;
    let current_state =
      if TSet.is_empty swp_assumptions (* trivial refinement *)
      then(
        if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
        then raise Unsatisfiable_gr
        else failwith "abstr_ref_procedure: should be unsat")
      else(
        if !current_options.abstr_ref_until_sat
        then(
          let until_sat_state = Abstr_ref.refine_until_sat state swp_assumptions in
          try
            abstr_ref_procedure left_time abstraction until_sat_state
          with
          | Instantiation_loop.Inst_satisfiable _
          | Resolution_loop.Res_satisfiable _ ->
            Abstr_ref.state_after_until_sat until_sat_state
        )
        else Abstr_ref.refine state swp_assumptions
      )
    in
    abstr_ref_procedure left_time abstraction current_state
  | Proof_search_loop.PS_loop_time_out(full_loop_counter) ->
    clear_solver_assumptions state;
    raise (Proof_search_loop.PS_loop_time_out(full_loop_counter))
  |x ->
    clear_solver_assumptions state;
    raise x

let rec ar_rec_loop ~time_limit ~ar_type_list_input state =
  match ar_type_list_input with
  | [abstr] ->
    let current_state = Abstr_ref.apply_abstraction abstr state in
    abstr_ref_procedure time_limit abstr current_state
  | hd_abstr :: tl_abstrs ->
    let abstr_state = Abstr_ref.apply_abstraction hd_abstr state in
    (
      try
        ar_rec_loop ~time_limit ~ar_type_list_input:tl_abstrs abstr_state
      with
      | Unsatisfiable_gr ->
        let inner_state = abstr_ref_procedure time_limit hd_abstr abstr_state in
        ar_rec_loop ~time_limit ~ar_type_list_input:tl_abstrs inner_state
    )
  | _ -> failwith "Abstractions list is empty"

let ar_loop ~time_limit abstr_ref_type_list cl_input =
  let state = Abstr_ref.init_ar_env cl_input in
  ignore(ar_rec_loop ~time_limit ~ar_type_list_input:abstr_ref_type_list state)
