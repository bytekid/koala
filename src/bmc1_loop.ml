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
open Options
open Statistics 
open Logic_interface
open Proof_search_loop
open Proof_search_schedule
open Bmc1Common 

let dbg_flag = false

type dbg_gr = 
  | D_axs_init
  | D_trace
  | D_input_clauses
  | D_result_after_each_check
  | D_preprocess_extra
  | D_incremental_clauses
  | D_print_uc
  | D_lemmas
  | D_model
  | D_solver_input_smart
  | D_solver_input_smart_full
  | D_mem
  | D_tr_pred
  | D_timer
      
let dbg_gr_to_str = function 
  | D_axs_init  ->  "axs_init"
  | D_trace -> "trace"
  | D_input_clauses -> "input_clauses"
  | D_result_after_each_check -> "result_after_each_check"
  | D_preprocess_extra -> "preprocess_extrapolated"
  | D_incremental_clauses -> "incremental_clauses"
  | D_print_uc -> "print unsat core"
  | D_lemmas -> "lemmas"
  | D_model -> "model"
  | D_solver_input_smart -> "solver_input"
  | D_solver_input_smart_full -> "solver_input_full"
  | D_mem -> "mem"
  | D_tr_pred -> "tr_pred"
  | D_timer -> "timer"

let dbg_groups =
  [
   D_axs_init;
   D_trace; 
    (* D_lemmas; *)
   (* D_solver_input_smart; *)
   (* D_solver_input_smart_full; *)
   (* D_mem; *)
   (* D_model; *)
(*  D_print_uc; *)
   D_input_clauses; 
   (* D_preprocess_extra;   *)
   D_incremental_clauses;
   D_tr_pred; 
 ]
    
let module_name = "bmc1_loop"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

let print_mem name v =
  dbg_env D_mem 
    (
     fun () ->
       (
	out_basic_mem ();
	print_objsize name v
       )
    )


(*
	let i = Objsize.objsize v in
	printf "%S : data_words=%i headers=%i depth=%i;   \
    bytes_without_headers=%i bytes_with_headers=%i\n%!"
    title i.Objsize.data i.Objsize.headers i.Objsize.depth
    (Objsize.size_without_headers i)
    (Objsize.size_with_headers i)
*)

let out_model all_clauses filtered_out_clauses = 
  out_str ("\n -------- Model ---------\n \n");
  
  if (not (!current_options.sat_out_model = Model_None))
  then
    let model =
      Model_inst.build_model ~inst_pre_model:all_clauses ~inst_pre_model_filtered_out:filtered_out_clauses in
    Model_inst.out_model model
  else ()
      

(* state of the MC process *)
type mc_state = {
  mc_phase : mc_phase;
  mc_handlers: bmc_handlers;
  mutable mc_assumptions: lit list;
  mutable mc_unsat_core: clause list;
  mutable mc_accum_uc: clause list;
  mutable mc_extrapolation: clause list;
  mutable mc_accum_extrap: clause list;
  mutable mc_new_clauses: clause list;
  mutable mc_accum_new: clause list;
  mutable mc_bound_init_clauses : clause list;
  mutable mc_init_clauses : clause list;
  mutable mc_clauses : clause list;
  mc_full_problem: clause list;
  mc_schedule : Proof_search_schedule.schedule;
  mc_schedule_clauses : Proof_search_schedule.schedule_clauses;
}
  
(* Get value of maximal bound *)
let get_max_bound () = max
    (val_of_override !current_options.bmc1_max_bound)
    (val_of_override !current_options.bmc1_max_bound_default)
    
let out_bmc1_result handlers phase result =
  Format.printf
    "@\n%s %s %s %s after %.3fs@\n@."
    pref_str
    handlers.mc_task_name
    (phase_to_string phase)
    result
    (truncate_n 3 (Unix.gettimeofday () -. iprover_start_time))

let bmc1_progress str state =
  out_str ("\nPerforming "^str^" for bound "^(string_of_int state.mc_phase.mc_cur_bound))

(*---------------------------------------------*)    
let out_bmc1_unsat_result handlers phase = out_bmc1_result handlers phase "UNSAT"
let out_bmc1_sat_result handlers phase = out_bmc1_result handlers phase "SAT"

(* the SAT solver is unsatisfiable without any assumption. E.g., empty *)
(* clause in the input. Report this properly for every reasoning task *)

let bmc1_unsat_no_assumptions_out handlers phase =
  (* report the main issue *)
  out_bmc1_unsat_result handlers phase;
  (* get the bound *)
  let current_bound = phase.mc_cur_bound in
  out_str "The input is Unsatisfiable without assumptions\n";
  (* print the message corresponding to the task *)
  if !current_options.bmc1_k_induction
  then 
    Format.printf "@\n%sProved at bound %d@\n@\n@." pref_str current_bound
  else 
    if !current_options.bmc1_deadlock
    then Format.printf "@\n%sDeadlock would not be found from bound %d on@\n@\n@." pref_str current_bound
    else (* normal and lemma-based BMC1 *)
      Format.printf "@\n%sUnsatisfiable at every bound from %d on@\n@\n@." pref_str current_bound;
  (* print the unsat core *)
  (* let uc = Prop_solver_exchange.get_unsat_core () in *)
  (* UnsatCore.print uc;                                *)
  (* assign current bound *)
  assign_int_stat current_bound bmc1_current_bound;
  (* Assign last solved bound in statistics *)
  assign_int_stat current_bound bmc1_last_solved_bound


let result_handler_bmc1_preprocess result = 
  match result with 
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat| PS_result_prop_solver_unsat_na
    -> 
      bmc1_unsat_no_assumptions_out (Bmc1Axioms.get_mc_handlers ()) (get_initial_phase ())
	
  | PS_result_instantiation_sat (_inst_pre_model, _filtered_out) -> 
      failwith "bmc1 PS_result_instantiation_sat should not happen at the preprocessing stage"

  | PS_result_resolution_sat (_res_model, _filtered_out)
    ->   
      failwith "bmc1 PS_result_resolution_sat should not happen at the preprocessing stage"

  | PS_result_unsat_multiple_cores _ ->
    failwith "bmc1 Multiple usat cores during instantiation should not happen here"

(*---------------------------------------------*)    
(* tsar: add/modify input axioms for different MC needs *)
let bmc1_input_transformation () =
  (* replace raw input with init/property predicates if necessary *)
  if Bmc1Common.need_init_predicate () || Bmc1Common.need_property_predicate ()
  then
    Bmc1InitTarget.bmc1_add_init_and_property ();

  (* tsar: all clauses from the parser *)
  let all_clauses = Parser_types.get_clauses_without_extra_axioms () in
  (* generate equal definition if necessary *)
  let equal_clauses = Bmc1Equal.bmc1_define_equal_predicate all_clauses in
  (* generate deadlock definition if necessary *)
  let deadlock_clauses =
    if Bmc1Common.need_deadlock_predicate ()
    then Bmc1Deadlock.bmc1_add_deadlock_predicate all_clauses
    else []
  in
  let new_parsed_clauses = List.rev_append deadlock_clauses (List.rev_append equal_clauses all_clauses) in
  dbg D_input_clauses (lazy ("bmc1_input_transformation"));
  dbg D_input_clauses (lazy (Clause.clause_list_to_string new_parsed_clauses));
  Parser_types.parsed_clauses := new_parsed_clauses

(*---------------------------------------------*)

(* TODO: adapt to current state of BMC *)

(*
let bmc1_init_bound_clauses input_clauses = 

  assert (val_of_override !current_options.bmc1_incremental);

  (* when state vars pre-instantiation is on clauses in bmc1_for_pre_inst_cl *)
  (* contain origianal clauses which are needed to be instantiated *)

  let bmc1_for_pre_inst_cl = ref [] in (* assigned later*)

  (* Override default value of maximal bound from file *)	

  (try 
    
    (* Get cardinality of state_type *)
    let max_bound =
      pred
	(Symbol.Map.find
	   Symbol.symb_ver_state_type
	   !Parser_types.cardinality_map)
    in
        
    !current_options.bmc1_max_bound <-
      override_file max_bound !current_options.bmc1_max_bound
	
	(* Cardinality not defined, then no upper bound *)
  with Not_found -> ()      
  );
  	  
  (* Return axioms for all bounds from [i] to [n] *)
  let rec skip_to_bound accum n i =      

    (* Axioms for all bounds added? *)
    if (i >= n) 
    then	    
      (* Return axioms *)
      accum		
    else	      
      (	(* Add axioms for next bound *)
	let next_bound_axioms =
	  Bmc1Axioms.increment_bound i (succ i) false
	in
	
	(* Output next bound *)
	Format.printf
	  "%s Incrementing %s bound to %d@\n@."
	  (pref_str)
	  (current_task_name())
	  (succ i);
	
	(* Save next bound as current *)
	bmc1_cur_bound := succ i;
	
	(* Recurse until all axioms for all bounds added *)
	skip_to_bound
	  (next_bound_axioms @ accum)
	  n
	  (succ i)
       )	      
  in
  
  (* Create clauses for initial bound *)
  let bmc1_init_bound_axioms, clauses_after_init_bound =
    Bmc1Axioms.init_bound input_clauses
  in
  
  out_str
    (Format.sprintf
       "%sAdded initial %s axioms@\n"
       pref_str (current_task_name()));
	
  (* Add axioms from bound 0 to starting bound *)
  let bmc1_axioms_for_all_bounds =
    if !current_options.bmc1_k_induction || !current_options.bmc1_deadlock
    then 
      bmc1_init_bound_axioms @ (get_next_bound_axioms ())
    else
      skip_to_bound
	init_bound
	(val_of_override !current_options.bmc1_min_bound)
	0
  in
  (* Clauses are input clauses *)
  assign_is_essential_input_symb bmc1_axioms_for_all_bounds;
  
  (* DEBUG *)
  dbg_env D_axs_init
    (fun () ->
      out_str "\n-----------BMC1 init axioms:---------\n";
      out_str ((Clause.clause_list_to_tptp bmc1_axioms_for_all_bounds)^"\n\n");
      out_str "\n--------------------\n";
      out_str "\n-----------BMC1 init clauses:---------\n";
      out_str ((Clause.clause_list_to_tptp current_clauses_after_init_bound)^"\n\n");
      out_str "\n--------------------\n";
    );
  (* DEBUG *)
	
	(* Add clauses for initial bound *)
  let current_clauses = ref ( bmc1_axioms_for_all_bounds @ current_clauses_after_init_bound) in

  (
   if !current_options.bmc1_pre_inst_reach_state
   then
     (current_clauses := 
       Bmc1Axioms.pre_inst_reachable_state_clauses (val_of_override !current_options.bmc1_min_bound) 
	 !current_clauses)
   else
     ()
  );
  
  (* when state vars pre-instantiation is on clauses in bmc1_for_pre_inst_cl *)
  (* contain origianal clauses which are needed to be instantiated *)

  bmc1_for_pre_inst_cl := !current_clauses;

  (if !current_options.bmc1_pre_inst_state
  then
    (current_clauses := 
      (Bmc1Axioms.pre_instantiate_state_var_clauses_range 
	 0 (val_of_override !current_options.bmc1_min_bound) !current_clauses);
     dbg D_axs_init ("\n Init all clauses \n"^(Clause.clause_list_to_string !current_clauses)^"\n");
    )
  else ()
  );

(* Output maximal bound for BMC1 *)
  let max_bound = get_max_bound () in

  (if max_bound >= 0 then
    out_str
      (Format.sprintf
	 "%sMaximal bound for %s is %d@\n"
	 pref_str
       (current_task_name())
	 max_bound);
  );
  (   (* Dump clauses to TPTP format? *)
      if val_of_override !current_options.bmc1_dump_clauses_tptp	  
      then
	  
	(* Formatter to write to, i.e. stdout or file *)
	let dump_formatter =
	  Bmc1Axioms.get_bmc1_dump_formatter ()
	in	
	Format.fprintf
	  dump_formatter
	  "%% ------------------------------------------------------------------------@\n%% Input clauses including axioms for bound 0@\n%a@."
	  (pp_any_list Clause.pp_clause_tptp "\n")
	  !current_clauses	  
     );
  (!current_clauses, !bmc1_for_pre_inst_cl)
*)


(*---------------------------------------------*)


(* return true if max_bound is not set of next_bound is larger than it *)
let pass_max_bound phase =
  let max_bound = get_max_bound() in
  max_bound >= 0 && phase.mc_cur_bound > max_bound

(*---------------------*)
let bmc1_init_bound_clauses state =

  (if (!current_options.bmc1_pre_inst_state || !current_options.bmc1_pre_inst_reach_state) 
  then 
    failwith "currently --bmc1_pre_inst_state and --bmc1_pre_inst_reach_state are not supported"
  );

  (
  try
    (* Get cardinality of state_type *)
    let max_bound = pred (Symbol.Map.find Symbol.symb_ver_state_type !Parser_types.cardinality_map) in
    (* Override default value of maximal bound from file *)
    !current_options.bmc1_max_bound <- override_file max_bound !current_options.bmc1_max_bound
	(* Cardinality not defined, then no upper bound *)
  with Not_found -> ()
  );

  let max_bound = get_max_bound () in
  if max_bound >= 0 then
    out_str
      (Format.sprintf
	 "%sMaximal bound for %s is %d@\n"
	 pref_str
	 (current_task_name())
	 max_bound);
  
  let state_term_0 = create_state_term 0 in
  Bmc1Axioms.change_gr_by_map_state state_term_0; 

  let bmc1_init_bound_axioms, problem_clauses = Bmc1Axioms.init_bound state.mc_clauses in
  state.mc_new_clauses <- List.rev_append state.mc_new_clauses bmc1_init_bound_axioms;

  (* DEBUG *)
  dbg_env D_axs_init
    (fun () ->
      out_str "\n-----------BMC1 problem clauses:---------\n";
      out_str (Clause.clause_list_to_string problem_clauses);
      out_str "\n--------------------\n";
    );
  dbg_env D_incremental_clauses
    (fun () ->
      out_str "\n-----------BMC1 init bound axioms:---------\n";
      out_str (Clause.clause_list_to_tptp bmc1_init_bound_axioms);
      out_str "\n--------------------\n";
    );
  (* DEBUG *)

  let phase = state.mc_phase in
  let handlers = state.mc_handlers in
  let (init_bound_axioms, assumptions) = handlers.mc_get_next_bound_axioms phase in
  
  (* fills in initial state *)
  state.mc_assumptions <- assumptions;
  (* add the new ones to the existing ones *)
  state.mc_new_clauses <- List.rev_append state.mc_new_clauses init_bound_axioms;
  state.mc_clauses <- problem_clauses
 
(* ground init clauses to a given bound *)
let ground_init clauses bound =
  (* create $$constBN *)
  let state_const = create_state_term bound in
  (* bound guard ~iProverbN *)
  let guard = add_compl_lit (create_bound_atom bound) in
  (* replace var with given state const in clause lits *)
  let ground_clause_by_var clause var =
    (* get grounded lits *)
    let ground_lits = Clause.replace_subterm term_db_ref var state_const (get_lits clause) in
    (* add the guard to minimise the SAT solver inferences *)
    let new_clause_lits = guard::ground_lits in
    (* reason *)
    let tstp_source =
      (Clause.TSTP_inference_record (Clause.TSTP_bmc1_instantiated_clause (bound), [clause]))
    in
    (* new clause *)
    let new_clause = create_clause tstp_source new_clause_lits in
    (* return that clause *)
    new_clause
  in
  (* find the var from ~$$init(var) and ground it. Keep clause if could't locate var *)
  let ground_clause clause =
    (* get var using init term *)
    let get_init_var init_lit =
      let init_atom = Term.get_atom init_lit in
      let args = Term.arg_to_list (Term.get_args init_atom) in
      assert (List.length args == 2);
      (* The format is $$init(Cj,X) *)
      let var = List.nth args 1 in
      var
    in
    (* calculate unique list of vars from init clauses *)
    let get_init_terms () =
      let is_init_term lit =
        (Term.get_top_symb (Term.get_atom lit)) == Symbol.symb_ver_init
      in
      let init_terms = Clause.find_all is_init_term clause in
      init_terms
    in
    (* init vars with dups *)
    let init_vars_dups = List.map get_init_var (get_init_terms ()) in
    (* remove dups *)
    let init_vars_set = TSet.of_list init_vars_dups in
    let init_vars = TSet.elements init_vars_set in
    (* use the only var *)
    let nvars = List.length init_vars in
    assert (nvars > 0);
    if nvars = 1
    then ground_clause_by_var clause (List.nth init_vars 0)
    else clause
  in
  (* ground all clauses *)
  let new_clauses () = List.map ground_clause clauses in
  (* return new or old clauses depending on a flag *)
  if !current_options.bmc1_ground_init
  then new_clauses ()
  else clauses

(* init the solver state *)
let bmc1_init_solver_state sched schedule_clauses =
  (* separate init clauses from the rest of the problem *)
  let separate_init_clauses clauses =
    (* clauses with init *)
    let is_init_term lit =
      (Term.get_top_symb (Term.get_atom lit)) == Symbol.symb_ver_init
    in
    let has_init clause = Clause.exists is_init_term clause in
    List.partition has_init clauses
  in
  (* problem clauses *)
  let problem = schedule_clauses.proof_clauses in
  (* separate init clauses *)
  let init_clauses, rest_of_problem = separate_init_clauses problem in
  (* ground the init clauses to bound 0 *)
  let grounded_init = ground_init init_clauses 0 in
  (* create initial BMC1 state *)
  let state = {
    mc_phase = Bmc1Common.get_initial_phase();
    mc_handlers = Bmc1Axioms.get_mc_handlers ();
    mc_assumptions = [];
    mc_unsat_core = [];
    mc_accum_uc = [];
    mc_extrapolation = [];
    mc_accum_extrap = [];
    mc_new_clauses = [];
    mc_accum_new = [];
    mc_bound_init_clauses = grounded_init;
    mc_init_clauses = init_clauses;
    mc_clauses = rest_of_problem;
    mc_full_problem = rest_of_problem;
    mc_schedule = sched;
    mc_schedule_clauses = schedule_clauses;
  } in

  (* add init clauses to state *)
  bmc1_init_bound_clauses state;

  (* load the full model *)
  Bmc1SplitPredicate.set_full_rel state.mc_full_problem;

  (* return that state *)
  state


(*----auxialry functions ------*)

(* get unsat core if necessary *)
let get_unsat_core_clauses () =
  let unsat_core_clauses =
    match val_of_override !current_options.bmc1_add_unsat_core with
      (* No unsat core needed *)
    | BMC1_Add_Unsat_Core_None
      when not (val_of_override !current_options.inst_out_proof)
      -> []
	  (* Need unsat core *)
    | _ ->
      let uc = Prop_solver_exchange.get_unsat_core ~soft:true () in
      if val_of_override !current_options.bmc1_verbose then
        (
        Format.printf "@\nAssumptions in UC:@.";
         List.iter (function t -> Format.printf "%s@." (Term.to_string t)) (UnsatCore.get_assumptions uc);
        Format.printf "@.";
        );
      UnsatCore.get_clauses uc
  in
  (* Verbose output for BMC1? *)
  (* if val_of_override !current_options.bmc1_verbose then                  *)
  (*   (                                                                    *)
  (*    (* Print unsat core *)                                              *)
  (*    Format.printf                                                       *)
  (*      "@\n%sUnsat core (size %d):@\n@\n%a@."                            *)
  (*      pref_str                                                          *)
  (*      (List.length unsat_core_clauses)                                  *)
  (*      (pp_any_list Clause.pp_clause_min_depth "\n") unsat_core_clauses; *)
  (*   );                                                                   *)
  (* Assign size of unsat core in statistics *)
  assign_int_stat (List.length unsat_core_clauses) bmc1_unsat_core_size;
  (* return clauses *)
  unsat_core_clauses

    (* Output proof from instantiation if necessary *)
let print_proof_for_instantiation unsat_core_clauses =
  if val_of_override !current_options.inst_out_proof then
    (
     (* Record time when proof extraction started *)
     let start_time = Unix.gettimeofday () in
     (* Start proof output *)
     Format.printf "@\n%% SZS output start CNFRefutation@\n@.";
     (* Proof output *)
     Format.printf "%a@." TstpProof.pp_tstp_proof_unsat_core unsat_core_clauses;
     (* End proof output *)
     Format.printf "%% SZS output end CNFRefutation@\n@.";
     (* Record time when proof extraction finished *)
     let end_time = Unix.gettimeofday () in
     (* Save time for proof extraction *)
     add_float_stat (end_time -. start_time) out_proof_time;
    )
      
      
      (* Get parent clauses of unsat core clauses *)
let get_unsat_core_parents unsat_core_clauses =
  (* save start time *)
  let start_time = Unix.gettimeofday () in
  
  (* save parent clauses of unsat core clauses *)
  let unsat_core_parents =
    match val_of_override !current_options.bmc1_add_unsat_core with
      (* Use no clauses from unsat core *)
    | BMC1_Add_Unsat_Core_None -> []
	  (* Use only clauses from unsat core *)
    | BMC1_Add_Unsat_Core_Clauses -> unsat_core_clauses
	  (* Use leaf clauses from unsat core *)
    | BMC1_Add_Unsat_Core_Leaves -> TstpProof.get_leaves unsat_core_clauses
	  (* Use all clauses from unsat core *)
    | BMC1_Add_Unsat_Core_All -> TstpProof.get_parents unsat_core_clauses
  in
  (* save end time *)
  let end_time = Unix.gettimeofday () in
  (* get extraction time *)
  let extraction_time = end_time -. start_time in
  (* Assign size of unsat core in statistics *)
  assign_int_stat (List.length unsat_core_parents) bmc1_unsat_core_parents_size;
  (* Assign time to extract unsat core clauses in statistics *)
  add_float_stat extraction_time bmc1_unsat_core_clauses_time;

  (* Verbose output for BMC1?*)
  if val_of_override !current_options.bmc1_verbose then
    (
     (* Print time to find parents of unsat core *)
     Format.printf
       "@\n%sTime to find parents of unsat core clauses: %.3f@."
       pref_str
       extraction_time;
     (* Print parents of unsat core *)
     Format.printf
       "@\n%sUnsat core parents has size %d@\n@\n%a@."
       pref_str
       (List.length unsat_core_parents)
       (pp_any_list Clause.pp_clause_min_depth "\n") unsat_core_parents;
    );
  (* return parents *)
  unsat_core_parents

    (* Dump unsat core in TPTP format if necessary *)
let dump_unsat_core_tptp unsat_core_clauses unsat_core_parents phase =
  if val_of_override !current_options.bmc1_dump_unsat_core_tptp then
    (
     (* Formatter to write to, i.e. stdout or file *)
     let dump_formatter = Bmc1Axioms.get_bmc1_dump_formatter () in
     (* bound *)
     let bound = phase.mc_cur_bound in
     (* Output clauses *)
     Format.fprintf
       dump_formatter
       "%% ------------------------------------------------------------------------@\n%% Unsat core for bound %d@\n%a@."
       bound
       Clause.pp_clause_list_tptp
       unsat_core_clauses;
     (* Output clauses *)
     Format.fprintf
       dump_formatter
       "%% ------------------------------------------------------------------------@\n%% Lifted unsat core for bound %d@\n%a@."
       bound
       Clause.pp_clause_list_tptp
       unsat_core_parents;
     (* Output bound assumptions *)
     Format.fprintf
       dump_formatter
       "%% ------------------------------------------------------------------------@\n%% Clause assumptions for bound %d@\n%a@."
       bound
       Clause.pp_clause_list_tptp
       (Bmc1Axioms.get_bound_assumptions bound)
    )
      

(* let _= out_str ("\n\n WARNING bmc1_loop commented: Bmc1Axioms.change_gr_by_map_state \n\n") *)

(* update phase; exit if the max_bound is passed *)
let update_phase_and_exit state =
  let handlers = state.mc_handlers in
  let phase = state.mc_phase in
  let old_mc_bound = phase.mc_cur_bound in 

  (* Increment bound by one *)
  handlers.mc_update_phase phase;
  (* assign current bound *)
  assign_int_stat phase.mc_cur_bound bmc1_current_bound;

  (* check is the bound was increased *)
  if ( not (old_mc_bound = phase.mc_cur_bound))
  then (
    (* change default grounding *)
    let next_state_term = create_state_term phase.mc_cur_bound in

(*    Bmc1Axioms.change_gr_by_map_state next_state_term; *)

    Bmc1Axioms.change_gr_by_map_state next_state_term; 

    (* output the AIG bound *)
    if !current_options.aig_mode
    then out_str (AigCommon.aig_pref^"u"^(string_of_int old_mc_bound)); (* unsat init state is bound 1 *)

    (* make new pre-instantiation of the input clauses *)
    state.mc_bound_init_clauses <- ground_init state.mc_init_clauses phase.mc_cur_bound;
  );
  (* Next bound is beyond maximal bound? *)
  if pass_max_bound phase then
    (
     out_str ("\n% Maximal bound is reached: "^(string_of_int (get_max_bound()))^"\n");
     (* Output  result for last bound *)
     out_str (szs_unknown_str);
     if not ((val_of_override !current_options.bmc1_out_stat) = BMC1_Out_Stat_None) then
       out_stat();
     (* Silently terminate *)
     raise Exit
    );

  (* output statistics if necessary *)
  if (val_of_override !current_options.bmc1_out_stat) = BMC1_Out_Stat_Full
  then out_stat ();

  (* Output next bound *)
  Format.printf "%s Continue %s with %s@\n@." pref_str handlers.mc_task_name (phase_to_string phase)


    (* Extrapolated axioms from unsat core *)
let get_bmc1_axioms_extrapolated phase unsat_core_clauses unsat_core_parents =
  (* Leaves clauses in proof to avoid repeated computation *)
  let get_unsat_core_leaves unsat_core_clauses unsat_core_parents =
    match val_of_override !current_options.bmc1_add_unsat_core with
      (* Unsat core has not been calculated *)
    | BMC1_Add_Unsat_Core_None ->
        failwith "Cannot extrapolate BMC1 axioms without unsat core"
	  (* Leaves of unsat core have not been calculated *)
    | BMC1_Add_Unsat_Core_Clauses ->
        TstpProof.get_leaves unsat_core_clauses
	  (* Take leaves of proof or all clauses in proof *)
    | BMC1_Add_Unsat_Core_Leaves
    | BMC1_Add_Unsat_Core_All ->
        unsat_core_parents
  in
  (* generate extrapolated axioms *)
  let create_bmc1_axioms_extrapolated unsat_core_clauses unsat_core_parents =
    (* create core leaves *)
    let unsat_core_leaves = get_unsat_core_leaves unsat_core_clauses unsat_core_parents in
    (* Create axioms for next bound of all axioms of previous bound in unsat core *)
    let bmc1_axioms_extrapolated = Bmc1Axioms.extrapolate_to_bound phase.mc_cur_bound unsat_core_leaves in
    (* Continue with extrapolated axioms *)
    bmc1_axioms_extrapolated
  in
  (* create those axioms if required *)
  if
    (* Extrapolate axioms in unsat core? *)
    (val_of_override !current_options.bmc1_unsat_core_extrapolate_axioms) &&
    (* Only if unsat caor has been extracted *)
    (not
       ((val_of_override !current_options.bmc1_add_unsat_core) =
        BMC1_Add_Unsat_Core_None))
  then create_bmc1_axioms_extrapolated unsat_core_clauses unsat_core_parents
  else []

(*
      (* get together all classes for next bound *)
let get_all_clauses clauses new_classes =
  let all_clauses =
   (*
    if !current_options.bmc1_pre_inst_state
    then
     
      let to_pre_instantiate = bmc1_for_pre_inst_cl @ new_classes in 
      (* out_str ("\n\nBefore pre inst \n\n"^(Clause.clause_list_to_string to_pre_instantiate)^"\n\n"); *)
     let pre_inst = Bmc1Axioms.pre_instantiate_state_var_clauses_range !bmc1_cur_bound !bmc1_cur_bound to_pre_instantiate in
      (* out_str ("\n\nAfter pre inst \n\n"^(Clause.clause_list_to_string pre_inst)^"\n\n"); *)
      let joint_clauses =  pre_inst @ (!clauses_ref) in
      if !current_options.bmc1_pre_inst_reach_state
      then Bmc1Axioms.pre_inst_reachable_state_clauses !bmc1_cur_bound joint_clauses
      else joint_clauses
    else
    *)
    new_classes @ (clauses)
  in
  (* Dump clauses to TPTP format *)
  let print_all_clauses all_clauses =
    (
     (*
       (* Formatter to write to, i.e. stdout or file *)
       let dump_formatter = Bmc1Axioms.get_bmc1_dump_formatter () in
       (* Output clauses *)
       Format.fprintf
       dump_formatter
       "%% ------------------------------------------------------------------------@\n%% Clauses for bound %d@\n%a@."
       next_bound
       (pp_any_list Clause.pp_clause_tptp "\n")
       all_clauses;
      *)
    );
  in
  (* print clauses if necessary *)
  if val_of_override !current_options.bmc1_dump_clauses_tptp then
    print_all_clauses all_clauses;
  (* return those clauses *)
  all_clauses
  *)

  
(* TODO: clean up *)

let get_all_clauses clauses new_clauses = List.rev_append new_clauses clauses

(* *)
let gathered_lemmas = ref []

let add_lemma lemma =
  gathered_lemmas := List.rev_append lemma !gathered_lemmas


let apply_lemmas state =
  let n_gl = List.length !gathered_lemmas in
  if n_gl > 0
  then (
    out_str ("Add "^(string_of_int n_gl)^" lemmas to UC axioms");
    state.mc_new_clauses <- List.rev_append !gathered_lemmas state.mc_new_clauses;
    (* clear the local lemma storage; they will still stay in the BMC1 state *)
    gathered_lemmas := []
  )


(*---------------------------------------------*)
(* check: run the scheduler on the given state *)
(*---------------------------------------------*)
let check state =
  (* prints the added things *)
  let print_state_new_stats state =
    (* stage-bound string *)
    let phase_str = phase_to_string state.mc_phase in
    (* Output assumptions for bound *)
    let print_assumptions assumptions =
      Format.printf "@.Assumptions for %s:@." phase_str;
      List.iter (function t -> Format.printf "%s@." (Term.to_string t)) assumptions;
      Format.printf "@."
    in
    (* output clause list with given explanation *)
    let print_nonempty_clause_list name clauses =
      Format.printf "@\n%s axioms for %s (total %d):@\n@." name phase_str
      (List.length clauses);
      List.iter (function t -> Format.printf "%s@." (Clause.to_string t)) clauses;
    in
    let print_clause_list name clauses =
      if list_non_empty clauses
      then print_nonempty_clause_list name clauses
    in
    (* Print all the fields *)
    (* print new clause lists *)
    print_clause_list "New bound" state.mc_new_clauses;
    print_clause_list "Unsat core" state.mc_unsat_core;
    print_clause_list "Extrapolated" state.mc_extrapolation;
    print_assumptions state.mc_assumptions;
  in

  (*---------------*)
  (* main function *)
  (*---------------*)
  print_mem "state" state;

  (* Clear properties of terms before running again *)
  (*  Proof_search_loop.provers_clear_and_remove_all ();*)

  (* apply gathered lemmas *)
  apply_lemmas state;

  (* print the new state if necessary *)
  if val_of_override !current_options.bmc1_verbose
  then print_state_new_stats state;

  (* process newly added fields *)
  let preprocess_state state =
    (* pass assumptions to the solver *)
    Prop_solver_exchange.assign_only_norm_solver_assumptions state.mc_assumptions;
    (* NOTE no preprocessing here, as it buys us too little *)
    (* add new clauses to solver *)
    (* List.iter Prop_solver_exchange.add_clause_to_solver state.mc_unsat_core;    *)
    (* List.iter Prop_solver_exchange.add_clause_to_solver state.mc_extrapolation; *)
    (* List.iter Prop_solver_exchange.add_clause_to_solver state.mc_new_clauses;   *)
    (* mark clauses as input. Note no unsat core or extrapolation *)
    Clause.assign_is_essential_input_symb (Clause.CL_List state.mc_new_clauses);

    (* save all session clauses *)
    state.mc_accum_new <- List.rev_append state.mc_new_clauses state.mc_accum_new;
    state.mc_accum_uc <- List.rev_append state.mc_unsat_core state.mc_accum_uc;
    state.mc_accum_extrap <- List.rev_append state.mc_extrapolation state.mc_accum_extrap;

    (* mark unsat core clauses *)
(*
    List.iter (Clause.assign_in_unsat_core false) state.mc_bound_init_clauses;
    List.iter (Clause.assign_in_unsat_core false) state.mc_clauses;
    List.iter (Clause.assign_in_unsat_core false) state.mc_accum_new;
    List.iter (Clause.assign_in_unsat_core false) state.mc_accum_uc;
    List.iter (Clause.assign_in_unsat_core true) state.mc_unsat_core;
    List.iter (Clause.assign_in_unsat_core true) state.mc_extrapolation;
*)
  in

  (* process the newly added clauses *)
  preprocess_state state;

  (* get clauses that are unconditionally used, conditionally used and unused *)
  (* use it after the the preprocessing, so all the new clauses are already merged *)
  let separate_clauses state =
    (* all the "new" clauses together *)
    let cl_1 = List.rev_append state.mc_accum_extrap state.mc_accum_new in
    let all_added_clauses = List.rev_append state.mc_accum_uc cl_1 in
    let ass_set = TSet.of_list state.mc_assumptions in
    (* get the short/full TR assumption flag used there *)
    let tr_ass_list =
      if TSet.mem (create_short_r_assumption ()) ass_set
      then [create_short_r_assumption ()]
      else if TSet.mem (create_full_r_assumption ()) ass_set
      then [create_full_r_assumption ()]
      else (
        dbg D_solver_input_smart (lazy ("Neither full_r no short_r assumption is used"));
        []
      )
    in
    (* get the clauses active and inactive on current bound *)
    let bound_ass_list = List.rev_append tr_ass_list (Bmc1Axioms.get_current_bound_assumptions state.mc_phase.mc_cur_bound) in
    (* lists of bound assumptions and their negations *)
    let bound_ass = TSet.of_list bound_ass_list in
    let bound_ass_neg = TSet.of_list (List.map add_compl_lit bound_ass_list) in
    (* clause that contain at least one negated assumption *)
    let not_assumed term = TSet.mem term bound_ass_neg in
    let not_assumed_cl clause = Clause.exists not_assumed clause in
    (* clause that contain at least one assumption *)
    let assumed term = TSet.mem term bound_ass in
    let assumed_cl clause = Clause.exists assumed clause in
    (* clauses that contain at least one assumptions are inactive (as they are switched off) *)
    let (inactive_clauses, other_cl) = List.partition assumed_cl all_added_clauses in
    (* from others, clauses that contain at least one negated assumptions *)
    (* (= all negated assumptions) are active *)
    let (active_clauses, always_clauses) = List.partition not_assumed_cl other_cl in
    always_clauses, active_clauses, inactive_clauses
  in

  (* separate all clauses *)
  let always_clauses, active_clauses, inactive_clauses = separate_clauses state in

  (* output state clauses in a smart way *)
  let out_smart state =
    (* output clause list with given explanation *)
    let print_nonempty_clause_list name clauses =
      Format.printf "%s axioms (total %d):@." name (List.length clauses);
      List.iter (function t -> Format.printf "%s@." (Clause.to_string t)) clauses;
      out_str "";
    in
    let print_clause_list name clauses =
      if list_non_empty clauses
      then print_nonempty_clause_list name clauses
    in
    (* print active clauses *)
    print_clause_list "Active clauses" active_clauses;
    print_clause_list "Always on clauses" always_clauses;
    print_clause_list "Init clauses" state.mc_bound_init_clauses;
    dbg_env D_solver_input_smart_full (fun () -> print_clause_list "Inactive clauses" inactive_clauses);

    (* output the problem if requested *)
    let cur_problem_size = " (size "^(string_of_int (List.length state.mc_clauses))^")" in
    let cur_problem_short =
      if state.mc_clauses == state.mc_full_problem
      then "Use FULL problem"^cur_problem_size
      else "Use REDUCED problem"^cur_problem_size
    in
    out_str cur_problem_short;
    dbg_env D_solver_input_smart_full (fun () ->
      List.iter (function t -> Format.printf "%s@." (Clause.to_string t)) state.mc_clauses);
  in

  (* use only clauses that are valid wrt current assumption *)
  let problem_clauses = List.rev_append state.mc_bound_init_clauses state.mc_clauses in
  let clauses = List.rev_append active_clauses (List.rev_append always_clauses problem_clauses) in

  (* !!! print the stats *)
  Bmc1SplitPredicate.print_transition_relation_size ();
  (* at this point mc_clauses contains everything *)
  dbg D_input_clauses (lazy ("\n"^Clause.clause_list_to_string clauses));
  dbg_env D_solver_input_smart (fun () -> out_smart state);
  let schedule_clauses = { state.mc_schedule_clauses with proof_clauses = clauses; } in
  let result = Proof_search_schedule.schedule_run schedule_clauses state.mc_schedule in
  (* out_str ("\nafter check: exception raised.\nBacktrace:\n"^(Printexc.get_backtrace ())); *)
  (* print result if necessary *)
  dbg_env D_result_after_each_check (fun () -> result_handler_basic result );

  (* clear session fields of state *)
  state.mc_assumptions <- [];
  state.mc_unsat_core <- [];
  state.mc_extrapolation <- [];
  state.mc_new_clauses <- [];

  (* return obtained result *)
  result


(*-------------------------------------------------*)
(* elapsed time code *)
(*-------------------------------------------------*)

(* keep the time *)
let last_timestamp_std = ref 0.0

(* set the timestamp *)
let timestamp_std () = last_timestamp_std := Unix.gettimeofday ()

(* helper: print the elapsed time, keep the time stamp *)
let elapsed_helper_std status =
  (* current time *)
  let current = Unix.gettimeofday () in
  (* report *)
  dbg D_timer (lazy (Format.sprintf "UCM:Timer report: %s: elapsed time %.3fs" status (current -. !last_timestamp_std)));
  (* return current time *)
  current

(* print the elapsed time, reset timer *)
let elapsed_std op stage state =
  let bound = state.mc_phase.mc_cur_bound in
  let bound_str = (", bound "^(string_of_int bound)) in
  let status = (stage^" "^op^bound_str) in
  last_timestamp_std := (elapsed_helper_std status)


(*---------------------------------------*)
let rec bmc1_loop state =
  (* let clauses = schedule_clauses.proof_clauses in *)

  (* assign current bound *)
  assign_int_stat state.mc_phase.mc_cur_bound bmc1_current_bound;

  dbg D_trace (lazy ("in main"));
  (* add assert that eq axioms are not omitted *)
    
(*---------------------------------------*)
  let rerun_all_after_unsat_for_next_bound () =
(*---------------------------------------*)
    let phase = state.mc_phase in
    let handlers = state.mc_handlers in
    state.mc_handlers.mc_after_unsat phase;
    (* Output status for current bound *)
    out_bmc1_unsat_result handlers phase;
    (* Assign last solved bound in statistics *)
    assign_int_stat phase.mc_cur_bound bmc1_last_solved_bound;

    (* Get clauses in unsatisfiable core *)
    let unsat_core_clauses = get_unsat_core_clauses () in
    (* Output proof from instantiation if necessary *)
    print_proof_for_instantiation unsat_core_clauses;
    (* Get parent clauses of unsat core clauses *)
    let unsat_core_parents = get_unsat_core_parents unsat_core_clauses in
    (* Dump unsat core in TPTP format if necessary *)
    dump_unsat_core_tptp unsat_core_clauses unsat_core_parents phase;

    (* update phase; check whether we can continue *)
    update_phase_and_exit state;

    (* gather axioms for next bound *)
    let next_bound_axioms, assumptions = handlers.mc_get_next_bound_axioms phase in

    (* Extrapolated axioms from unsat core *)
    let bmc1_axioms_extrapolated = get_bmc1_axioms_extrapolated phase unsat_core_clauses unsat_core_parents in

    (* fill in state fields *)
    state.mc_assumptions <- assumptions;
    state.mc_unsat_core <- unsat_core_parents;
    state.mc_extrapolation <- bmc1_axioms_extrapolated;
    state.mc_new_clauses <- next_bound_axioms;

    (* Run again for next bound *)
    elapsed_std "after UNSAT" "prepare" state;
    bmc1_loop state
  in
(*---------------------------------------*)
  let rerun_all_after_sat_for_next_bound all_clauses filtered_out_clauses =
(*---------------------------------------*)
    let phase = state.mc_phase in
    let handlers = state.mc_handlers in
    (* update phase; check whether we can continue *)
    state.mc_handlers.mc_after_sat phase;
    update_phase_and_exit state;

    (* Add axioms for next bound *)
    let next_bound_axioms, assumptions = handlers.mc_get_next_bound_axioms phase in

    (* fill in state fields. Note no unsat and extrapolated ones *)
    state.mc_assumptions <- assumptions;
    state.mc_new_clauses <- next_bound_axioms;

    (* Run again for next bound *)
    elapsed_std "after SAT" "prepare" state;
    bmc1_loop state
  in
(*---------------------------------------*)

  (* the following 4 functions are necessary to catch the case where *)
  (* the unsat is proved during the preprocessing of new axioms *)
  let rec rerun_all_after_sat_for_next_bound' all_clauses filtered_out_clauses =
    try rerun_all_after_sat_for_next_bound all_clauses filtered_out_clauses with
    Unsatisfiable_gr ->
      (* proprocessing shows that we are UNSAT wrt given assumptions *)
      check_stage_after_unsat_and_exit ()
	  
  and rerun_all_after_unsat_for_next_bound' () =
    try rerun_all_after_unsat_for_next_bound () with
    Unsatisfiable_gr ->
      (* proprocessing shows that we are UNSAT wrt given assumptions *)
      check_stage_after_unsat_and_exit ()

	  (* check the MC status after SAT and exit/re-run if necessary *)
  and check_stage_after_sat_and_exit all_clauses filtered_out_clauses =
    (* debug trace if requested *)
    (if !current_options.dbg_backtrace then
      out_str ("\nSatisfiable in check_stage_after_SAT: exception raised.\nBacktrace:\n"^(Printexc.get_backtrace ()))
    );

    rerun_all_after_sat_for_next_bound' all_clauses filtered_out_clauses

	(* check the MC status after UNSAT and exit/re-run if necessary *)
  and check_stage_after_unsat_and_exit () =
    (* debug trace if requested *)
    if !current_options.dbg_backtrace then
      out_str ("\nUnsatisfiable in check_stage_after_UNSAT: exception raised.\nBacktrace:\n"
	       ^(Printexc.get_backtrace ()));
    
    rerun_all_after_unsat_for_next_bound' ()
  in
 
  (* ------ main part of bmc1_loop----- *)
    
  let result = check state in
  elapsed_std "bmc1_loop" "check  " state;
  try
    match result with
    | PS_result_empty_clause _
    | PS_result_prop_solver_unsat ->
      dbg D_trace (lazy "checking after unsat");
      check_stage_after_unsat_and_exit ()

    | PS_result_unsat_multiple_cores _ ->
      failwith "bmc1_loop Multiple usat cores during instantiation should not happen here"

    | PS_result_prop_solver_unsat_na ->
      bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
      result

(* TODO: add model output: move result_handler_basic from iprover.ml to proof_search.ml *)
	
    | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

    | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
      dbg D_trace (lazy "checking after sat");
      check_stage_after_sat_and_exit inst_pre_model filtered_out_inst_pre_model
  with 
    Exit -> 
      result 

(*---------------------------------------*)
(* multi-predicate support *)
(*---------------------------------------*)

exception Return of ps_result

(* TODO: move all global into a state *)

(* session flag where to find the unsat cores *)
let use_saved_unsat_cores_ref = ref false
(* saved clauses from multiple unsat cores *)
let unsat_core_clauses_ref = ref []
(* latest saved unsat core *)
let bmc1_saved_unsat_core_ref = ref None
(* session flag to use saved assumptions *)
let use_saved_assumptions = ref true
(* saved k-induction assumptions as a model *)
let ind_step_model_ref = ref (BCMap.empty)
(* saved UNSAT core for induction *)
let saved_unsat_core_ref = ref []

(* session flag: how many unsat cores produce during EXPAND step *)
let max_unsat_core_number = ref 0
(* session counter: how many times EXPAND was called *)
let expand_iterations_number_ref = ref 0

(* set the init value of the unsat cores number *)
let init_unsat_core_number () =
  expand_iterations_number_ref := 0;
  max_unsat_core_number := 2


(* increase current value of unsat cores number *)
let inc_unsat_core_number () =
  max_unsat_core_number := 2 * !max_unsat_core_number;

  (* SAT solver doesn't like too many UC *)
  (
    if !max_unsat_core_number > !current_options.bmc1_ucm_expand_uc_limit
    then max_unsat_core_number := !current_options.bmc1_ucm_expand_uc_limit
  );
  expand_iterations_number_ref := succ (!expand_iterations_number_ref);
  out_str ("EXPAND iteration: "^(string_of_int !expand_iterations_number_ref));
  Prop_solver_exchange.set_max_unsat_cores_number !max_unsat_core_number

(* check whether we make too many loops in EXPAND *)
let force_expand_exit () =
  !expand_iterations_number_ref > !current_options.bmc1_ucm_n_expand_iterations

(* save unsat core after UNSAT was returned *)
let save_unsat_core () =
  let unsat_core = Prop_solver_exchange.get_unsat_core ~soft:true () in
  bmc1_saved_unsat_core_ref := Some(unsat_core)

(* return saved UNSAT core *)
let lookup_unsat_core () =
  match !bmc1_saved_unsat_core_ref with
  | Some(uc) -> uc
  | None -> failwith "No expected UNSAT core found"

(* return saved UNSAT core and clear the ref *)
let consume_unsat_core () =
  let uc = lookup_unsat_core () in
  bmc1_saved_unsat_core_ref := None;
  uc

(* check whether UC contains no assumptions other than flags *)
let uc_only_const_assumptions unsat_core =
  (* get assumptions *)
  let assumptions = UnsatCore.get_assumptions unsat_core in
  (* non-const term *)
  let non_const lit = not (Term.is_const_term lit) in
  (* return true if there is no non-const lits *)
  let ret = not (List.exists non_const assumptions) in
  (* FORNOW!! *)
  ret && false

(* process UNSAT results: save the UC and check whether it was without assumptions*)
let process_unsat_result state =
  save_unsat_core ();
  if uc_only_const_assumptions (lookup_unsat_core ())
  then (
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    raise (Return PS_result_prop_solver_unsat_na)
  )
(*-------------------------------------------------*)
(* elapsed time code *)
(*-------------------------------------------------*)


(* keep the time *)
let last_timestamp = ref 0.0

(* set the timestamp *)
let timestamp () = last_timestamp := Unix.gettimeofday ()

(* helper: print the elapsed time, keep the time stamp *)
let elapsed_helper status =
  (* current time *)
  let current = Unix.gettimeofday () in
  (* report *)
  out_str (Format.sprintf "UCM:Timer report: %s: elapsed time %.3fs" status (current -. !last_timestamp));
  (* return current time *)
  current

(* print the elapsed time, reset timer *)
let elapsed kind op stage state =
  let bound = state.mc_phase.mc_cur_bound in
  let bound_str = (", bound "^(string_of_int bound)) in
  let expand_iter =
    if op = "EXPAND"
    then (" (iteration "^(string_of_int !expand_iterations_number_ref)^")")
    else ""
  in
  let status = (stage^" "^kind^" "^op^expand_iter^bound_str) in
  last_timestamp := (elapsed_helper status)

(*-------------------------------------------------*)
(* unsat core based relation *)
(*-------------------------------------------------*)

let reduced_problem = ref []

(* mark state as using full relation *)
let use_full_problem state =
  (* use full problem *)
  state.mc_clauses <- state.mc_full_problem

let get_reduced_problem state new_clauses =
  match !current_options.bmc1_ucm_cone_mode with
  | BMC1_Ucm_Cone_Mode_None -> (* use full model *)
    use_full_problem state
  | BMC1_Ucm_Cone_Mode_AIG ->
    (* save the problem cone in the state *)
    state.mc_clauses <- Bmc1SplitPredicate.get_aig_pass_cone ()
  | BMC1_Ucm_Cone_Mode_Symb ->
    (* save the problem cone generated by symbols *)
    state.mc_clauses <- Bmc1SplitPredicate.get_cone_symb ()
  | BMC1_Ucm_Cone_Mode_UC ->
    reduced_problem := List.rev_append new_clauses !reduced_problem;
    state.mc_clauses <- !reduced_problem

let get_layered_problem state depth =
  match !current_options.bmc1_ucm_layered_model with
  | BMC1_Ucm_Cone_Mode_UC ->
    failwith "UC is not a valid cone mode for --bmc1_ucm_layered_model"
  | BMC1_Ucm_Cone_Mode_AIG
  | BMC1_Ucm_Cone_Mode_Symb ->
    state.mc_clauses <- Bmc1SplitPredicate.get_restricted_cone depth
  | BMC1_Ucm_Cone_Mode_None ->
    use_full_problem state

(* process single UNSAT core: remember used assumptions, print if necessary*)
(* and add lemmas. Return a list of clauses in the unsat core *)
let process_unsat_core unsat_core =
  print_mem "uc" unsat_core;
  (* remember all the assumptions from unsat core *)
  let assumptions = UnsatCore.get_assumptions unsat_core in
  Bmc1SplitPredicate.add_used_assumptions assumptions;
  (* clauses *)
  let unsat_core_clauses = UnsatCore.get_clauses unsat_core in
  assign_int_stat (List.length unsat_core_clauses) bmc1_unsat_core_size;
  (* let unsat_core_parents = TstpProof.get_parents unsat_core_clauses in *)
  (* (* Print parents of unsat core *)                                    *)
  (* dbg_env D_lemmas (fun () -> Format.printf                            *)
  (*   "@\n%sUnsat core parents has size %d@\n@\n%a@."                    *)
  (*   pref_str                                                           *)
  (*   (List.length unsat_core_parents)                                   *)
  (*   (pp_any_list Clause.pp_clause_min_depth "") unsat_core_parents;    *)
  (* );                                                                   *)

  (* print *)
  out_str ("Unsat core (size "^(string_of_int (List.length unsat_core_clauses))^") collected");
  (* print UC if requested or during debug *)
  (
    if (val_of_override !current_options.bmc1_out_unsat_core)
    then UnsatCore.print unsat_core
    else dbg_env D_print_uc (fun () -> UnsatCore.print unsat_core)
  );
  (* lemmas *)
  if !current_options.bmc1_ucm_max_lemma_size > 0
  then add_lemma (Bmc1SplitPredicate.get_lemma_by_uc unsat_core);
  (* return clauses *)
  unsat_core_clauses

(* support: *)

let get_unsat_core_rel state =
  (* Get clauses in unsatisfiable core *)
  let unsat_core_clauses =
    if !use_saved_unsat_cores_ref
    then ( (* use it just once *)
      out_str "Use SAVED unsat cores";
      use_saved_unsat_cores_ref := false;
      !unsat_core_clauses_ref
    )
    else (
      out_str "Don't Use SAVED unsat cores";
      process_unsat_core (consume_unsat_core ())
    )
  in
  (* get the unsat-based relation *)
  try
    let short_rel, short_problem = Bmc1SplitPredicate.get_next_clauses_from_unsat_core unsat_core_clauses state.mc_phase.mc_cur_bound in
    (* save it in UNSAT *)
    state.mc_unsat_core <- short_rel;
    (* Print parents of unsat core *)
    dbg_env D_lemmas (fun () -> Format.printf
      "@\n%sUnsat core-based problem has size %d@\n@\n%a@."
      pref_str
      (List.length short_problem)
      (pp_any_list Clause.pp_clause_min_depth "") short_problem;
    );
    (* reduce problem based on the reduced TR *)
    get_reduced_problem state short_problem
  with
  | Bmc1SplitPredicate.No_path_in_tr ->
  (* if there is no path in the UNSAT core, it is always UNSAT *)
  (
    (* state.mc_handlers.mc_after_unsat state.mc_phase; *)
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    raise (Return PS_result_prop_solver_unsat_na);
  )

let get_sat_model_rel state inst_pre_model =
  let bound = state.mc_phase.mc_cur_bound in
  (* get the set of NEXT constants from the model *)
  let next_preds = Bmc1SplitPredicate.get_tr_predicates inst_pre_model bound in
  dbg D_tr_pred (lazy ("before no_changes_in_next: "^(Term.term_list_to_string (TSet.elements next_preds))));

  if Bmc1SplitPredicate.no_changes_in_next next_preds
  then true
  else (
    (* get the model-based short relation *)
    let short_rel = Bmc1SplitPredicate.get_tr_from_model inst_pre_model next_preds bound in
    (* save it in UNSAT *)
    state.mc_unsat_core <- short_rel;
    (* use the full problem *)
    use_full_problem state;
    (* that's it *)
    false
  )

(* combine all clauses from unsat cores together *)
let process_multiple_unsat_core unsat_cores =
  let process_uc accum unsat_core =
    List.rev_append (process_unsat_core unsat_core) accum
  in
  (* set the appropriate flag *)
  use_saved_unsat_cores_ref := true;
  (* output the unsat core number *)
  out_str ("Unsat cores collected: "^(string_of_int (List.length unsat_cores)));
  (* process all unsat cores *)
  unsat_core_clauses_ref := List.fold_left process_uc [] unsat_cores;
  out_str "Unsat core collection finished"

let add_next_to_unsat_core = ref false

let use_problem_depth = false
(* model assumption that was passed to the ..*)
let initial_depth_model_assumptions = ref TSet.empty

(* check the list of the UNSAT cores if they contain the only *)
let cores_from_init_model unsat_cores =
  (* return true if UC contains assumptions from the initial model assumptions *)
  let uc_from_init unsat_core =
    (* return true if a term is NOT in in the initial model assumptions *)
    let non_initial_assumption term =
      not (TSet.mem term !initial_depth_model_assumptions)
    in
    (* check if such one exists *)
    not (List.exists non_initial_assumption (UnsatCore.get_assumptions unsat_core))
  in
  (* return true if *)
  List.exists uc_from_init unsat_cores

(* remove from ASSUMPTIONS those that participate in UC and are not from the initial ones *)
let filter_new_assumptions assumptions unsat_cores =
  (* make the set of old assumptions *)
  let old_assumptions = TSet.of_list assumptions in
  let all_uc_assumptions =
    (* add all the assumptions from UC to a given set *)
    let f set unsat_core =
      TSet.union set (TSet.of_list (UnsatCore.get_assumptions unsat_core))
    in
    List.fold_left f TSet.empty unsat_cores
  in
  (* remove violating UC assumptions *)
  let violating_uc_assumptions = TSet.diff all_uc_assumptions !initial_depth_model_assumptions in
  let rest_assumptions = TSet.diff old_assumptions violating_uc_assumptions in
  (* return the rest assumptions *)
  TSet.elements rest_assumptions

(* extend current model *)
let extend state =
  let handlers = state.mc_handlers in
  let old_bound = state.mc_phase.mc_cur_bound in
  (* update phase; check whether we can continue *)
  update_phase_and_exit state;

  (* gather axioms for next bound *)
  let next_bound_axioms, assumptions = handlers.mc_get_next_bound_axioms state.mc_phase in

  (* copy to state *)
  state.mc_assumptions <- assumptions;
  state.mc_new_clauses <- List.rev_append state.mc_new_clauses next_bound_axioms;

  (* if we have a new bound... *)
  let new_bound = state.mc_phase.mc_cur_bound in
  if ( new_bound > old_bound )
  then (
    (* clear saved relation *)
    Bmc1SplitPredicate.clear_current_rel old_bound;
    (* clear saved assumptions if required *)
    if ( (!current_options.bmc1_ucm_relax_model mod 2) = 0 )
    then Bmc1SplitPredicate.clear_saved_assumptions ();
  )

(* get assumptions for the short relation *)
let get_short_r_assumptions () =
  (* get extra assumptions if necessary *)
  let extra_assumptions =
    if !current_options.bmc1_ucm_expand_neg_assumptions
    then Bmc1SplitPredicate.get_negative_assumptions ()
    else if !current_options.soft_assumptions
    then (
      let soft_assumptions = Bmc1SplitPredicate.get_grounded_pos_assumptions () in
      (* mark assumptions as a soft one right now *)
      Prop_solver_exchange.set_soft_assumptions soft_assumptions;
      (* return those assumptions *)
      soft_assumptions
    )
    else []
  in
  (* add short_rel assumption *)
  create_short_r_assumption() :: extra_assumptions

(* entry point: check SAT, expand(1), manage result exceptions *)
let rec bmc1_mp_loop_init state =
  (* output the size of the N *)
  out_str ("UIIU: "^(string_of_int (Term.Set.cardinal (get_next_state_consts ()))));
  bmc1_progress "SAT CHECK" state;
  timestamp();
  (* add full_R assumption for init *)
  state.mc_assumptions <- create_full_r_assumption() :: state.mc_assumptions;
  let result = check state in
  elapsed "BMC1" "loop init" "check  " state;
  try
    match result with
    | PS_result_empty_clause _
    | PS_result_prop_solver_unsat ->
      dbg D_trace (lazy "unsat in init");
      process_unsat_result state;
      if !current_options.bmc1_k_induction
      then (* go to induction step check *)
        extend_induction_step state
      else (* continue with BMC *)
        check_bound_1 state

    | PS_result_unsat_multiple_cores _ ->
      failwith "bmc1_mp_loop_init Multiple usat cores during instantiation should not happen here"

    | PS_result_prop_solver_unsat_na ->
      dbg D_trace (lazy "unsat no assumptions in init");
      bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
      result
    
    | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

    | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
      dbg D_trace (lazy "sat in init");
      state.mc_handlers.mc_after_sat state.mc_phase;
      result
  with
    | Exit ->
      result
    | Return res ->
      res

(* here we have an UNSAT after extension. Go to another extension then *)
and extend_after_unsat state =
  if !current_options.bmc1_k_induction
  then (* go to induction step check *)
    extend_induction_step state
  else (* continue with BMC *)
    bmc_extend_after_unsat state

(* at bound 1 we create the full R and if SAT then we done, *)
(* if not then the usual extend_unsat loop started *)
and check_bound_1 state =
  (* create N(X,s_1,s_0) *)
  extend state;
  (* use full problem *)
  use_full_problem state;
  (* add full_R assumption *)
  state.mc_assumptions <- create_full_r_assumption() :: state.mc_assumptions;
  (* check SAT *)
  bmc1_progress "SAT CHECK" state;
  elapsed "BMC1" "first bound" "prepare" state;
  let result = check state in
  elapsed "BMC1" "first bound" "check  " state;
  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat in bound_1");
    process_unsat_result state;
    extend_after_unsat state

  | PS_result_unsat_multiple_cores _ ->
    failwith "check_bound_1 Multiple usat cores during instantiation should not happen here"

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in bound_1");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

  | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
    
    dbg D_trace (lazy "sat in bound_1");
    state.mc_handlers.mc_after_sat state.mc_phase;
    result

(* choose a way to process EXPAND after SAT based on switch *)
and expand_after_sat state inst_pre_model filtered_out_inst_pre_model =
  if !current_options.bmc1_ucm_full_tr_after_sat
  then check_full_rel state inst_pre_model
  else bmc1_expand_after_sat state inst_pre_model filtered_out_inst_pre_model

(* get the TR out of the model *)
and bmc1_expand_after_sat state inst_pre_model filtered_out_inst_pre_model =
  bmc1_progress "EXPAND after SAT" state;
  Bmc1SplitPredicate.prepare_model_tr ();
  bmc1_expand_after_sat' state inst_pre_model filtered_out_inst_pre_model

and bmc1_expand_after_sat' state inst_pre_model filtered_out_inst_pre_model =
  bmc1_progress "EXPAND-after-SAT" state;
  (* get unsat core relation *)
  if get_sat_model_rel state inst_pre_model
  then (* no new elements there; return SAT *)
  (
    (* exit with sat *)
   state.mc_handlers.mc_after_sat state.mc_phase;
   PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model)
  )
  else (
  (* assume bound assumptions *)
  state.mc_assumptions <- Bmc1Axioms.get_current_bound_assumptions state.mc_phase.mc_cur_bound;
  (* add short_rel assumptions *)
  state.mc_assumptions <- List.rev_append (get_short_r_assumptions ()) state.mc_assumptions;


  (* check SAT *)
  elapsed "BMC1" "EXPAND-after-SAT" "prepare" state;
  let result = check state in
  elapsed "BMC1" "EXPAND-after-SAT" "check  " state;
  Prop_solver_exchange.clear_soft_assumptions ();

  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat in expand_after_sat");
    process_unsat_result state;
    (* in Chains there is a problem that we have no new NEXT but only INIT *)
    expand_after_unsat state

  | PS_result_unsat_multiple_cores unsat_cores ->
    dbg D_trace (lazy "multi-unsat $next in expand_after_sat");
    process_multiple_unsat_core unsat_cores;
    expand_after_unsat state

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in expand_after_sat");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

  | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->

    dbg D_trace (lazy "sat in expand_after_sat");
    dbg_env D_model (fun () -> out_model inst_pre_model filtered_out_inst_pre_model);
    bmc1_expand_after_sat' state inst_pre_model filtered_out_inst_pre_model
  )

(* check the full relation *)
(* we came here after SAT for bound n *)
(* we add full relation up from 0 to n *)
(* and check this on a model. *)
(* Save N(i,s,s') in a list for the further unsat core *)
and check_full_rel state model =
  bmc1_progress "EXPAND" state;
  (* increase the number of produced unsat cores *)
  inc_unsat_core_number ();
  (* get and save assumptions together with list on N(i,s,s') prediates *)
  let model_assumptions = (Bmc1SplitPredicate.get_model_literals model) in
  (* assume full_R assumption together with bounds for n *)
  let bound_assumpitons = Bmc1Axioms.get_current_bound_assumptions state.mc_phase.mc_cur_bound in
  let unconditional_assumptions = create_full_r_assumption() :: bound_assumpitons in
  initial_depth_model_assumptions := TSet.of_list (List.rev_append unconditional_assumptions model_assumptions);
  (* init depth counter *)
  let depth =
    if !current_options.bmc1_ucm_layered_model != BMC1_Ucm_Cone_Mode_None
    then 1
    else -1
  in
  (* call the full relation check on layered problem *)
  check_layered_problem state depth model_assumptions unconditional_assumptions

(* check the full-rel model with problem restricted to DEPTH *)
and check_layered_problem state depth model_assumptions unconditional_assumptions =
  (* check whether we should use model *)
  let assumptions =
    if force_expand_exit ()
    then []
    else model_assumptions
  in
  (* correct elapsed *)
  let elapsed_depth stage =
    let d = string_of_int depth in
    let d_str = (" (depth "^d^")") in
    elapsed ("BMC1"^d_str) "EXPAND" stage state
  in
  (* add model here *)
  state.mc_assumptions <- List.rev_append assumptions unconditional_assumptions;
  (* use full problem, reduced to certain depth if necessary *)
  get_layered_problem state depth;
  (* inform instantiation about the multiple unsat cores mode *)
  Prop_solver_exchange.init_multiple_run_mode (state.mc_assumptions) unconditional_assumptions;
  (* check SAT *)
  elapsed_depth "prepare";
  let result = check state in
  elapsed_depth "check  ";
  (* clear the multi unsat core mode *)
  Prop_solver_exchange.clear_multiple_run_mode ();
  
  (* helper method to proceed after the UNSAT *)
  let continue_after_unsat unsat_cores =
    (* unsat cores contain the one from the original model? *)
    (* UNSAT core must came with additional TR segments, that's what we are looking for*)
    (* so continue with EXPAND phase (see true) *)
    if (depth = -1) || cores_from_init_model unsat_cores || true
    then (* check the consistency with an appropriate UNSAT core, no extend *)
    (
      (* out_str "CORES FROM INIT only"; *)
      expand_after_unsat state
    )
    else (* remove violating assumptions from the model *)
    (
      (* if the max depth is reached, and the TR from the UCs adds something new *)
      (* to the existing one, then exit as above. If the max depth is reached,*)
      (* but the TR is subsumed by the existing one, re-run with the last depth *)
      (* and initial model *)
      let max_depth_reached = Bmc1SplitPredicate.max_depth_reached depth in
      let new_depth =
        if max_depth_reached
        then depth
        else succ depth
      in
      (* do we need to reduce model to the initial one *)
      let reduce_model =
        if max_depth_reached
        then Bmc1SplitPredicate.has_new_next_segments unsat_cores
        else false
      in
      (* use initial assumptions if re have to reduce model *)
      let new_assumptions =
        if reduce_model
        then TSet.elements !initial_depth_model_assumptions
        else filter_new_assumptions model_assumptions unsat_cores
      in
      (* continue with new depth if possible; exit if the max is reached and new TR found *)
      if max_depth_reached && (not reduce_model)
      then (
        out_str "Max depth reached with new segments in N";
        expand_after_unsat state
      )
      else (
        (
          if max_depth_reached
          then out_str "Max depth reached with NO new segments in N";
        );
        check_layered_problem state new_depth new_assumptions unconditional_assumptions
      )
    )
  in

  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat $next in full_rel");
    process_unsat_result state;
    let unsat_cores = [lookup_unsat_core()] in
    (* in Chains there is a problem that we have no new NEXT but only INIT *)
    continue_after_unsat unsat_cores

  | PS_result_unsat_multiple_cores unsat_cores ->
    dbg D_trace (lazy "multi-unsat $next in full_rel");
    process_multiple_unsat_core unsat_cores;
    continue_after_unsat unsat_cores

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in full_rel");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

 | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
    dbg D_trace (lazy "sat in full_rel");
    dbg_env D_model (fun () -> out_model inst_pre_model filtered_out_inst_pre_model);
    (* exit if full problem or *)
    if Bmc1SplitPredicate.max_depth_reached depth
    then (* the problem was full; we are done then *)
    (
      state.mc_handlers.mc_after_sat state.mc_phase;
      result
    )
    else (* increase depth and continue *)
    (
      let new_ass_set = TSet.of_list (Bmc1SplitPredicate.get_model_literals inst_pre_model) in
      let old_ass_set = !initial_depth_model_assumptions in
      let new_assumptions = TSet.elements (TSet.union old_ass_set new_ass_set) in
      (* TODO: add flag to choose between only new or merged assumptions *)
      (* currently use new ones *)
      check_layered_problem state (succ depth) new_assumptions unconditional_assumptions
    )

(* extend after UNSAT for BMC *)
and bmc_extend_after_unsat state =
  bmc1_progress "EXTEND" state;
  (* extend the model *)
  extend state;
  (* clear the saved problem as the new one will appear *)
  reduced_problem := [];
  (* get unsat core relation guarded by bound_{n+1} *)
  get_unsat_core_rel state;
  (* reset solvers if requested *)
  if !current_options.reset_solvers
  then Prop_solver_exchange.reset_solvers ();
  (* populate the extra bound with short rel *)
  let clauses_for_new_bound = Bmc1SplitPredicate.extend_one_bound state.mc_phase.mc_cur_bound in
  state.mc_new_clauses <- List.rev_append clauses_for_new_bound state.mc_new_clauses;
  (* add short_rel assumptions *)
  state.mc_assumptions <- List.rev_append (get_short_r_assumptions ()) state.mc_assumptions;


  (* check SAT *)
  elapsed "BMC1" "EXTEND" "prepare" state;
  let result = check state in
  elapsed "BMC1" "EXTEND" "check  " state;
  Prop_solver_exchange.clear_soft_assumptions ();

  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat $next in extend_unsat");
    process_unsat_result state;
    (* continue with extension *)
    extend_after_unsat state

  | PS_result_unsat_multiple_cores _ ->
    failwith "expand_after_unsat Multiple usat cores during instantiation should not happen here"

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in extend_unsat");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

 | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
    dbg D_trace (lazy "sat in extend_unsat");
    dbg_env D_model (fun () -> out_model inst_pre_model filtered_out_inst_pre_model);
    (* first time we come to EXPAND from UNSAT; *)
    init_unsat_core_number ();
    (* clear the saved problem as the new one will appear *)
    reduced_problem := [];
    (* keep the UNSAT core from the NEXT predicate *)
    (* NB!! we do NOT need this, as all the UNSAT core is there from the previous run *)
    (* add_next_to_unsat_core := true; *)
    expand_after_sat state inst_pre_model filtered_out_inst_pre_model

(* expand after UNSAT *)
and expand_after_unsat state =
  bmc1_progress "SAT CHECK" state;
  (* get unsat core relation *)
  get_unsat_core_rel state;
  (* assume bound assumptions *)
  state.mc_assumptions <- Bmc1Axioms.get_current_bound_assumptions state.mc_phase.mc_cur_bound;
  (* add short_rel assumptions *)
  state.mc_assumptions <- List.rev_append (get_short_r_assumptions ()) state.mc_assumptions;


  (* check SAT *)
  elapsed "BMC1" "after EXPAND" "prepare" state;
  let result = check state in
  elapsed "BMC1" "after EXPAND" "check  " state;
  Prop_solver_exchange.clear_soft_assumptions ();

  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat $next in expand_unsat");
    process_unsat_result state;
    (* continue with extension *)
    extend_after_unsat state

  | PS_result_unsat_multiple_cores _ ->
    failwith "no_expand_after_unsat Multiple usat cores during instantiation should not happen here"

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in expand_unsat");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

  | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
    dbg D_trace (lazy "sat $next in expand_unsat");
    (* no need to add extra stuff to unsat core, as it is already there *)
    add_next_to_unsat_core := false;
    expand_after_sat state inst_pre_model filtered_out_inst_pre_model

(* induction step for k-induction *)
and extend_induction_step state =
  bmc1_progress "k-induction STEP" state;
  (* save unsat cores from previous run *)
  saved_unsat_core_ref := process_unsat_core (consume_unsat_core ());
  (* extend the model *)
  extend state;
  (* clear the saved problem as the new one will appear *)
  reduced_problem := [];
  (* first time we come to STEP EXPAND from UNSAT; *)
  init_unsat_core_number ();
  (* continue with expanded k-induction step and saved model *)
  check_induction_step state !ind_step_model_ref

and check_induction_step state inst_pre_model =
  bmc1_progress "k-induction EXPAND" state;
  (* increase the number of produced unsat cores *)
  inc_unsat_core_number ();
  (* get assumptions together with list on N(i,s,s') prediates *)
  let model_assumptions = (Bmc1SplitPredicate.get_model_literals inst_pre_model) in
  (* assume full_R assumption together with bounds for n *)
  let bound_assumpitons = Bmc1Axioms.get_current_bound_assumptions state.mc_phase.mc_cur_bound in
  let unconditional_assumptions = create_full_r_assumption() :: bound_assumpitons in
  (* check whether we should use model *)
  let assumptions =
    if force_expand_exit ()
    then []
    else model_assumptions
  in
  (* add model here *)
  state.mc_assumptions <- List.rev_append assumptions unconditional_assumptions;
  (* use full problem *)
  use_full_problem state;
  (* inform instantiation about the multiple unsat cores mode *)
  Prop_solver_exchange.init_multiple_run_mode (state.mc_assumptions) unconditional_assumptions;
  (* check SAT *)
  elapsed "k-induction" "EXPAND" "prepare" state;
  let result = check state in
  elapsed "k-induction" "EXPAND" "check  " state;
  (* clear the multi unsat core mode *)
  Prop_solver_exchange.clear_multiple_run_mode ();
  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat in check_induction_step");
    process_unsat_result state;
    (* check the consistency with an appropriate UNSAT core, no extend *)
    expand_after_induction state

  | PS_result_unsat_multiple_cores unsat_cores ->
    dbg D_trace (lazy "multi-unsat $next in check_induction_step");

    process_multiple_unsat_core unsat_cores;

    (* check the consistency with an appropriate UNSAT cores, no extend *)
    if (Prop_solver_exchange.is_empty_model ())
    then (* unconditionally unsat; exit now *)
    (
      state.mc_handlers.mc_after_unsat state.mc_phase;
      result
    )
    else
      (* expand_after_induction state *)
      check_induction_step state inst_pre_model

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in check_induction_step");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

  | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->
 
    dbg D_trace (lazy "sat in check_induction_step");
    (* save the model *)
    ind_step_model_ref := inst_pre_model;
    (* restore UNSAT core *)
    use_saved_unsat_cores_ref := true;
    unsat_core_clauses_ref := !saved_unsat_core_ref;
    (* continue with BMC1 *)
    if state.mc_phase.mc_cur_bound = 1
    then check_bound_1 state
    else bmc_extend_after_unsat state

and expand_after_induction state =
  bmc1_progress "SAT CHECK after STEP" state;

  (* get unsat core relation *)
  get_unsat_core_rel state;
  (* assume bound assumptions *)
  state.mc_assumptions <- Bmc1Axioms.get_current_bound_assumptions state.mc_phase.mc_cur_bound;
  (* add short_rel assumptions *)
  state.mc_assumptions <- List.rev_append (get_short_r_assumptions ()) state.mc_assumptions;
  (* check SAT *)
  elapsed "k-induction" "after EXPAND" "prepare" state;
  let result = check state in
  elapsed "k-induction" "after EXPAND" "check  " state;
  Prop_solver_exchange.clear_soft_assumptions ();

  match result with
  | PS_result_empty_clause _
  | PS_result_prop_solver_unsat ->
    dbg D_trace (lazy "unsat $next in expand_after_induction");
    (* UNSAT in induction step; the whole thing is UNSAT *)
    state.mc_handlers.mc_after_unsat state.mc_phase;
    result

  | PS_result_unsat_multiple_cores _ ->
    failwith "expand_after_induction Multiple usat cores during instantiation should not happen here"

  | PS_result_prop_solver_unsat_na ->
    dbg D_trace (lazy "unsat no assumptions in expand_after_induction");
    bmc1_unsat_no_assumptions_out state.mc_handlers state.mc_phase;
    result

  | PS_result_resolution_sat (_res_model, _filtered_out_clauses_inst_pre_model)
      ->  failwith "bmc1_loop: resoltion sat is not supported "

  | PS_result_instantiation_sat (inst_pre_model, filtered_out_inst_pre_model) ->

    dbg D_trace (lazy "sat $next in expand_after_induction");
    (* no need to add extra stuff to unsat core, as it is already there *)
    add_next_to_unsat_core := false;
    check_induction_step state inst_pre_model

