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

type stat_int_entry = 
    {
     int_entry_name : string;
     mutable value : int ;
   }

type stat_float_entry = 
    {
     float_entry_name    : string;
     mutable float_value : float ;
   }


type stat_fun_type = unit -> int

(* statistics for stat_fun_entry is generated by calling stat_fun *)
(* stat_fun can be assigned by any module *)
type stat_fun_entry = 
    {
     fun_entry_name          : string;
     mutable stat_fun        : stat_fun_type param
   }



(*-----------------*)
let assign_int_stat value stat  = 
  stat.value <- value

let incr_int_stat int stat = 
  stat.value <- stat.value + int

let get_val_stat s = s.value

let get_float_val_stat s = s.float_value

let assign_float_stat value stat = 
  stat.float_value <- value

let add_float_stat float stat = 
  stat.float_value <- (stat.float_value +. float)

let get_val_stat_fun stat_fun_entry = 
  match stat_fun_entry.stat_fun with
    Def(f) -> f ()
  |Undef -> failwith 
	("Statistics for function "^(stat_fun_entry.fun_entry_name)^" is undefined")
	
let assign_fun_stat f stat  = 
  stat.stat_fun <- Def (f)

let clear_stat_int_entry e = e.value <- 0
let clear_stat_fun_entry e = e.stat_fun <- Undef


(* does not work! *)
let run_and_time stat f x =
  let start_time = Unix.gettimeofday () in
  (* out_str ("s "^(string_of_float start_time)^"\n");*)
  try
    let res = f x in
    let end_time   = Unix.gettimeofday () in 
(*    out_str ("e "^(string_of_float end_time)^"\n");*)
    let run_time = (end_time -. start_time) in
(*    out_str ("r "^(string_of_float run_time)^"\n");*)
    add_float_stat run_time stat;
    res
  with
  |e -> 
      let end_time   = Unix.gettimeofday () in 
      let run_time = (end_time -. start_time) in
      out_str "adding\n";
      add_float_stat run_time stat;      
      raise e
	


(*-------General---------*)

let num_of_terms  = 
  {
   fun_entry_name  = "num_of_terms";
   stat_fun        = Undef 
 }

let num_of_symbols  = 
  {
   fun_entry_name  = "num_of_symbols";
   stat_fun        = Undef 
 }

let num_of_input_clauses = 
  {
   int_entry_name = "num_of_input_clauses"; 
   value          = 0
 }

let num_of_input_neg_conjectures = 
  {
   int_entry_name = "num_of_input_neg_conjectures";
   value          = 0
 }


let num_of_splits = 
  {
   int_entry_name  = "num_of_splits";
   value = 0;
 }


let num_of_split_atoms = 
  {
   int_entry_name  = "num_of_split_atoms";
   value = 0;
 }

let num_of_reused_defs = 
  {
   int_entry_name  = "num_of_reused_defs";
   value = 0;
 }

let num_eq_ax_congr_red = 
  {
   int_entry_name  = "num_eq_ax_congr_red";
   value = 0;
 }

let num_of_sem_filtered_clauses = 
  {
   int_entry_name  = "num_of_sem_filtered_clauses";
   value = 0;
 }

(* non-collapsed subtypes *)
let num_of_subtypes = 
  {
   int_entry_name  = "num_of_subtypes";
   value = 0;
 }

let monotx_restored_types = 
  {
   int_entry_name  = "monotx_restored_types";
   value = 0;
 }


let sat_num_of_epr_types = 
  {
   int_entry_name  = "sat_num_of_epr_types";
   value = 0;
 }

let sat_num_of_non_cyclic_types = 
  {
   int_entry_name  = "sat_num_of_non_cyclic_types";
   value = 0;
 }

let sat_num_of_guarded_non_collapsed_types = 
  {
   int_entry_name  = "sat_guarded_non_collapsed_types";
   value = 0;
 }


let epr = 
  {
   int_entry_name  = "epr";
   value = 0;
 }
    
let horn = 
  {
   int_entry_name  = "horn";
   value = 0;
 }

let lits = 
  {
   int_entry_name  = "lits";
   value = 0;
 }
    
let lits_eq = 
  {
   int_entry_name  = "lits_eq";
   value = 0;
 }

let clauses = 
  {
   int_entry_name  = "clauses";
   value = 0;
 }

let conjectures = 
  {
   int_entry_name  = "conjectures";
   value = 0;
 }


let unary = 
  {
   int_entry_name  = "unary";
   value = 0;
 }

let binary = 
  {
   int_entry_name  = "binary";
   value = 0;
 }


let pure_diseq_elim = 
  {
   int_entry_name  = "num_pure_diseq_elim";
   value = 0;
 }


let simp_replaced_by =
  {
   int_entry_name  = "simp_replaced_by";
   value = 0;
 }

let res_preprocessed =
  {
   int_entry_name  = "res_preprocessed";
   value = 0;
 }

let prep_upred =
  {
   int_entry_name  = "prep_upred";
   value = 0;
 }


let prep_unflattend = 
 {
   int_entry_name  = "prep_unflattend";
   value = 0;
 } 

let pred_elim_cands = 
 {
  int_entry_name  = "pred_elim_cands";
  value = 0;
 } 

let pred_elim = 
 {
  int_entry_name  = "pred_elim";
  value = 0;
 } 


let pred_elim_cl = 
 {
  int_entry_name  = "pred_elim_cl";
  value = 0;
 } 

let pred_elim_cycles = 
 {
  int_entry_name  = "pred_elim_cycles";
  value = 0;
 } 

let prep_cycles = 
  {
   int_entry_name  = "prep_cycles";
   value = 0; 
 }

let merged_defs = 
  {
   int_entry_name  = "merged_defs";
   value = 0; 
 }

let merged_defs_ncl = 
  {
   int_entry_name  = "merged_defs_ncl";
   value = 0; 
 }


let abstr_arg_filter_cycles = 
 {
  int_entry_name  = "abstr_arg_filter_cycles";
  value = 0;
 } 

let forced_gc_time = 
  {
   int_entry_name  = "forced_gc_time" ;
   value = 0;
 }

let gc_basic_clause_elim =
  {
   int_entry_name  = "gc_basic_clause_elim";
   value =0
 }

let total_time = 
  {
   float_entry_name  = "total_time";
   float_value = 0.;
 }

let parsing_time = 
  {
   float_entry_name  = "parsing_time";
   float_value = 0.;
 }

let sem_filter_time = 
  {
   float_entry_name  = "sem_filter_time";
   float_value = 0.;
 }

let pred_elim_time = 
  {
   float_entry_name  = "pred_elim_time";
   float_value = 0.;
 }

let splitting_time = 
  {
   float_entry_name  = "splitting_time";
   float_value = 0.;
 }

    
let out_proof_time = 
  {
   float_entry_name  = "out_proof_time";
   float_value = 0.;
 }
    

let monotx_time = 
  {
   float_entry_name  = "monotx_time";
   float_value = 0.;
 }
 
let subtype_inf_time = 
  {
   float_entry_name  = "subtype_inf_time";
   float_value = 0.;
 }
 

let unif_index_cands_time = 
  {
   float_entry_name  = "unif_index_cands_time";
   float_value = 0.;
 }
 

let unif_index_add_time = 
  {
   float_entry_name  = "unif_index_add_time";
   float_value = 0.;
 }
    

(*--------Propositonal Solver---------*)

let prop_solver_calls = 
  {
   fun_entry_name  = "prop_solver_calls";
   stat_fun        = Undef 
 }


let prop_solver_time = 
  {
   float_entry_name  = "prop_solver_time";
   float_value = 0.;
 }


let prop_fast_solver_calls  = 
  {
   fun_entry_name  =  "prop_fast_solver_calls";
   stat_fun        = Undef 
 }

let prop_fast_solver_time = 
  {
   float_entry_name  = "prop_fast_solver_time";
   float_value = 0.;
 }


let prop_unsat_core_time = 
  {
   float_entry_name  = "prop_unsat_core_time";
   float_value = 0.;
 }


let prop_num_of_clauses = 
  {
   int_entry_name = "prop_num_of_clauses";
   value = 0;
 }

let prop_preprocess_simplified = 
  {
   int_entry_name = "prop_preprocess_simplified";
   value = 0;
 }


let prop_fo_subsumed = 
  {
   int_entry_name = "prop_fo_subsumed";
   value = 0;
 }


(*------- QBF ----------*)

let qbf_q_res = 
  {
   int_entry_name = "qbf_q_res";
   value = 0;
 }

let qbf_prep_cycles = 
  {
   int_entry_name = "qbf_prep_cycles";
   value = 0;
 }

let qbf_num_tautologies =
 {
   int_entry_name = "qbf_num_tautologies";
   value = 0;
 }


(*------BMC1- --------------------------*)

let bmc1_current_bound =
  {
   int_entry_name = "bmc1_current_bound";
   value = -1;
 }

let bmc1_last_solved_bound = 
  {
   int_entry_name = "bmc1_last_solved_bound";
   value = -1;
 }

let bmc1_unsat_core_size = 
  {
   int_entry_name = "bmc1_unsat_core_size";
   value = -1;
 }

let bmc1_unsat_core_parents_size = 
  {
   int_entry_name = "bmc1_unsat_core_parents_size";
   value = -1;
 }

let bmc1_unsat_core_clauses_time = 
  {
   float_entry_name = "bmc1_unsat_core_clauses_time";
   float_value = 0.;
 }

let bmc1_merge_next_func = 
  {
   int_entry_name = "bmc1_merge_next_fun";
   value = 0;
 }


(*------Instantiation------------------*)

let inst_num_of_loops = 
  {
   int_entry_name  =  "inst_num_of_loops";
   value = 0;
 }

let inst_num_in_passive  = 
  {
   fun_entry_name =  "inst_num_in_passive";
   stat_fun        = Undef 
 }

let inst_num_in_active  = 
  {
   int_entry_name  = "inst_num_in_active" ;
   value = 0;
 }
    
let inst_num_moves_active_passive  = 
  {
   int_entry_name  =  "inst_num_moves_active_passive";
   value = 0;
 }


let inst_num_of_learning_restarts  = 
  {
   int_entry_name  =  "inst_num_of_learning_restarts";
   value = 0;
 }

let inst_num_in_unprocessed  = 
  {
   int_entry_name  = "inst_num_in_unprocessed";
   value = 0;
 }

let inst_num_child_elim = 
  {
   int_entry_name  = "inst_num_child_elim" ;
   value = 0;
 }

let inst_num_prop_implied  = 
  {
   int_entry_name  = "inst_num_prop_implied" ;
   value = 0;
 }

let inst_max_lit_activity  = 
  {
   int_entry_name  = "inst_lit_activity" ;
   value = 0;
 }


let inst_lit_activity_moves  = 
  {
   int_entry_name  = "inst_lit_activity_moves" ;
   value = 0;
 }


let inst_num_tautologies  = 
  {
   int_entry_name  = "inst_num_tautologies" ;
   value = 0;
 }

let inst_num_existing_simplified  = 
  {
   int_entry_name  = "inst_num_existing_simplified" ;
   value = 0;
 }

let inst_num_eq_res_simplified =
  {
   int_entry_name  = "inst_num_eq_res_simplified" ;
   value = 0;
 }

let inst_num_from_inst_to_res  = 
  {
   int_entry_name  = "inst_inst_num_from_inst_to_res" ;
   value = 0;
 }

let inst_num_of_clauses = 
  {
   fun_entry_name  =  "inst_num_of_clauses";
   stat_fun        = Undef 
 }


let inst_num_of_dismatching_blockings  = 
  {
   int_entry_name  = "inst_num_of_dismatching_blockings";
   value = 0;
 }


let inst_dismatching_checking_time = 
  {
   float_entry_name = "inst_dismatching_checking_time";
   float_value = 0.
 }

let inst_num_of_non_proper_insts  = 
  {
   int_entry_name  = "inst_num_of_non_proper_insts";
   value = 0;
 }

let inst_num_of_duplicates  = 
  {
   int_entry_name  = "inst_num_of_duplicates";
   value = 0;
 }


(*------Resolution------------------*)

let res_num_of_clauses  = 
  {  
     fun_entry_name  = "res_num_of_clauses";
     stat_fun        = Undef 
   }

let res_num_in_passive = 
  {
   fun_entry_name  = "res_num_in_passive";
   stat_fun        = Undef 
 }

let res_num_in_active = 
  {
   int_entry_name  = "res_num_in_active";
   value = 0;
 }


let res_num_of_loops = 
  {
   int_entry_name  = "res_num_of_loops";
   value = 0;
 }

let res_forward_subset_subsumed  = 
  {
   int_entry_name  = "res_forward_subset_subsumed";
   value = 0;
 }

let res_backward_subset_subsumed = 
  {
   int_entry_name  = "res_backward_subset_subsumed";
   value = 0;
 }

let res_forward_subsumed = 
  {
   int_entry_name  = "res_forward_subsumed";
   value = 0;
 }

let res_backward_subsumed = 
  {
   int_entry_name  = "res_backward_subsumed";
   value = 0;
 }

let res_forward_subsumption_resolution = 
  {
   int_entry_name  = "res_forward_subsumption_resolution";
   value = 0;
 }

let res_backward_subsumption_resolution = 
  {
   int_entry_name  = "res_backward_subsumption_resolution";
   value = 0;
 }
    
let res_clause_to_clause_subsumption = 
  {
   int_entry_name  = "res_clause_to_clause_subsumption";
   value = 0;
 }

let res_orphan_elimination = 
  {
   int_entry_name  = "res_orphan_elimination";
   value = 0;
 }


let res_tautology_del = 
  {
   int_entry_name  = "res_tautology_del" ;
   value = 0;
 }

let res_num_eq_res_simplified =
  {
   int_entry_name  = "res_num_eq_res_simplified" ;
   value = 0;
 }

let res_num_sel_changes = 
  {
   int_entry_name  = "res_num_sel_changes";
   value = 0;
 }

let res_moves_from_active_to_pass = 
  {
   int_entry_name  = "res_moves_from_active_to_pass";
   value = 0;
 }




(*
  let   = 
  {
  int_entry_name  = "";
  value = 0;
  }


  let  = 
  {
  fun_entry_name  = "";
  stat_fun        = Undef 
  }

 *)


(*-----------------*)

let val_dist = 40

let stat_int_to_str s = 
  (space_padding_str val_dist ((tptp_safe_str s.int_entry_name)^":"))
  ^(string_of_int s.value)

(* truncates to 3 digits after .*)
let stat_float_to_str s = 
  (space_padding_str val_dist ((tptp_safe_str s.float_entry_name)^":"))
  ^(string_of_float (truncate_n 3 s.float_value))


let stat_fun_to_str s = 
  let val_str = 
    match s.stat_fun with 
    | Def (f) ->  string_of_int (f ())
    | Undef   -> "undef"
  in
  (space_padding_str val_dist ((tptp_safe_str s.fun_entry_name)^":"))^(val_str)


let stat_int_list_str s_list = 
  list_to_string stat_int_to_str s_list "\n"

let stat_float_list_str s_list = 
  list_to_string stat_float_to_str s_list "\n"

let stat_fun_list_str s_list = 
  list_to_string stat_fun_to_str s_list "\n"

(*--------General--------*)

let gen_fun_stat_list =
  [
   num_of_symbols;
   num_of_terms;
 ]
    
let gen_int_stat_list = 
  [
   abstr_arg_filter_cycles;
   gc_basic_clause_elim;
   forced_gc_time;
 ]

let gen_float_stat_list = 
  [
   parsing_time;   
   unif_index_cands_time;
   unif_index_add_time;
   out_proof_time;
   total_time;
 ]    


(*---- propblem properites ------*)
let problem_props_int_stat_list = 
  [
   clauses;
   conjectures;
   epr;
   horn;
   unary;
   binary;
   lits;
   lits_eq;
 ]

(*---- preprocessing ------*)

let prep_int_stat_list = 
  [
   num_of_splits;
   num_of_split_atoms;
   num_of_reused_defs;
   num_eq_ax_congr_red;
   num_of_sem_filtered_clauses;
   num_of_subtypes;
   monotx_restored_types;
   sat_num_of_epr_types;
   sat_num_of_non_cyclic_types;
   sat_num_of_guarded_non_collapsed_types;
   pure_diseq_elim;
   simp_replaced_by;
   res_preprocessed;
   prep_upred;
   prep_unflattend;
   pred_elim_cands;
   pred_elim;
   pred_elim_cl;
   pred_elim_cycles;
   merged_defs;
   merged_defs_ncl;
   prep_cycles;
 ]

let prep_float_stat_list = 
  [
   pred_elim_time;
   splitting_time;
   sem_filter_time;
   monotx_time;
   subtype_inf_time;
 ]

(*----prop solver-----*)
let prop_solver_fun_stat_list = 
  [
   prop_solver_calls;
   prop_fast_solver_calls;
 ]
    
let prop_solver_int_stat_list = 
  [
   prop_num_of_clauses;
   prop_preprocess_simplified;
   prop_fo_subsumed;   
 ]

let prop_solver_float_stat_list =
  [ prop_solver_time ;
    prop_fast_solver_time ;
    prop_unsat_core_time ]

(*-------qbf ---------*)
let qbf_int_stat_list = 
  [
   qbf_q_res;
   qbf_num_tautologies;
   qbf_prep_cycles;
 ]

(*---- bmc1 --------*)
let bmc1_int_stat_list =
  [ bmc1_current_bound;
    bmc1_last_solved_bound; 
    bmc1_unsat_core_size; 
    bmc1_unsat_core_parents_size;
    bmc1_merge_next_func
 ]

let bmc1_float_stat_list =
  [ bmc1_unsat_core_clauses_time ]

(*-------instantiation --------*)
let inst_fun_stat_list = 
  [
   inst_num_of_clauses;
   inst_num_in_passive;
 ]

let inst_int_stat_list = 
  [
   inst_num_in_active;
   inst_num_in_unprocessed;
   inst_num_of_loops;
   inst_num_of_learning_restarts;
   inst_num_moves_active_passive;
   inst_max_lit_activity;
   inst_lit_activity_moves;
   inst_num_tautologies;
   inst_num_prop_implied;
   inst_num_existing_simplified;
   inst_num_eq_res_simplified;
   inst_num_child_elim;
   inst_num_of_dismatching_blockings;
   inst_num_of_non_proper_insts;
   inst_num_of_duplicates;
   inst_num_from_inst_to_res;
 ]


let inst_float_stat_list = 
  [inst_dismatching_checking_time]

(*----- resolution -------*)
let res_fun_stat_list = 
  [
   res_num_of_clauses;
   res_num_in_passive;
 ]

let res_int_stat_list = 
  [
   res_num_in_active;
   res_num_of_loops;
   res_forward_subset_subsumed;
   res_backward_subset_subsumed; 
   res_forward_subsumed; 
   res_backward_subsumed;
   res_forward_subsumption_resolution;
   res_backward_subsumption_resolution; 
   res_clause_to_clause_subsumption;
   res_orphan_elimination;
   res_tautology_del; 
   res_num_eq_res_simplified;
   res_num_sel_changes;
   res_moves_from_active_to_pass;
 ]

let clear_inst_stat () = 
  List.iter clear_stat_int_entry inst_int_stat_list;
  List.iter clear_stat_fun_entry inst_fun_stat_list

let clear_res_stat () = 
  List.iter clear_stat_int_entry res_int_stat_list;
  List.iter clear_stat_fun_entry res_fun_stat_list

let stat_to_str () = 
  String.concat ""
    [(space_padding_str (val_dist -5) pref_str);
     "Statistics\n\n";
     (s_pref_str ());
     "General\n\n";
     (stat_int_list_str  gen_int_stat_list);"\n";   
     (stat_float_list_str gen_float_stat_list);"\n";   
     (stat_fun_list_str gen_fun_stat_list);"\n\n";
     (s_pref_str ());"Preprocessing\n\n";
     (stat_int_list_str prep_int_stat_list);"\n";
     (stat_float_list_str prep_float_stat_list);"\n\n";
     (s_pref_str ());"Problem properties\n\n";
     (stat_int_list_str problem_props_int_stat_list);"\n\n";
     (s_pref_str ());"Propositional Solver\n\n";
     (stat_fun_list_str prop_solver_fun_stat_list);"\n";
     (stat_int_list_str prop_solver_int_stat_list);"\n";
     (stat_float_list_str prop_solver_float_stat_list);"\n\n";
     (s_pref_str ());"QBF \n\n";
     (stat_int_list_str qbf_int_stat_list);"\n\n";
     (s_pref_str ());"BMC1\n\n";
     (stat_int_list_str bmc1_int_stat_list);"\n";
     (stat_float_list_str bmc1_float_stat_list);"\n\n";
     (s_pref_str ());"Instantiation\n\n";
     (stat_fun_list_str inst_fun_stat_list);"\n";
     (stat_int_list_str inst_int_stat_list);"\n";
     (stat_float_list_str inst_float_stat_list);"\n\n";
     (s_pref_str ());"Resolution\n\n";
     (stat_fun_list_str res_fun_stat_list);"\n";
     (stat_int_list_str res_int_stat_list);"\n"
   ]



let out_stat () = 
  let end_time   = Unix.gettimeofday () in 
  let iprover_total_time = truncate_n 3 (end_time -. iprover_start_time) in 
  assign_float_stat iprover_total_time total_time;
  out_str (stat_to_str ())
    



(*

  type statistics = 
  {

(*---------General--------*)


  (* let lit_activity_check_move  = ref 0*)


  let inst_solver_thershold   = ref 100

 *)
