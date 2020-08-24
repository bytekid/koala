(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2017 Konstantin Korovin and The University of Manchester. 
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
open Git_info
open Options
open Statistics
open Printf
open Bmc1InitTarget

open Logic_interface
open Problem_properties

open Instantiation_env
open Resolution_loop
open Proof_search_schedule


(* record backtrace for debugging          *)
(* compile with -g option to get the trace *)



(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_elapsed
  | D_preprocess
  | D_trace
  | D_trace_prep
  | D_symb_reachability 
  | D_parse
  | D_sub_typing
  | D_axs_distinct 
  | D_axs_less_range
  | D_axs_eq
  | D_sem_filter
  | D_clausify
  | D_apply_after_parsing
  | D_after_parsing_exit

let dbg_gr_to_str = function 
  | D_elapsed -> "elapsed"
  | D_preprocess -> "preprocess"	
  | D_trace -> "trace"
  | D_trace_prep -> "trace_preprocess"
  | D_symb_reachability -> "symb_reach"
  | D_parse -> "parse"
  | D_sub_typing -> "sub_typing"
  | D_axs_distinct  ->  "axs_distinct"
  | D_axs_less_range -> "axs_less_range"
  | D_axs_eq -> "axs_eq"
  | D_sem_filter -> "sem_filter"
  | D_clausify -> "clausify"
  | D_apply_after_parsing -> "apply_after_parsing"
  | D_after_parsing_exit -> "after_parsing_exit"

let dbg_groups =
  [
   (* D_trace_prep; *)
(*   D_elapsed; *)
   D_trace; 
(*   D_symb_reachability; *)
   D_parse; 
   D_sub_typing;  
   D_clausify; 
(*   D_axs_eq; *)
(*   D_clausify; *)
(*    D_preprocess;  *)
(*   D_trace_prep; *)
(*    D_sem_filter;  *)
(*   D_apply_after_parsing; *)
(*   D_after_parsing_exit; *)
 ]
    
let module_name = "sggs"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


exception Time_out_real = Signals.Time_out_real
exception Time_out_virtual = Signals.Time_out_virtual
 
(*------------Out source info -----------------------------*)
let source_info_str = 
  let git_pref = tptp_safe_str "git:" in
  "\n"^(s_pref_str())^" iProver source info "^"\n\n"^
  git_pref^(" date: "^(git_info.git_date))^"\n"^ 
  git_pref^(" sha1: "^(git_info.git_sha1))^"\n"^
  git_pref^" non_committed_changes: "^(string_of_bool git_info.git_non_committed_changes)^"\n"^
  git_pref^" last_make_outside_of_git: "^(string_of_bool !make_outside_git)^"\n" 
									       
  
let out_source_info () = 
  out_str source_info_str

(*-----------------------------------------*)

(* print witness for the AIG mode verification *)
let bmc1_out_witness result =
  if (val_of_override !current_options.bmc1_incremental) && !current_options.aig_mode && !current_options.bmc1_aig_witness_out
  then
    match result with
    (* SAT results in a witness *)
    | PS_result_resolution_sat (res_model, filtered_out_clauses_pre_inst_model)
      ->  failwith "bmc1_out_witness: resoltion sat is not supported "

    | PS_result_instantiation_sat (inst_pre_model, filtered_out_clauses_inst_pre_model)

      -> Bmc1Witness.print_witness ~inst_pre_model ~inst_pre_model_filtered_out:filtered_out_clauses_inst_pre_model (get_val_stat bmc1_current_bound)
    (* UNSAT results in an unsat inform *)
    | PS_result_empty_clause _
    | PS_result_prop_solver_unsat
    | PS_result_prop_solver_unsat_na
    | PS_result_unsat_multiple_cores _
      -> Bmc1Witness.print_unsat ()

let result_handler_prep result =

  (if (val_of_override !current_options.bmc1_incremental)
  then
    (* note that in the case of bmc1 here only preprocess results are handled; *)
    (* results during bmc1 search are handled in bmc1_loop  *)
    Bmc1_loop.result_handler_bmc1_preprocess result
  else
    result_handler_basic result
  );
  (if 
    ((not (val_of_override !current_options.bmc1_incremental)) 
   || (val_of_override !current_options.bmc1_out_stat <> BMC1_Out_Stat_None))
  then 
    out_stat ()
  )
    

let result_handler result =

  result_handler_basic result;
  (if  (val_of_override !current_options.bmc1_incremental)
  then
      bmc1_out_witness result;
  );
  (if 
    ((not (val_of_override !current_options.bmc1_incremental)) 
   || (val_of_override !current_options.bmc1_out_stat <> BMC1_Out_Stat_None))
  then 
    out_stat ()
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
  out_str (Format.sprintf "Timer report: %s: elapsed time %.3fs" status (current -. !last_timestamp));
  (* return current time *)
  current

(* print the elapsed time, keep the time stamp *)
let elapsed status = ignore (elapsed_helper status)

(* print the elapsed time, reset timer *)
let elapsed_ts status = last_timestamp := (elapsed_helper status)

(*----------------Top Function--------------------*)

(*-- run_iprover: initialises, ----------------*)
(*-- parses and then runs main on the preprocessed clauses------*)

let run_iprover () =

  (*-------------------*)
  (*out_source_info ();
  out_str(options_to_str !current_options);*)
  
  let filtered_out_inst_pre_model_ref = ref BCMap.empty in 
  
  try

    (*---------Set System Signals--------------------*)

    Signals.set_sys_signals ();
    Signals.set_time_out ();
    
    (*---------------Parse the input-------------*)

      
    (* we need to switch off type checking during parsing since vars are retyped during parsing *)
    (* restore after parsing *)

    let input_symbol_type_check = !current_options.symbol_type_check in

    !current_options.symbol_type_check <- false;
    
    (*------------- parsing ------------------*)

    dbg D_trace_prep (lazy ("parsing start"));
    dbg_env D_elapsed (fun () -> timestamp ());
    assign_float_stat (get_time_fun 3 ParseFiles.parse) parsing_time;
    dbg_env D_elapsed (fun () -> (elapsed_ts "parsing and AIG"));

    !current_options.symbol_type_check <- input_symbol_type_check;
    
    (*---- after parsing we need to calculate has_conj_symb/has_non_prolific_conj_symb ----------*)
  
    dbg D_trace_prep (lazy ("change_conj_symb_input start"));
    Parser_types.change_conj_symb_input ();
    dbg_env D_elapsed (fun () -> (elapsed_ts "change_conj_symb_input"));

    
    (*-------------------------------*)
    let current_clauses = ref (Parser_types.get_clauses_without_extra_axioms ()) in
    (*-------------------------------*)
      
    let clausify_out () = 
      (
       let clause_list = !current_clauses in (* Parser_types.get_clauses_without_extra_axioms () in*)
       let (epr, non_epr) = List.partition Clause.is_epr clause_list in
       out_str ("% "^pref_str^"Clauses after clausification:\n\n");
       out_str ("% "^pref_str^"EPR clauses "^(string_of_int (List.length epr))^" :\n\n");
       Clause.out_clause_list_tptp epr;
       out_str ("\n\n"^"% "^pref_str^"non-EPR clauses "^(string_of_int (List.length non_epr))^" :\n\n");
       Clause.out_clause_list_tptp non_epr;
       out_str "\n\n";
(*	     exit(0);*)
	    )
    in
    (if !current_options.clausify_out
    then
      (
       clausify_out ();
       exit(0);
      )
    );
    dbg_env D_clausify
	 (
	  fun () ->
	    ( clausify_out ())
	 );

    (*---debug-------*)
    dbg_env D_parse 
	(fun () -> 
	  Logic_interface.out_symbs ();
	  Logic_interface.out_terms (); 
	  Clause.out_clauses_param (Clause.CL_List !current_clauses)
	);
   

    dbg D_trace_prep (lazy ("get_bv_axioms start"));
    let bv_axioms = Eq_axioms.get_bv_axioms () in
    current_clauses := List.rev_append bv_axioms !current_clauses;
    dbg_env D_elapsed (fun () -> (elapsed_ts "get_bv_axioms"));


    dbg_env D_apply_after_parsing 
      (
       fun () -> 
         out_str "";
         out_str "Clauses before splitting_nvd:\n";         
         out_str (Clause.clause_list_to_string !current_clauses);
         current_clauses:=Splitting_nvd.split_clause_list Definitions.def_env_glb 3 !current_clauses;
         out_str "";
         out_str "Clauses after splitting_nvd:\n";
         out_str (Clause.clause_list_to_string !current_clauses);
      );

    dbg_env D_after_parsing_exit 
      (
       fun () -> 
         out_str "";
         dbg D_after_parsing_exit (lazy "Parsed clauses:");
         out_str (Clause.clause_list_to_string !current_clauses);
         out_str "";
        (*--- some dbg on clauses after parsing----*)
         
         let def_map = Def_discovery.get_def_map !current_clauses in 
         dbg D_after_parsing_exit (lazy "Definiton discovery:");
         Def_discovery.out_def_map def_map;
         dbg D_after_parsing_exit (lazy "done; exiting");
         exit 0;
      );


    (* At the moment Parsed_input_to_db.input_clauses_ref are not memory released! *)
    (* we can replace Parsed_input_to_db.input_clauses_ref with *)
    (* global  Parsed_input_to_db.current_clauses, which are gradually replaced by preprocessing but should be carefull how intput caluses are used below: finite_models eq_axioms etc. *)

    (* tsar: AIG does not contains equalities, so unflatten is not applicable *)
    (if (not !current_options.aig_mode) && !current_options.prep_unflatten
    then (
      dbg D_trace_prep (lazy ("unflatten start"));
      current_clauses := Inference_rules.unflatten !current_clauses;
      dbg_env D_elapsed (fun () -> (elapsed_ts "unflatten"));
    ));


      (*-------------------------------------------------*)
      out_str ("");
      out_str (pref_str^"Proving...");
      (*-------------------------------------------------*)

      dbg D_trace (lazy ("In run_iprover: input size = "^(string_of_int(List.length !current_clauses))^"\n"));

      dbg_env D_trace
        (fun () -> 
          dbg D_trace (lazy ("Clauses: before proving \n"));
          Clause.out_clause_list_tptp !current_clauses;
        );


(*----- problem properties --------*)

    (*
    let problem_properties = (Problem_properties.get_prob_props !current_clauses) in 
    Problem_properties.prob_props_to_statistics problem_properties;      
    out_str (pref_str^"Problem Properties \n");
    out_str ("\n"^(Problem_properties.prob_props_to_string problem_properties)^"\n");
    *)
    Format.printf "\nKoala is working ...\n%!";
    let res = SGGS.do_something_smart !current_clauses in
    let s =
      if res = SGGS.Unsatisfiable then "Unsatisfiable"
      else if  res = SGGS.Satisfiable then "Satisfiable"
      else "Unknown"
    in
    Format.printf "\nSZS status %s\n%!" s

  with e -> 
    let msg = Printexc.to_string e
    and stack = Printexc.get_backtrace () in
    Printf.eprintf "there was an error: %s%s\n" msg stack;
    raise e
  
;;

let _ = run_iprover ()

(*---------------------------Commented----------------------------*)
