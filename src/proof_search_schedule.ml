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
open Problem_properties

type res_model = Resolution_loop.res_model
type inst_pre_model = Instantiation_env.inst_pre_model

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "preprocess"	

let dbg_groups =
  [
   D_trace 
 ]
    
let module_name = "proof_search_schedule"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(* setting hard time limit is problematic since the SAT solver can be interrupted *)
exception Schedule_Terminated

type time = float param

type schedule = (named_options * time) list

let time_to_string time =
  match time with
  | Def(float) -> string_of_float float
  | Undef -> "Unbounded"
	
type schedule_clauses = 
    {

(* clauses used for proof search *)
     mutable proof_clauses : clause list; 

(* clauses used for finite model search  (equality may be missing) *)
     mutable finite_model_clauses : clause list;  

(* clauses removed by sem_filter; needed for model building*)
     mutable filtered_out_inst_pre_model : inst_pre_model;  

   }


(* DT multi-pred parameter *)
let bmc1_multi_unsat_stop_prop = true

(* let _ = out_str ("DEFAULT: stop_after_prop_unsat = "^(string_of_bool bmc1_multi_unsat_stop_prop)) *)

(*----------- result handlers --------------------*)

(*
let szs_pref = "\n\n% SZS status "

let unknown_str () = szs_pref^"Unknown\n"
*)

(* "PROVED\n" *)
let proved_str () =
  if !unsat_incomplete_mode 
  then 
     (
      out_warning (" shown unsat in unsat incomplete mode ");
      szs_unknown_str;
     )
  else
    let input_problem_type = (get_some !Parser_types.input_problem_type) in
    if (( input_problem_type = Parser_types.FOF || input_problem_type = Parser_types.TFF)
          && (get_val_stat num_of_input_neg_conjectures > 0) )
    then
      szs_theorem_str
    else
      szs_unsat_str

(*"SATISFIABLE\n"*)
let satisfiable_str () =
  if !sat_incomplete_mode 
  then 
     (
      out_warning (" shown sat in sat incomplete mode ");
      szs_unknown_str;
     )
  else
    if ((get_some !Parser_types.input_problem_type) = Parser_types.FOF 
           && (get_val_stat num_of_input_neg_conjectures > 0))
    then
      szs_counter_sat_str
    else
      szs_sat_str




(*-------------- results after running a proof scehdule ----------------------------------*)

type ps_result = 
  | PS_result_empty_clause of clause 
  | PS_result_resolution_sat of res_model * inst_pre_model (* res_model * filtered_out_inst_pre_model *)
  | PS_result_prop_solver_unsat 
  | PS_result_prop_solver_unsat_na (* unsat without assumtions *)
  | PS_result_instantiation_sat of inst_pre_model * inst_pre_model  (* inst_pre_model * filtered_out_inst_pre_model *)
  | PS_result_unsat_multiple_cores of UnsatCore.unsat_core list

	
(* result_handler_preprocess: if parsing/preprocessing already returns a result *)

(*let result_handler_basic_preprocess result = *)

(* put out statistics before *)

let result_handler_basic result = 
  match result with 
  | PS_result_empty_clause clause -> 
      (

       (* Output status *)
       out_str (proved_str ());
    
       out_str(" Resolution empty clause\n");
       
       (* in this case the unsat is already without answer clauses *)
       if !answer_mode_ref then
	 out_str "% SZS answers Tuple [[]]";
       
       
       (* Output proof from resolution? *)
       if !current_options.res_out_proof then	 
	 (
	  
	  (* Record time when proof extraction started *)
	  let start_time = Unix.gettimeofday () in
	  
	  (* Start proof output *)
	  Format.printf "%% SZS output start CNFRefutation@\n@.";
	  
	  (* Proof output *)
	  (Format.printf "%a@." TstpProof.pp_tstp_proof_resolution clause);
	  
	  (* End proof output *)
	  Format.printf "%% SZS output end CNFRefutation@\n@.";
	  
	  (* Record time when proof extraction finished *)
	  let end_time = Unix.gettimeofday () in
	  
	  (* Save time for proof extraction *)
	  assign_float_stat (end_time -. start_time) out_proof_time;
	  
	 );
      )
 
  | PS_result_prop_solver_unsat | PS_result_prop_solver_unsat_na  ->
      (

       (* Output SZS status *)
       out_str (proved_str ());
  
       (* Output backtrace of unsatisfiable exception *)
       ( if !current_options.dbg_backtrace
       then
	 Format.eprintf
	   "Unsatisfiable exception raised: after main.@\nBacktrace:@\n%s@\n@."
	   (Printexc.get_backtrace ());
	);
       
       (* Output answer first *)
       (if !answer_mode_ref then
	 Prop_solver_exchange.out_answer ();
       );
        
       (* Output proof from instantiation? *)
       (
	 if val_of_override !current_options.inst_out_proof
	 then
	   (
	    
	    (* Record time when proof extraction started *)
	    let start_time = Unix.gettimeofday () in
	    
	    (* Get unsatisfiable core *)
            let uc = Prop_solver_exchange.get_unsat_core ~soft:false () in
            let unsat_core_clauses = UnsatCore.get_clauses uc in
	    
	    (* Start proof output *)
	    Format.printf
	      "@\n%% SZS output start CNFRefutation@\n@.";
	    
	    (* Proof output *)
	    Format.printf
	      "%a@."
	      TstpProof.pp_tstp_proof_unsat_core
	      unsat_core_clauses;
	    
	    (* End proof output *)
	    Format.printf
	      "%% SZS output end CNFRefutation@\n@.";
	    
	    (* Record time when proof extraction finished *)
	    let end_time = Unix.gettimeofday () in
	    
	    (* Save time for proof extraction *)
	    add_float_stat (end_time -. start_time) out_proof_time;
	    
	   )
       );
       
       (* For ISA use
	  % SZS output start ListOfFOF for SYN075 +1
	  ...
	  % SZS output end ListOfFOF for SYN075 +1
	*)
   
      )

  | PS_result_unsat_multiple_cores _ ->
      out_str "Multiple usat cores generated during instantiation";

  | PS_result_resolution_sat (inst_pre_model, filtered_out_inst_pre_model)
    ->
      
      (* Output SZS status *)
      out_str (satisfiable_str ());
      
      if 
	((not (!current_options.sat_out_model = Model_None))
       || 
	 !current_options.sat_out_clauses)
      then
	 Model_res.out_res_model ~res_model:inst_pre_model ~filtered_out_inst_pre_model
      else ()
          
	   
  | PS_result_instantiation_sat (all_clauses, filtered_out_clauses)
    ->
      (* Output SZS status *)
       out_str (satisfiable_str ());
      
       if (not (!current_options.sat_out_model = Model_None))
       then
	 let model =
	   Model_inst.build_model ~inst_pre_model:all_clauses  ~inst_pre_model_filtered_out:filtered_out_clauses in
	 Model_inst.out_model model
       else ()
           

	

(*-------- schedule run with excetions -------------------------------------------*)
(*-------- later all proving excetions are caught and converted to results -------*)

(* prover_functions by default are Undef, in some cases we want to continue with the same or modified externaly prover state which is represented by prover functions *)


let rec schedule_run_exceptions (* ?(prover_functions_param=Undef)*) schedule_clauses schedule =
  
  (* (if !current_options.reset_solvers        *)
  (* then                                      *)
  (*   (Prop_solver_exchange.reset_solvers ()) *)
  (* );                                        *)
  match schedule with
  | (named_options, time_limit) :: tl ->
    if (named_options.options.sat_mode && named_options.options.sat_finite_models)
    then 
      begin
      (* current_options:= named_options.options; *)
	
	set_new_current_options named_options.options;

(*	init_sched_time time_limit; *)

	out_str ((s_pref_str ())^named_options.options_name
		 ^" Time Limit: "^(time_to_string time_limit)^"\n\n");
	
(*
	print_string ((s_pref_str ())^named_options.options_name
		      ^" Time Limit: "^(time_to_string time_limit)^"\n"^
		      (options_to_str !current_options)^"\n\n"
        ^(s_pref_str ())^"\n");
	flush stdout;
*)
	Finite_models_loop.finite_models_loop schedule_clauses.finite_model_clauses
      end
    else 
      begin

	(if not (!current_options.prolific_symb_bound = named_options.options.prolific_symb_bound)
	then 
	  (Problem_properties.change_prolific_symb_input schedule_clauses.proof_clauses;)
	);

      (* current_options:= named_options.options; *)
	set_new_current_options named_options.options;
	out_str ((s_pref_str ())^named_options.options_name
		 ^" Time Limit: "^(time_to_string time_limit)^"\n\n");
(*
	print_string ((s_pref_str ())^named_options.options_name
		      ^" Time Limit: "^(time_to_string time_limit)^"\n"^
		      (options_to_str !current_options)^"\n\n"
		      ^(s_pref_str ())^"Proving...");
	flush stdout;
*)

      (* debug *)
	dbg D_trace (lazy ("In Schedule: input size "^(string_of_int (List.length schedule_clauses.proof_clauses))));
      (* Clause.out_clause_list !input_clauses_ref; *)
      
      (* !current_options.out_options <- Out_All_Opt;                             *)
      (* out_str ("\n current options: "^(options_to_str !current_options)^"\n"); *)
      
(*	init_sched_time time_limit; *)

(*
	let new_prover_functions = 
	  match prover_functions_param with 
	  |Def(pf)  ->  pf (* continue with the old ones *)
	  |Undef -> Proof_search_loop.create_provers_current_options schedule_clauses.proof_clauses in
*)
	try
	  (
           if (!current_options.abstr_ref = []) 
           then 
             (Proof_search_loop.ps_full_loop ~time_limit schedule_clauses.proof_clauses;)
           else
             (Abstr_ref_process.ar_loop
                ~time_limit !current_options.abstr_ref schedule_clauses.proof_clauses;)
             (* (Axiom_selection.axiom_selection_loop
              *    ~time_limit !current_options.abstr_ref schedule_clauses.proof_clauses;) *)
(*
           if !current_options.abstr_ref_arg_filter
           then
             (Abstr_ref_arg_filter.abstr_ref_gr_filter_loop ~time_limit schedule_clauses.proof_clauses;)
           else 
           
             if (!current_options.abstr_ref_sig || !current_options.abstr_ref_subs)
             then
               (Axiom_selection.axiom_selection_loop ~time_limit schedule_clauses.proof_clauses;)
             else
               (Proof_search_loop.ps_full_loop ~time_limit schedule_clauses.proof_clauses;)
*)
	  )
	with
	| Proof_search_loop.PS_loop_time_out(full_loop_counter) ->
            out_str ("Time Out after: "^(string_of_int full_loop_counter)^" full_loop iterations\n");
(* TODO
            schedule_clauses.proof_clauses <- 
	      Proof_search_loop.simplify_input new_prover_functions schedule_clauses.proof_clauses;
*)
         (*   out_str (" \n\n commented: schedule_clauses.sat_clauses <- simplify_input prover_functions schedule_clauses.sat_clauses \n\n");	  *) 
        (* TODO: check why does not work  *)
(*         finite_model_clauses_ref  := simplify_input prover_functions !finite_model_clauses_ref; *)

       (*     provers_clear_and_remove_all (); *)
(*            Proof_search_loop.clear_all_provers new_prover_functions;*)
            clear_memory ();
            schedule_run_exceptions schedule_clauses tl

      (* One should be careful here,                     *)
      (* since if Inst.  Satisfiable the model is passed *)
      (* and resolution empty clause, proof  is passed, clearing provers should not *)
      (* destroy models/proofs (at the moment it does not) *)

      | x ->
        (* cannot clear since exception can return context as model or unsat core *)
        (* provers_clear_and_remove_all ();    *)
        (* clear_all_provers prover_functions; *)
          raise x
      end

  | [] -> raise Schedule_Terminated

let try_prop_solve () =
  (* try in assumpiton of the multiple unsat cores *)
  let rec try_solve_unsat () =
    Prop_solver_exchange.clear_soft_assumptions ();
    if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
    then (* collect unsat core and re-run *)
      (  
	 Prop_solver_exchange.process_unsat_result ();
	 try_solve_unsat ()
      )
    else (* SAT: return if we have unsat cores collected *)
      if bmc1_multi_unsat_stop_prop && (list_non_empty !Prop_solver_exchange.unsat_cores)
      then
        raise (Prop_solver_exchange.MultipleUnsat !Prop_solver_exchange.unsat_cores)
  in
  (* both multi-unsat and unsat are covered by this *)
  try_solve_unsat ()

(* schedule_run should not raise exceptions *)
let schedule_run (* ?(prover_functions_param = Undef)*)  schedule_clauses schedule = 
  try 
    dbg D_trace (lazy ("schedule_run before solver"));

    List.iter Prop_solver_exchange.add_clause_to_solver schedule_clauses.proof_clauses;
 
    try_prop_solve ();
  
    dbg D_trace (lazy ("schedule_run after solver"));  


    schedule_run_exceptions (* ~prover_functions_param *) schedule_clauses schedule; 

    failwith "schedule_run_exceptions: should happen"

  with 
        (* Unsatisfiable in propositional solver, not by empty clause in
       resolution *)
(*  | Prop_solver_exchange.Unsatisfiable

  | PropSolver.Unsatisfiable
  | Instantiation.Unsatisfiable ->
*)
      (* |Discount.Unsatisfiable *)

  | Unsatisfiable_gr       
    ->
      assert (Prop_solver_exchange.soft_assumptions_is_empty ());
      PS_result_prop_solver_unsat

  | Unsatisfiable_gr_na | Finite_models.Unsatisfiable_fm_na
    ->
(*      assert (Prop_solver_exchange.soft_assumptions_is_empty ()); *)
      PS_result_prop_solver_unsat_na

  | Prop_solver_exchange.MultipleUnsat unsat_cores ->
      PS_result_unsat_multiple_cores unsat_cores
     
  | Empty_clause (clause) ->      
      PS_result_empty_clause (clause)
      
	
  | Resolution_loop.Res_satisfiable res_model ->
      PS_result_resolution_sat (res_model, schedule_clauses.filtered_out_inst_pre_model)
      
	
  | Instantiation_loop.Inst_satisfiable inst_pre_model ->      
      PS_result_instantiation_sat (inst_pre_model, schedule_clauses.filtered_out_inst_pre_model)


      	

(*--------------------------------------------------------*)


let is_large_theory () =
  (get_val_stat num_of_input_clauses) > !current_options.lt_threshold


(*--------------------------------------------------------*)

let schedule_to_many_axioms_schedule schedule =
  if (is_large_theory ())
      && (get_val_stat num_of_input_neg_conjectures > 0)
  then
    (out_str (pref_str^"Large theory \n");
     let f (opt, time) = ((Options.named_opt_to_many_axioms_named_opt1 opt), time)
     in List.map f schedule
    )
  else
    schedule


let strip_conj_schedule schedule =
  if (get_val_stat num_of_input_neg_conjectures = 0)
  then
    let f (opt, time) = ((Options.strip_conj_named_opt opt), time)
    in List.map f schedule
  else schedule

(*returns (list_no_last,last)  *)
let get_last_elm_list list =
  let rec get_last_elm_list' rest list =
    match list with
    | h::[] -> ((List.rev rest), h)
    | h:: tl -> get_last_elm_list' (h:: rest) tl
    |[] -> failwith " iprover.ml: get_last_elm_list list is empty"
  in
  get_last_elm_list' [] list

let schedule_no_learinig_restarts schedule =
  let f (opt, time) =
    let new_opt =
      { opt with
	options = { opt.options with
		    inst_learning_start = 30000000
		  }
      } in (new_opt, time)
  in List.map f schedule
    
let schedule_no_learinig_restarts_between schedule =
  let (rest, last) = get_last_elm_list schedule in
  let new_rest = schedule_no_learinig_restarts rest in
  new_rest@[last]


let trivial_schedule () =
  [(input_named_options, Undef)]
    
	      
(* for now a schedule is defined manualy here and not in the options *)
let init_schedule1 () =
  let time1 = Def(10.) in
  let option1 = named_option_1 () in
  let time2 = Def(10.) in
  let option2 = named_option_2 () in
  let time3 = Def(10.) in
  let option3 = named_option_3 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1); (option2, time2); (option3, time3); (option_last, time_last)]

let init_schedule2 () =
  let time1 = Def(10.) in
  let option1 = named_option_1 () in
  let time2 = Def(10.) in
  let option2 = named_option_2 () in
  let time3 = Def(15.) in
  let option3 = named_option_4 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1); (option2, time2); (option3, time3); (option_last, time_last)]

let init_schedule3 () =
  let time1 = Def(15.) in
  let option1 = named_option_1 () in
  let time2 = Def(15.) in
  let option2 = named_option_2 () in
  let time3 = Def(15.) in
  let option3 = named_option_3 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1); (option2, time2); (option3, time3); (option_last, time_last)]

let init_schedule3_1 () =
  let time1 = Def(15.) in
  let option1 = named_option_1_1 () in
  let time2 = Def(15.) in
  let option2 = named_option_2_1 () in
  let time3 = Def(15.) in
  let option3 = named_option_3_1 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1); (option2, time2); (option3, time3); (option_last, time_last)]

(* like option 1 but with shorter times *)
let init_schedule4 () =
  let time1 = Def(15.) in
  let option1 = named_option_1 () in
  (* let time2 = Def(10.) in
     let option2 = named_option_2 () in
     let time3 = Def(10.) in
     let option3 = named_option_3 () in *)
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1);(*(option2,time2);(option3,time3);*)(option_last, time_last)]

let init_schedule5 () =
  let time1 = Def(25.) in
  let option1 = input_named_options in
  let time2 = Def(15.) in
  let option2 = named_option_1 () in
  let time3 = Def(15.) in
  let option3 = named_option_2 () in
  let time4 = Def(15.) in
  let option4 = named_option_3 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1); (option2, time2); (option3, time3); (option4, time4); (option_last, time_last)]

let init_schedule5_no_res_last () =
  let time1 = Def(10.) in
  let option1 = input_named_options in
  let time2 = Def(10.) in
  let option2 = named_option_1 () in
  let time3 = Def(10.) in
  let option3 = named_option_2 () in
  let time4 = Def(10.) in
  let option4 = named_option_3 () in
  let time_last = Undef in
  let option_last =
    { options_name = input_named_options.options_name^" \"--resolution_flag false\"";
      options = { input_named_options.options with resolution_flag = false }}
  in
  [(option1, time1); (option2, time2); (option3, time3); (option4, time4); (option_last, time_last)]

let init_schedule5_1 () =
  let time1 = Def(25.) in
  let option1 = input_named_options in
  let time2 = Def(15.) in
  let option2 = named_option_1_1 () in
  let time3 = Def(15.) in
  let option3 = named_option_2_1 () in
  let time4 = Def(15.) in
  let option4 = named_option_3_1 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(option1, time1); (option2, time2); (option3, time3); (option4, time4); (option_last, time_last)]

let init_schedule5_2 () =
  let time1 = Def(25.) in
  let option1 = named_option_1_2 () in
  let time2 = Def(15.) in
  let option2 = named_option_1 () in
  let time3 = Def(15.) in
  let option3 = named_option_2 () in
  let time4 = Def(15.) in
  let option4 = named_option_3 () in
  let time_last = Undef in
  let option_last = named_option_1_2 () in
  [(option1, time1); (option2, time2); (option3, time3); (option4, time4); (option_last, time_last)]

let init_schedule5_inst_first () =
(*
  let time_2 = Def(5.) in
  let option_2 =
    { options_name = input_named_options.options_name^" \"--resolution_flag false; --inst_lit_sel_side num_var\"";
      options = { input_named_options.options with 
                  resolution_flag = false;
                  inst_lit_sel_side = CM_num_var;}} in
*)
(*  let time_1 = Def(5.) 
  let option_1 =
    { options_name = input_named_options.options_name^" \"--resolution_flag false; --inst_lit_sel_side none\"";
      options = { input_named_options.options with 
                  resolution_flag = false;
                  inst_lit_sel_side = CM_none;}} in
*)
  let time0 = Def(10.) in
  let option0 =
    { options_name = input_named_options.options_name^" \"--resolution_flag false --inst_lit_sel_side none\"";
      options = { input_named_options.options with 
                  resolution_flag = false;
                  inst_lit_sel_side = CM_none;          
                }} 
  in
  let time1 = Def(25.) in

  let option1 = 
    { options_name = input_named_options.options_name^"\"--res_lit_sel adaptive --res_lit_sel_side num_symb\"";
      options = { input_named_options.options with 
                  res_lit_sel = Res_adaptive_max;
                  res_lit_sel_side = CM_num_symb };
    }
  in 

  let time2 = Def(15.) in
  let option2 = named_option_1 () in
  let time3 = Def(15.) in
  let option3 = named_option_2 () in
  let time4 = Def(15.) in
  let option4 = named_option_3 () in
  let time_last = Undef in
  let option_last = input_named_options in
  [(*(option_2, time_2);*) (*(option_1, time_1);*)(option0, time0); (option1, time1); (option2, time2); (option3, time3); (option4, time4); (option_last, time_last)]

(*
  let init_schedule () =
  out_str (pref_str^"Schedule 1 is on \n");
  init_schedule1 ()
 *)
(*
  let init_schedule () =
  out_str (pref_str^"Many Axioms, Schedule 1 is on \n");
  schedule_to_many_axioms_schedule (init_schedule1 ())
 *)

(*
  let init_schedule () =
  if num_of_input_clauses > !current_options.axioms_threshold
  then
  ( out_str (pref_str^"Schedule 3 is on, Many Axioms, no restarts \n");
  schedule_to_many_axioms_schedule (schedule_no_learinig_restarts (init_schedule3 ()))
  )
  else
  (out_str (pref_str^"Schedule 3 is on, no restarts between \n");
  schedule_no_learinig_restarts_between (init_schedule3 ()))

 *)

(*
  let init_schedule () =
  if num_of_input_clauses > !current_options.axioms_threshold
  then
  ( out_str (pref_str^"Schedule 3 is on, Many Axioms, no restarts \n");
  schedule_to_many_axioms_schedule (schedule_no_learinig_restarts (init_schedule3 ()))
  )
  else
  (out_str (pref_str^"Schedule 3 is on \n");
  (init_schedule3 ()))
 *)

(*
  let init_schedule () =
  if num_of_input_clauses > !current_options.axioms_threshold
  then
  ( out_str (pref_str^"Schedule 1 is on, Many Axioms, no restarts \n");
  schedule_to_many_axioms_schedule (schedule_no_learinig_restarts (init_schedule1 ()))
  )
  else
  (out_str (pref_str^"Schedule 1 is on \n");
  (init_schedule1 ()))
 *)

(*
  let init_schedule () =
  out_str (pref_str^"Schedule 5 is on \n");
  strip_conj_schedule
  (schedule_to_many_axioms_schedule (init_schedule5 ()))
 *)
(*
  let init_schedule () =
  out_str (pref_str^"Schedule 5_2 is on \n");
  strip_conj_schedule
  (schedule_to_many_axioms_schedule (init_schedule5_2 ()))
 *)

(*
  let init_schedule () =
  out_str (pref_str^"Schedule 5_1 is on \n");
  strip_conj_schedule
  (schedule_to_many_axioms_schedule (init_schedule5_1 ()))
 *)


let sat_schedule_gen () =
  out_str (pref_str^"Schedule Sat is on\n");
  let time1 = Def(30.) in
  let option1 = (named_opt_sat_mode_off input_named_options) in
  let time2 = Def(10.) in
  let option2 = named_option_1 () in
  let time3 = Def(10.) in
  let option3 = named_option_2 () in
  let time4 = Def(10.) in
  let option4 = named_option_3 () in
  let time_last = Undef in
  let option_last = named_option_finite_models() in
  strip_conj_schedule [(option1, time1); (option2, time2); (option3, time3); (option4, time4); (option_last, time_last)]

let epr_non_horn_non_eq_schedule_before_2018_06 () =
  out_str (pref_str^"Schedule EPR non Horn non eq is on\n");
  let time1 = Def(20.) in 
  let option1 = 
    let nopt3 = named_option_3 () in
    {options_name =  nopt3.options_name^" \"--instantiation_flag false\"";
     options = { nopt3.options with 
		 instantiation_flag = false; 
		 res_time_limit = 200.;
		 res_backward_subs = Subs_Subset;
		 res_backward_subs_resolution = false;
		 res_forward_subs_resolution = true;
	(*	 res_to_prop_solver = PS_result_to_Solver_None;
		 res_prop_simpl_new = false;
		 res_prop_simpl_given = false; 
*)
 
	       }} 
  in

  let time2 = Def(70.) in 
  let option2 =
    { 
      options_name = input_named_options.options_name^" \"--resolution_flag false\"";
      options = { input_named_options.options with 
		  inst_prop_sim_given = false;
		  resolution_flag = false;		 
                  inst_lit_sel = [Lit_Prop true; Lit_Num_of_Symb true;  Lit_Sign false; Lit_Num_of_Var true; ]; 
		}} in

(*  let time3 = Def(10.) in 
  let option3 = named_option_3 () in
 *)
  let time_last = Undef in
  let option_last = named_option_epr_non_horn_non_eq () in
  [(option2, time2);  (option1, time1);   (option_last, time_last)]

(*-----------------*)
let epr_non_horn_non_eq_schedule_single_opt () =
  out_str (pref_str^"Schedule EPR non Horn non eq is on\n");  
  let time_last = Undef in
  let option_last = named_option_epr_non_horn_non_eq () in  
  [(option_last, time_last)]
    
let epr_non_horn_non_eq_schedule () =
  epr_non_horn_non_eq_schedule_before_2018_06 () 

(*-----------------*)
let epr_non_horn_eq_schedule () =
  out_str (pref_str^"Schedule EPR non Horn eq is on\n");
  let time_last = Undef in
  let option_last = named_option_epr_non_horn_eq () in 
  [(option_last, time_last)]
    

(*-----------------*)
let epr_horn_non_eq_schedule () =
  out_str (pref_str^"Schedule EPR Horn non eq is on\n");
  let time_last = Undef in
  let option_last = named_option_epr_horn_non_eq () in 
  [(option_last, time_last)]
    



(*let _ = out_str "\n Schedule 5 was the best before\n"*)

(*
  let init_schedule () =
  out_str (pref_str^"Schedule 5 is on \n");
  strip_conj_schedule
  (schedule_to_many_axioms_schedule (init_schedule5 ()))
 *)

(*let _ = out_str "\n now init_schedule5_no_res_last, change later!\n "*)

let dynamic_sched_5 problem_properties =
  if ((is_epr problem_properties) && (not (is_horn problem_properties)) &&  (not (has_eq problem_properties)))
  then
    strip_conj_schedule ( (* schedule_to_many_axioms_schedule *)
			   (epr_non_horn_non_eq_schedule ()))
      (*  [((named_option_epr_non_horn  ()),Undef)])    *)
  else
    if  ((is_epr problem_properties) && (not (is_horn problem_properties)) &&  (has_eq problem_properties))
    then
      strip_conj_schedule ( (* schedule_to_many_axioms_schedule *)
      (epr_non_horn_eq_schedule ()))
    else
      if ((is_epr problem_properties) && (is_horn problem_properties)) &&  (not (has_eq problem_properties))
      then
        strip_conj_schedule ( (* schedule_to_many_axioms_schedule *)
        (epr_horn_non_eq_schedule ()))
(*	[((named_option_epr_horn_non_eq ()), Undef)]) *)
      else
        (out_str (pref_str^"Schedule dynamic 5 is on \n");
         (*
	   strip_conj_schedule
	   (schedule_to_many_axioms_schedule (init_schedule5 ()))
	  *)
       (*
	 strip_conj_schedule
	 (schedule_to_many_axioms_schedule (init_schedule5_no_res_last ()))
	*)
         (*
	 strip_conj_schedule
	   (schedule_to_many_axioms_schedule (init_schedule5 ()))
	*)
       (* -2012: init_schedule5_inst_first () *)
       
         strip_conj_schedule
	   ((* schedule_to_many_axioms_schedule *)(init_schedule5_inst_first ()))	 
        )


let sat_schedule problem_properties =
  if ((is_epr problem_properties) && (not (is_horn problem_properties)) &&  (not (has_eq problem_properties)) )
  then
    strip_conj_schedule ( (* schedule_to_many_axioms_schedule *)
			   (epr_non_horn_non_eq_schedule ()))
      (*  [((named_option_epr_non_horn  ()),Undef)])    *)
  else
    if  ((is_epr problem_properties) && (not (is_horn problem_properties)) &&  (has_eq problem_properties))
    then
      strip_conj_schedule ( (* schedule_to_many_axioms_schedule *)
      (epr_non_horn_eq_schedule ()))
    else
  
    if (is_epr problem_properties) && (is_horn problem_properties) && (not (has_eq problem_properties))
    then
      strip_conj_schedule (  schedule_to_many_axioms_schedule 
			       (epr_horn_non_eq_schedule ()))
    else
      strip_conj_schedule
	( schedule_to_many_axioms_schedule  (sat_schedule_gen ()))

let default_schedule problem_properties =
  dynamic_sched_5 problem_properties

let verification_epr_schedule_old () =
  let time_last = Undef in
  let option_last = named_option_verification_epr_old () in
  strip_conj_schedule [(option_last, time_last)]

let verification_epr_schedule_tables () =
  let time_last = Undef in
  let option_last = named_option_verification_epr_tables () in
  strip_conj_schedule [(option_last, time_last)]

let verification_epr_schedule () =
  let time_last = Undef in
  let option_last = named_option_verification_epr () in
  strip_conj_schedule [(option_last, time_last)]


let change_first_option f sched = 
  let modif_schd = 
    match sched with 
    |[]     -> failwith "change_last_option: sched should not be empty"
    | h::tl -> (f h) :: tl 
  in
  modif_schd

let change_last_option f sched = 
 List.rev (change_first_option f (List.rev sched))

(*
  let rev_sched = List.rev sched in 
  let rev_modif = 
    match rev_sched with 
    |[]     -> failwith "change_last_option: sched should not be empty"
    | h::tl -> (f h) :: tl 
  in
  List.rev rev_modif
*)

let abstr_ref_change_named_opt b nopt = 
  if ( nopt.options.abstr_ref != [])
  then 
    nopt
  else 
    let abstr_ref = [Abstr_ref_sig;Abstr_ref_subs;Abstr_ref_arg_filter] in
    let new_nopt = 
      { 
        options_name = input_named_options.options_name^" \"--abstr_ref "^(abstr_ref_list_type_to_str abstr_ref)^" \"";
        options = { nopt.options with abstr_ref = abstr_ref}
      }
    in
    new_nopt
 (* if (b = nopt.options.abstr_ref_arg_filter) 
  then 
    nopt
  else    
    let new_nopt = 
      { 
        options_name = input_named_options.options_name^" \"--abstr_ref_arg_filter "^(string_of_bool b)^" \"";
        options = { nopt.options with abstr_ref_arg_filter = true}
      }
    in
    new_nopt
*)




let abstr_ref_schedule problem_properties = 
  out_str (pref_str^"Schedule abstr_ref is on \n");
  let f (nopt, time) = ((abstr_ref_change_named_opt true nopt),time) in

(*  change_first_option f (default_schedule (problem_properties)) *)
  change_last_option f (default_schedule (problem_properties)) 


let abstr_ref_sat_schedule problem_properties = 
  out_str (pref_str^"Schedule abstr_ref_sat is on \n");
  let f (nopt, time) = ((abstr_ref_change_named_opt true nopt),time) in

(*  change_first_option f (default_schedule (problem_properties)) *)
  change_last_option f (sat_schedule (problem_properties)) 



let smac_tmp_schedule () = 
   out_str (pref_str^"Schedule smac_tmp is on \n");
  [((named_option_smac_tmp ()), Undef)]
    
