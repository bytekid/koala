(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006 -2016 Konstantin Korovin and The University of Manchester.
   This file is part of iProver - a theorem prover for first - order logic.

   iProver is free software: you can redistribute it and / or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver. If not, see < http:// www.gnu.org / licenses />. *)
(*----------------------------------------------------------------------[C]-*)

open Lib
open Options
open Statistics
open Logic_interface
open Simplify
open Resolution_env
open Resolution_sel

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_trace
  | D_passive
  | D_given
  | D_input
  | D_sim
  | D_res_change_sel
  | D_splitting

let dbg_gr_to_str = function
  | D_trace -> "trace"
  | D_passive -> "passive"
  | D_given     -> "given"
  | D_input     -> "input"
  | D_sim       -> "sim"
  | D_res_change_sel -> "res_change_sel"
  | D_splitting -> "splitting"

let dbg_groups =
  [
    D_trace; 
    D_sim; 
    D_passive; 
   D_given;
   D_splitting; 
    D_input;  
    D_res_change_sel; 
 ]

let module_name = "resolution_loop"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(* exception Unsatisfiable *)

(*
exception Res_satisfiable of all_clauses

exception DontKnow
*)
(* in order to get the proof we need to pass the empty clause *)
(* exception Empty_Clause of clause*)


(*-----------------------*)

type res_state = 
    {
     (* TODO add res_options; separate from current options ? *)
(*     mutable res_context       : context; *)  (* all clauses *)
     mutable res_sim_state     : sim_state; (* all clauses are added first to sim  *)
     mutable res_input_clauses : BCSet.t;   (* non-dead clauses are copied to res_context *)

     mutable res_cl_params     : res_cl_param BCMap.t;
     mutable res_unif_index    : ClauseUnifIndex.t;
     mutable res_passive_queue : PassiveQueues.passive_queue;

     mutable res_prep_only     : bool;
     mutable res_is_usable     : bool;
     mutable res_simplified_input : BCSet.t;

   }


(* TODO: create res_options *)

let res_create_state ~res_prep_only (* ~input_clauses *)= 
(*  let res_context = Clause.context_copy ~non_dead:true input_clauses in *)

(* sim_state *) (* TODO: adjust to input/res_options *)
  let sim_options = 
    {
     sim_add_to_prop_solver =  (*true;*) (not (!current_options.res_to_prop_solver = Res_to_Solver_None));
     sim_use_ss_index = true;
     sim_use_sub_index =  true; 
     sim_add_to_sub_index_test = (fun _clause -> true);
(* (fun clause -> ((Clause.num_of_var clause) <= 10 && (Clause.length clause) <= 20));*)
   }
  in
  let res_sim_state = sim_create sim_options in

(* passive queue *)
  let passive_queue_type = !current_options.res_passive_queue_type in
  let priorities = !current_options.res_passive_queues in
  let mults = !current_options.res_passive_queues_freq in

  dbg D_passive (lazy ("priorities:"^(pass_queues_type_to_str priorities)
                         ^", freqs:"^(passive_queue_freqs_to_str mults)));

  let res_passive_queue = PassiveQueues.create_passive_queue passive_queue_type priorities mults in

(* stats *)
  assign_fun_stat
    (fun () -> context_size ~non_dead:true (Simplify.sim_get_context res_sim_state)) res_num_of_clauses;

  assign_fun_stat (fun () -> PassiveQueues.num_elem res_passive_queue) res_num_in_passive;

(* res_state *)
  {
(*   res_context          = res_context; *)
   res_sim_state        = res_sim_state;
   res_input_clauses    = BCSet.empty;

   res_cl_params        = BCMap.empty;
   res_unif_index       = ClauseUnifIndex.create ();
   res_passive_queue    = res_passive_queue;

   res_prep_only        = res_prep_only;
   res_is_usable        = true;
   res_simplified_input = BCSet.empty;
 }


(*-------------------------------------*)
type res_model = res_cl_param BCMap.t

(* res_model: active clauses with params *)
let res_get_model rs = 
  let f cl cl_param = res_is_in_active cl_param in
  BCMap.filter f rs.res_cl_params

(*-------------------------------------*)

(* internal exceptions *)

exception Given_clause_is_dead

exception Res_satisfiable of res_model


let get_is_dead rs clause = Simplify.sim_is_dead rs.res_sim_state clause

let clause_in_rs rs clause = BCMap.mem clause rs.res_cl_params

(*
  module type InputM =
  sig
  val res_module_name : string
  (* we assume that input clauses are normalised with terms in *)
  (* Parsed_input_to_db.term_db_ref *)
  val input_clauses : clause list
  
  (* this insance is used only for res_preprocessing clauses *)
  val is_res_prepocessing : bool
  
  end

  module Make (InputM: InputM) =
  struct
 *)
    (*  let res_module_name = InputM.res_module_name *)
(*    let input_clauses = ref InputM.input_clauses *)

let get_all_input_clauses rs = rs.res_input_clauses
    
let get_cl_param rs clause = 
  try 
    BCMap.find clause rs.res_cl_params
  with 
    Not_found -> failwith ("resolution_loop: cl_param is not defined: "^(Clause.to_string clause))
        
        (* replace with watched clauses later *)
(* let simplified_input = ref (context_create (List.length !input_clauses)) *)

        (*	let prep_input = ref (context_create (List.length input_clauses))*)	

(* TODO clean-up *)	
let record_simplified rs clause  = 
  if !current_options.res_sim_input && (BCSet.mem clause rs.res_input_clauses) 
  then 
    (
     (*out_str "\n Record Simplified:\n";
       Format.printf "@[%a @]@.@[%a @]@."
       (TstpProof.pp_clause_with_source_gs ~clausify_proof:false ) clause
       (Clause.pp_clause_params Clause.param_out_list_gen) clause;
      *)
     rs.res_simplified_input <- BCSet.add clause rs.res_simplified_input
         (* ignore (context_add !simplified_input clause)  *)
    )
  else 
    ()

(*
  let res_clause_register_subsumed_by rs ~by c =
  clause_register_subsumed_by rs.res_context by c;
  if (Clause.equal_bc by c)
  then ()
  else
  (record_simplified rs c)
 *)

let _ = clear_res_stat ()

(*----- get selected literals of the clause assuming sel lits are defined ------*)
let get_selected_lits cl_param =
  (* choose selected literals *)
  let sel_lits =
    try
      res_get_sel_lits cl_param
    with 
      Res_sel_lits_undef ->
        failwith "get_selected_lits: clause should have selected literals here"
  in
  (* return that literals *)
  sel_lits

(*---- get unification candidates for a (negated) literal -----*)
let get_compl_unif_candidates rs lit =
  ClauseUnifIndex.get_unif_candidates rs.res_unif_index (add_compl_lit lit)

let add_to_active rs clause cl_param selected_literals =
  dbg D_trace (lazy (
	       ("add_to_active: "^(Clause.to_string clause)
		^" selected lits: "
		^(Term.term_list_to_string selected_literals)
	       )));
  let add_lit sel_lit = ClauseUnifIndex.add_clause_with_sel rs.res_unif_index sel_lit clause in  
  res_set_in_active true cl_param;
  incr_int_stat 1 res_num_in_active;
  List.iter add_lit selected_literals
    

    (*--------------------Passive QUEUES-----------------*)
    
    
    (* passive queue shortcuts *)
let finalise_passive rs = PassiveQueues.finalise rs.res_passive_queue
let remove_from_passive rs = 
  let clause = PassiveQueues.remove_from_passive rs.res_passive_queue in 
  dbg D_passive (lazy ("rm pq: "^(Clause.to_string clause)));
  clause

let add_to_passive' rs clause = 
  dbg D_passive (lazy ("add pq: "^(Clause.to_string clause)));
  PassiveQueues.add_to_passive rs.res_passive_queue clause
    
    (* TODO change empty clause check to unprocessed *)
let add_to_passive rs clause =
  check_empty_clause clause;
  add_to_passive' rs clause

(*---------- End Passive QUEUES -----------*)


(*------------ simplifications ------------*)
    
let eliminate_from_unif_index_cl_param rs clause cl_param =
  res_set_in_active false cl_param;
  incr_int_stat (-1) res_num_in_active;
  let selected_literals = get_selected_lits cl_param in
  let elim_lit sel_lit = ClauseUnifIndex.elim_clause_with_sel rs.res_unif_index sel_lit clause in
  try
    List.iter elim_lit selected_literals;
  with
    Not_found -> ()


let eliminate_from_unif_index rs clause = 
  eliminate_from_unif_index_cl_param rs clause (get_cl_param rs clause)
    
let eliminate_clause_cl_param rs clause cl_param =  
  Simplify.assign_dead_and_remove_from_indexes rs.res_sim_state clause;

(* we keep clause in the context *)
(* TODO: should be moved to Simplify
   Clause.assign_replaced_by (Def(Clause.RB_subsumption (main_clause))) c; 
   res_clause_register_subsumed_by ~by:main_clause c
 *)

  (if (res_is_in_active cl_param)
  then
    (eliminate_from_unif_index_cl_param rs clause cl_param;)
  else ()
  )

let eliminate_clause rs clause =  
  dbg D_trace (lazy ("eliminate_clause: "^(Clause.to_string clause)));
  if (clause_in_rs rs clause) 
  then 
    eliminate_clause_cl_param rs clause (get_cl_param rs clause)
  else 
    ()

let check_sim_mem rs c =    
  (if 
    (Simplify.sim_mem_clause rs.res_sim_state c) ||
    (not ((Simplify.forward_subset_subsume rs.res_sim_state c) == c))
  then 
    raise Eliminated
  else c
  )
    
(* can raise Empty_clause(clause) *)
let check_empty_clause_return clause = 
  check_empty_clause clause;
  inconsistent_with_assumptions clause;
  clause


(* can raise Eliminated *)    
let sim_fwd_new_cl_fun_list rs = 
  let o = !current_options in
(* sim functions in the list: f c -> c' or raise Eliminated,   *)
(* if c' is in sim_state then Eliminated will be raised so we assume that f does not add c' into the sim_state context *) 
  [ 
    check_sim_mem rs;
    check_empty_clause_return;
    Simplify.tautology_elim;
    Simplify.equality_resolution_simp;
    Simplify.forward_subset_subsume rs.res_sim_state; 
    if o.res_prop_simpl_new then (Simplify.forward_prop_subsume (* rs.res_sim_state *)) else id_fun;
  ]



let simplify_light_new_clause rs clause =

  dbg D_trace (lazy ("simplify_light_new_clause: "^(Clause.to_string clause)));

  let forward_light_fun_list = sim_fwd_new_cl_fun_list rs in
  let sim_clause = fix_point (fold_left_fun_list forward_light_fun_list) clause in  
  let (new_clause,s_subsumed_clauses) = Simplify.sim_add_clause rs.res_sim_state sim_clause in

  dbg_env D_sim
    (fun () -> 
      (if (not (new_clause == clause)) 
      then dbg D_sim (lazy ("new_clause: "^(Clause.to_string clause))));

      (if (not (s_subsumed_clauses = [])) 
      then dbg D_sim (lazy ("bwd_subsumed_clauses: "^(Clause.clause_list_to_string s_subsumed_clauses))));
    );
  
  List.iter (eliminate_clause rs) s_subsumed_clauses;  
  incr_int_stat (List.length s_subsumed_clauses) res_backward_subset_subsumed;
  
  
(*  TODO: res_clause_register_subsumed_by
    (if not (s_subsumed_clauses = [])
    then
    (
(* out_str ("Is simpl"^(Clause.to_string main_clause)^"\n"); *)

    Clause.set_ps_simplifying true main_clause;
    List.iter
    (fun c -> 
    Clause.assign_replaced_by (Def(Clause.RB_subsumption (main_clause))) c; 
    res_clause_register_subsumed_by ~by:main_clause c
    ) subsumed_clauses; 
    )
    else ());
 *)
  new_clause


(* process without adding to passive *)
    let process_new_clause rs clause =
      dbg D_trace (lazy ("process_new_clause: "^(Clause.to_string clause)));
      if (not (get_is_dead rs clause))
      then
        (
         let sim_clause = simplify_light_new_clause rs clause in     
         (match !current_options.res_to_prop_solver with
         | Res_to_Solver_Passive -> Prop_solver_exchange.add_clause_to_solver sim_clause
         | _ -> ());
         (if (!current_options.qbf_dom_pre_inst) (* TODO clean up *)
         then
           (
            let pre_inst_clauses = Inference_rules.dom_pre_inst SystemDBs.type_to_domain clause in
            dbg D_trace (lazy ("pre_inst: "^(Clause.clause_list_to_string pre_inst_clauses))); 
            
            (* only add pre_inst_clauses to sat solver *)
            List.iter Prop_solver_exchange.add_clause_to_solver pre_inst_clauses;          
           )
         );

         (if (not (clause_in_rs rs sim_clause))
         then
           (rs.res_cl_params <- BCMap.add sim_clause (res_create_cl_param ()) rs.res_cl_params;)
         else ()
         );
         sim_clause
        )
      else
     (
      dbg D_trace (lazy ("process_new_clause: is dead: "^(Clause.to_string clause)));
      (if (* is_res_prepocessing *) rs.res_prep_only 
      then 
        (incr_int_stat 1 res_preprocessed)
      );
      raise Eliminated
     )
 	  
          
(* simplify and add to passive *)
	  
    let add_new_clause_to_passive rs clause =
      try 

        (*    out_str ("Before Prep Clause: "^(Clause.to_string clause)^"\n");*)
        let added_clause = process_new_clause rs clause in

        (*    out_str ("Added Clause: "^(Clause.to_string added_clause)^"\n");*)
        add_to_passive rs added_clause
          
	  (* one might also add to full subsumption index*)

      with
        Eliminated -> ()



(*---------------*)

    let add_conclusion_to_passive rs given_clause clause =
      add_new_clause_to_passive rs clause;
      if (get_is_dead rs given_clause)
      then 
        (* we abort all further
	   inferences with the given clause,
	   later we can also add elimination of all other conclusions
	   with this clause but not this one!,
	   also in general after backward subsumption we can eliminate
	   all children of the subsumed clause provided that we add
	   the clause which subsumes to the clause set *)
	( (*out_str ("\nSubset subs Resol."^(Clause.to_string given_clause)^"\n"); *)

	  raise Given_clause_is_dead)
      else ()


(*--------------------*)
    let get_forward_simp_fun_list rs = 
      let o = !current_options in
      [ 

        if o.res_prop_simpl_given then (Simplify.forward_prop_subsume (* rs.res_sim_state *)) else id_fun;

(* subsumption *)
        (match o.res_forward_subs with 
        |Subs_Full               -> (Simplify.forward_subs rs.res_sim_state) 
        |Subs_By_Length (length) -> failwith "Subs_By_Length: restore support"
        |Subs_Subset             ->  id_fun
        );

(* subs_res *)
        if o.res_forward_subs_resolution then (Simplify.forward_subs_res rs.res_sim_state) else id_fun; 

      ]


    let simplify_forward rs clause =

      dbg D_trace (lazy ("simplify_forward: "^(Clause.to_string clause)));
      let fwd_fun_list = get_forward_simp_fun_list rs in
      let sim_clause = 
        try
          fix_point (fold_left_fun_list fwd_fun_list) clause 
        with 
          Eliminated -> 
            (
             eliminate_clause rs clause;
             raise Eliminated
            )
      in

      if (not (sim_clause == clause))
      then
	(
         dbg D_sim (lazy ("simplify_forward: new_clause: "^(Clause.to_string sim_clause)));  
         eliminate_clause rs clause;
         (
         if (clause_in_rs rs sim_clause)
         then
           (add_to_passive rs sim_clause;)
         else
           (add_new_clause_to_passive rs sim_clause)
         );
(*         let new_clause = process_new_clause rs sim_clause in *)
(*	 res_clause_register_subsumed_by ~by:new_clause clause;	 *)

(* KK *)
(*         sim_clause *)
         raise Eliminated
	)
      else 
        clause

	  
    let add_active_to_exchange clause =
      match !current_options.res_to_prop_solver with
      | Res_to_Solver_Active -> Prop_solver_exchange.add_clause_to_solver clause
      | _ -> ()
	    
            
	    
 	    (*------------------- TODO Orph Elim ---------------------*)
	    (* in order for orphan elimination to be correct: *)
	    (* 1. all simplifying clauses should have res_simplifying set to true *)
	    (* 2. dead clauses should be removed from all indexies and clauseDB *)
	    (* the clause can become dead beacause of the orphan elimination but later *)
	    (* can be derived in a non-redundant way (and needed for completeness) *)
	    (* and therefore should be regenerated *)
	    (*------------------------------------------------------*)
	    
	    (*let dismatching_flag = ref false*)
	    
	    
	    (*----------- Subsumption index based on compressed features ------------------------*)
	    


            (*-----Orphan Elimination---------------*)
            (* we need to try orphan elimination only if *)
            (* at leas one clause is backward susbumed  *)
(* TODO: restructure 2016 *)
(*
  let some_are_backward_subsumed () =
  if
  (get_val_stat res_backward_subset_subsumed) > 0 ||
  (get_val_stat res_backward_subsumed) > 0 ||
  (get_val_stat res_backward_subsumption_resolution) > 0
  then true
  else false
  
  let orphan_elimination clause =
  if !current_options.res_orphan_elimination
  then
  if (some_are_backward_subsumed ())
  then
  (let orphan_list = Clause.get_orphans clause in
  List.iter
  (fun c ->
  if (not (Clause.get_ps_simplifying c)) &&
  (not (Clause.get_is_dead c))
  then
  (eliminate_clause c;
  (*    out_str ("Orph: "^(Clause.to_string c)^"\n");*)
  incr_int_stat 1 res_orphan_elimination)
  else ()
  ) orphan_list;
  if (Clause.get_is_dead clause)
  then raise Eliminated else()
  )
  else ()
  else ()
 *)    


(*-----  backward_subs_res -------*)

    let backward_subs_full rs clause =
      
      let b_subsumed_list = Simplify.backward_subs_full rs.res_sim_state clause in
      List.iter 
        (fun subsumed ->
(*	   res_clause_register_subsumed_by ~by:clause subsumed;	 *)
	  eliminate_clause rs subsumed
	) b_subsumed_list;
      incr_int_stat (List.length b_subsumed_list) res_backward_subsumed
	
    let backward_subs_by_length rs length clause =
      if ((Clause.length clause) <= length)
      then
        backward_subs_full rs clause
      else ()
          
    let simplify_backward rs clause =
      (match !current_options.res_backward_subs with
      | Subs_Full -> backward_subs_full rs clause
      | Subs_By_Length (length) -> backward_subs_by_length rs length clause
      | Subs_Subset -> ()
      )
        
	
(*-----  backward_subs_res -------*)
    let backward_subs_res rs given_clause =
      let subsumed_and_new_clause_list = Simplify.backward_subs_res rs.res_sim_state given_clause in
      let f (subsumed, new_clause) =
	(* (* Clause.assign_backward_subsumption_resolution_history
	      new_clause [clause; subsumed]; *)
	   Clause.assign_tstp_source_backward_subsumption_resolution
	   new_clause [clause; subsumed];
	   Clause.set_bool_param true Clause.res_simplifying new_clause;
	   eliminate_clause subsumed;*)
        dbg D_sim (lazy ("bwd_subs_res: new: "^(Clause.to_string new_clause)));
        dbg D_sim (lazy ("bwd_subs_res subsumed: "^(Clause.clause_list_to_string subsumed)));
        List.iter (eliminate_clause rs) subsumed;   (*TODO: check why eliminate_clause subsumed; was commented before *)
        add_new_clause_to_passive rs new_clause
      in
      List.iter f subsumed_and_new_clause_list

(*  sim_bwd_fun_list *)        
(*  bwd sim functions are f: clause -> unit *)
    let sim_bwd_fun_list rs = 
      let o = !current_options in
      [ 

(* bwd subs *)
        (match o.res_backward_subs with
        | Subs_Full -> backward_subs_full rs
        | Subs_By_Length (length) -> backward_subs_by_length rs length
        | Subs_Subset -> unit_fun
        );

(* backward_subs_res *)    
        if o.res_backward_subs_resolution then (backward_subs_res rs) else unit_fun;
      ]


  let simplify_backward rs clause = 
  let bwd_fun_list = sim_bwd_fun_list rs in
  iter_fun_list bwd_fun_list clause
        

(*------------------------------------------------*)
(* removes clause from the state and context;     *)
(* the clause can be regenerated and added later  *)

    let remove_from_res_state rs clause = 
      dbg D_trace (lazy ("remove_from_res_state: "^(Clause.to_string clause)));
      
      let cl_param = get_cl_param rs clause in  
      (if (res_is_in_active cl_param)
      then
        (eliminate_from_unif_index_cl_param rs clause cl_param;)
      else ()
      );
      
 (*  remove_from_active is cl_param clause; *) (* we assume it is not in active; used in splitting *)
      Simplify.remove_from_indexes_and_context rs.res_sim_state clause;
      rs.res_cl_params <- BCMap.remove clause rs.res_cl_params
          
(* TODO: add remove from passive; needs changes in passive queues for lazy removal based on sets; *)
(* at the moment we assume that this clause is already removed from passive *)

exception Given_Splitted
(*---------------------------*)
let splitting_given rs given_clause = 
  (match !current_options.splitting_mode with (* TODO: add splitting_cvd, splitting_nvd *)
  | Split_Full ->
      begin
        check_empty_clause given_clause;
        let splitted_clauses = Splitting.splitting Definitions.def_env_glb ~out_progress:false [given_clause] in
        match splitted_clauses with 
        |[_] -> 
            (
(*              dbg D_splitting (lazy (" not splitted: "^(Clause.to_string given_clause))); *)
            ) (* no splitting *)
        |_-> 
            
	    ( 
              dbg D_splitting (lazy ("rm: "^(Clause.to_string given_clause)));

	      remove_from_res_state rs given_clause;
	      let f new_clause =
                dbg D_splitting (lazy ("add: "^(Clause.to_string new_clause)));
	        Clause.assign_ps_when_born_concl
	          ~prem1:[given_clause] ~prem2:[] ~c: new_clause;

                add_new_clause_to_passive rs new_clause (* process is called there *)
(*                process_new_clause rs new_clause; *)
	      in
	      List.iter f splitted_clauses;	  
	      raise Given_Splitted
	     )
      end
  | _ -> ()
  )
        
(*---------------------General Simplify---------------------*)
    let all_simplifications rs clause =
(* TODO: orphan_elimination clause; *)
      check_empty_clause clause;
      check_disc_time_limit ();

      Simplify.remove_from_sub_index rs.res_sim_state clause;

      let simplified_clause = 
        try
          simplify_forward rs clause 
        with 
          Eliminated -> 
            (dbg D_sim (lazy ("all_simplifications: Eliminated: "^(Clause.to_string clause)));
             raise Eliminated
            )
      in
      check_empty_clause clause;
      check_disc_time_limit ();
      
      simplify_backward rs simplified_clause;
      check_disc_time_limit ();

(* can raise Given_Splitted *)
      splitting_given rs simplified_clause;

      if (get_is_dead rs simplified_clause)
      then
        (dbg D_sim (lazy ("all_simplifications: is_dead: "^(Clause.to_string clause)));
         raise Eliminated
        )
      else
        (
         Simplify.add_to_sub_index rs.res_sim_state simplified_clause;
         simplified_clause
        ) 
          

          (*---------------------General Simplify---------------------*)
(*  
    let all_simplifications clause =
    orphan_elimination clause;
    (* feature_list is quite expensive therefore need to pass it as param*)
    let feature_list = get_feature_list clause in
    (*  out_str ("simpl: "^(Clause.to_string clause)^"\n");*)
    let simplified_clause = simplify_forward feature_list clause in
    check_empty_clause clause;
    check_disc_time_limit ();
    let new_feature_list =
    if (simplified_clause == clause) then
    feature_list
    else
    get_feature_list simplified_clause
    in
    simplify_backward new_feature_list simplified_clause;
    check_disc_time_limit ();
    if (Clause.get_is_dead simplified_clause)
    then
    raise Eliminated
    else
    (new_feature_list, simplified_clause)
 *)
          
          (*----------------------all factorings-----------------------*)
    let rec all_factorings' rs main_clause sel_lit rest_sel_lits =
      match rest_sel_lits with
      | l:: tl ->
          (try
	    let conclusion =
	      Inference_rules.factoring main_clause sel_lit l in
	    add_conclusion_to_passive rs main_clause conclusion;
	    (* out_str_debug ("\n Factoring: "^(Clause.to_string main_clause)
	       ^" conclusion: "^(Clause.to_string conclusion));*)
	    all_factorings' rs main_clause sel_lit tl
          with Unif.Unification_failed -> ()
          | Unif.Unif_type_check_failed -> 
              (
               out_warning ("resolution_loop: all_factorings': Unif_type_check_failed main_clause:"
                            ^(Clause.to_string main_clause)^"\n\n");
               out_warning ("Proof:\n\n");
               (Format.printf "%a@." TstpProof.pp_tstp_proof_resolution main_clause);
	       
               raise Unif.Unif_type_check_failed
              )
          )
      |[] -> ()
	    
    let rec all_factorings_lits rs main_clause selected_literals =
      match selected_literals with
      | l:: tl ->
          all_factorings' rs main_clause l tl;
          all_factorings_lits rs main_clause tl
      |[] -> ()
	    
    let all_factorings rs main_clause =
      let selected_literals = get_selected_lits (get_cl_param rs main_clause) in
      all_factorings_lits rs main_clause selected_literals

        (*-------------------------all resolutions-----------------------*)
        
        (* eliminates dead clauses from the clause_list and returns the rest*)
    let rec remove_if_dead_from_active rs clause_list =
      match clause_list with
      | c::tl ->
          if (get_is_dead rs c)
          then (
            incr_int_stat 1 res_backward_subsumption_resolution;
            eliminate_clause rs c;
            (*	 out_str ("Backward Subsumed: "^(Clause.to_string c)^"\n");*)
            remove_if_dead_from_active rs tl
           )
          else
            c::(remove_if_dead_from_active rs tl)
      | [] -> []

            (* eliminates dead clauses from the clause_list if ordered by flag *)
    let remove_deads_from_active rs clause_list =
      if !current_options.res_backward_subs_resolution
      then
        let _ = remove_if_dead_from_active rs clause_list in ()

    let all_resolutions rs main_clause selected_literals =
      (* out_str ("res: main"^(Clause.to_string main_clause)^"\n"); *)
      try
        (let for_all_sel_lit sel_lit =
          let unif_candidates = get_compl_unif_candidates rs sel_lit in
          let for_all_candidates (lit, clause_list) =
	    (try
	      (*		out_str ("res_try: "^(Clause.to_string main_clause)
	        ^(Clause.clause_list_to_string clause_list));
               *)
	      let new_clause_list = remove_if_dead_from_active rs clause_list in
	      let conclusion_list = Inference_rules.resolution main_clause sel_lit new_clause_list lit in
	      
	      (*
	        let conclusion_list =
	        Inference_rules.resolution_dismatch (!dismatching_flag)
	        (!forward_subs_resolution_flag) (!backward_subs_resolution_flag)
	        main_clause sel_lit compl_sel_lit new_clause_list lit term_db_ref in
	       *)
	      (*	
	        out_str
	        ("resolution: "^(Clause.to_string main_clause)
	        ^"["^(Clause.clause_list_to_string new_clause_list)^"]"
	        ^"conclusion: "
	        ^"["^(Clause.clause_list_to_string conclusion_list)^"]");
	       *)
              (* TODO: check with KK that this is necessary *)
	      remove_deads_from_active rs new_clause_list;
	      List.iter (add_conclusion_to_passive rs main_clause) conclusion_list
	    with Unif.Unification_failed -> ()
	    ) in
          List.iter for_all_candidates unif_candidates in
        List.iter for_all_sel_lit selected_literals
        )
      with
        Inference_rules.Main_subsumed_by (by_conclusion) ->
          (
           incr_int_stat 1 res_forward_subsumption_resolution;
           add_conclusion_to_passive rs main_clause by_conclusion)
	    
	    (* add to unif index *)
	    
            (* add_to_subsumption_index *)
            (*add later !!!*)
            
            (*-------------------- resolution loop-------------------------*)
            
    let rec resolution_loop_body rs =
      incr_int_stat 1 res_num_of_loops;
      try
        let clause = remove_from_passive rs in
        dbg D_given (lazy ("removed from passive"^(Clause.to_string clause)^"\n"));
        (*   out_str ("removed from passive"^(Clause.to_string clause)^"\n");*)
(*    if ((Clause.get_is_dead clause) ||
      (Clause.get_ps_in_active clause))
 *)
        if ((get_is_dead rs clause) 
          ||(not (clause_in_rs rs clause)) (* clause might be removed from rs state due e.g., splitting but not declared dead *) 
          ||(res_is_in_active (get_cl_param rs clause)))
        then () (* (out_str ("is dead or in active"^(Clause.to_string clause)^"\n");) *)
        else
          (try
	    let given_clause = all_simplifications rs clause in
            let given_cl_param = get_cl_param rs given_clause in 
	    (* Clause.set_bool_param false Clause.in_passive given_clause; *)
(*	    let selected_literals = res_get_sel_lits given_cl_param in *)
	    let selected_literals = res_lit_sel rs.res_unif_index given_cl_param given_clause in 
	    dbg D_given (lazy (
		         ("given_clause: "^(Clause.to_string given_clause)
		          ^" selected lit: "
		          ^(Term.term_list_to_string selected_literals)
		          ^(" Born: "^( string_of_int (Clause.get_ps_when_born given_clause))^"\n")
		         )));
	    
	    (*debug*)
	    (* (if (Clause.length given_clause) <=1 then
	       out_str_debug ("given unit clause: "
	       ^(Clause.to_string given_clause)^"\n"));*)
	    all_factorings rs given_clause;
	    all_resolutions rs given_clause selected_literals;
	    add_to_active rs given_clause given_cl_param selected_literals;

	    (* alternatively one can add all newly generated to subsumption also  *)
(*	add_to_subsumption_index given_clause; *)
	    add_active_to_exchange given_clause;
	    (* out_str
	       ("\n In Active: "^(Clause.to_string given_clause)) *)
	    (* else () *)
          with
          | Eliminated -> ()
          | Given_clause_is_dead -> ()
          | Given_Splitted -> ()
	        (*out_str_debug "\n Given_clause_is_dead \n"*)
          )
      with
        PassiveQueues.Passive_Empty ->
          ((* out_str ("Satisfiable context 2 \n\n");
	      context_iter !context (fun c -> out_str ((Clause.to_string c)^"\n"));
	    *) 
	    raise (Res_satisfiable(res_get_model rs))
)
  (*-------------------- Adaptive selection ---------------------*)
  
    let resolution_change_sel rs main_clause main_cl_param =
      dbg D_res_change_sel (lazy "start");
      let success = ref false in
      try
        (
         while (not !success) do
           let current_select_lits = res_get_sel_lits main_cl_param in

           dbg D_res_change_sel (lazy (("main clause: "^(Clause.to_string main_clause)
	                                ^" selected lit: "
	                                ^(Term.term_list_to_string current_select_lits))) );

           if (not (res_get_sel_final main_cl_param))
           then
	     (* then only one lit is sel and it is neg*)
	     let sel_lit =
	       (match current_select_lits with
	       | h::[] -> h
	       | _ -> failwith "resolution_change_sel: more than one lit sel \n ")
	     in
             let unif_candidates = get_compl_unif_candidates rs sel_lit in
	     (* subsumption resolution is proper now *)
	     (*---*) 
(*
  if ((not !current_options.res_forward_subs_resolution)
  && (not !current_options.res_backward_subs_resolution))
  then
 *)
	     (*---*)
	     (if ( unif_candidates = [])
	     then
	       (success:= true)
	     else
	       (let _ = Resolution_sel.res_change_sel rs.res_unif_index main_cl_param main_clause in ();
	       incr_int_stat 1 res_num_sel_changes
               )
	     )
	       (*---*) 
(*
  else
  (* subsumption resolution part! *)
  let for_all_candidates rest (lit, clause_list) =
  (try
  let clause_list_before = remove_if_dead_from_active clause_list in
  let subsuming_list =
  Inference_rules.subs_resolution
  main_clause sel_lit clause_list_before lit 
  in
  List.iter (add_conclusion_to_passive main_clause) subsuming_list;
  let clause_list_after =
  if !current_options.res_backward_subs_resolution
  then
  remove_if_dead_from_active clause_list_before
  else
  clause_list_before
  in
  clause_list_after@rest
  with
  Unif.Unification_failed -> rest
  )
  in
  
  let all_clause_list =
  List.fold_left for_all_candidates [] unif_candidates in
  if (all_clause_list = [])
  then
  (success:= true)
  else
  (let _ = Selection.change_sel main_clause in ();
  incr_int_stat 1 res_num_sel_changes)
  (*----- *)
 *)
           else
	     ( (* selection is final: maximal, can be several lits*)
	       success:= true;
	       let for_all_sel_lit sel_lit =
                 let unif_candidates = get_compl_unif_candidates rs sel_lit in
	         let for_all_candidates (lit, clause_list) =
	           let prune_clause_list rest clause =
                     let cl_param = get_cl_param rs clause in
		     if (not (res_get_sel_final cl_param))
		     then
		       (
                        dbg D_res_change_sel 
                          (lazy 
                             (("removed from active: "^(Clause.to_string clause)
	                       ^" selected lit: "
	                       ^(Term.term_list_to_string current_select_lits))) 
                          );

		        eliminate_from_unif_index rs clause;

		        incr_int_stat 1 res_moves_from_active_to_pass;
		        let _ = Resolution_sel.res_change_sel rs.res_unif_index cl_param clause in ();
		        incr_int_stat 1 res_num_sel_changes;
		        
		        (* out_str_debug ("New sel: "
		           ^(Term.term_list_to_string
		           (Clause.get_res_sel_lits clause))^"\n"); *)
		        add_to_passive rs clause;
		        rest)
		     else
		       clause:: rest
	           in
	           let side_clause_list =
		     List.fold_left prune_clause_list [] clause_list
	           in
	           (try
		     let conclusion_list =
		       Inference_rules.resolution
		         main_clause sel_lit side_clause_list lit 
		     in
                     remove_deads_from_active rs side_clause_list;                     
                     dbg D_res_change_sel 
                       (lazy 
                          ("resolution: side: "^(Clause.clause_list_to_string side_clause_list)
                             )	                      
                       );
                     dbg D_res_change_sel 
                       (lazy 
                             ("conclusion: "^(Clause.clause_list_to_string conclusion_list)
                             )	                      
                       );
		     (*debug*)
		     (* let f cl =
		        if (Clause.is_ground cl)
		        then
		        out_str ((Clause.to_string cl)^"\n")
		        else ()
		        in
		        List.iter f conclusion_list;
		      *)
		     (*debug end*)
		     List.iter (add_conclusion_to_passive rs main_clause) conclusion_list
	           with Unif.Unification_failed -> ()
	           )
	         in
	         List.iter for_all_candidates unif_candidates in
	       List.iter for_all_sel_lit current_select_lits
	      )
         done
        )
      with
        Inference_rules.Main_subsumed_by (by_conclusion) ->
          (
           incr_int_stat 1 res_forward_subsumption_resolution;
           add_conclusion_to_passive rs main_clause by_conclusion)
	    
	    (*-----------------------Adaptive Selection Loop Body----------------------*)
	    
    let rec resolution_change_sel_loop_body rs =
      assert rs.res_is_usable;
      incr_int_stat 1 res_num_of_loops;
      try
        let clause = remove_from_passive rs in
        dbg D_given ( lazy ("removed from passive: "^(Clause.to_string clause)^"\n"));

        if ((get_is_dead rs clause) ||
        (res_is_in_active (get_cl_param rs clause)))
        then ()  (* (out_str ("is dead or in active"^(Clause.to_string clause)^"\n");) *)
        else
          (
           let given_clause = all_simplifications rs clause in
           let given_cl_param = get_cl_param rs given_clause in 

           dbg D_given ( lazy ("given: "^(Clause.to_string given_clause)^"\n"));

           (*
	     (if (not (res_sel_is_def clause))
	     then (* clause is "new" *)
	     (
	     let (feature_list, given_clause) = all_simplifications clause in
	     let _ = Selection.change_sel given_clause in
	     (* alternatively one can add all newly generated to subsumption also  *)
	     add_to_subsumption_index feature_list given_clause;
	     (* exchange with instantiation*)
	     add_active_to_exchange given_clause;
	     given_clause
	     )
	     else clause)
             in
            *)
	   (if (not (res_sel_is_def given_cl_param))
	   then (* clause is "new" *)
           (
            let _ = Resolution_sel.res_change_sel rs.res_unif_index given_cl_param given_clause in 
	    add_active_to_exchange given_clause;
           )
           );
	    (*	out_str ("Clause for inf: "^(Clause.to_string clause_for_inferences)^"\n"); *)
(*	    let _ = Resolution_sel.change_sel given_cl_param given_clause in *)

	   resolution_change_sel rs given_clause given_cl_param;

           ( 
	    if (res_get_sel_final given_cl_param)
	    then (* we need factoring only with max selected *)
	      all_factorings rs given_clause
	    else()
            );
           let selected_lits = res_get_sel_lits given_cl_param  in

           dbg D_given ( lazy ("sel_lits: "^(Term.term_list_to_string selected_lits)^"\n"));

           add_to_active rs given_clause given_cl_param selected_lits;

           
           (*	out_str ("given_clause: "^(Clause.to_string clause_for_inferences)
	     ^" selected lit: "
	     ^(Term.term_list_to_string selected_lits));
	    *)
          )
	    
	    (* out_str_debug
	       ("\n In Active: "^(Clause.to_string given_clause)) *)
	    (* else () *)
	    
      with
        
      | Eliminated -> 
          (
           dbg D_given ( lazy ("Given Eliminated"));
          )
      | Given_clause_is_dead ->           
          (
           dbg D_given ( lazy ("Given_clause_is_dead"));
          )
	    (* out_str "\n Given_clause_is_dead \n" *)
      | Given_Splitted -> 
          (
           dbg D_splitting ( lazy ("Given_Splitted"));
          )

      | PassiveQueues.Passive_Empty ->
          (
           (* out_str ("Satisfiable context\n\n");
	      context_iter !context (fun c -> out_str ((Clause.to_string c)^"\n")); 
	    *)
           raise (Res_satisfiable (res_get_model rs))
          )
	    
	    (* replaced by resolution_loop_exchange
	       let resolution_loop () =
	       while true do
	       (match !current_options.res_sel_fun with
	       | Res_Adaptive ->
	       resolution_change_sel_loop_body ()
	       | _ ->
	       resolution_loop_body ()
	       )
	       done
	     *)
	    
	    (*let init_resolution input_clauses = *)
	    
	    (* Old
	       
	       (* for combination with e.g. instantiation *)
	       (* if we add eq. axioms than we need to use this*)
	       let init_resolution_input_clauses input_clauses =
	       (* need to copy clauses if combine with instantiation *)
	       let renew_clauses_in_init clause =
	       let new_clause = Clause.create (Clause.get_literals clause) in
	       (Clause.inherit_param_modif clause new_clause;
	       Clause.inherit_bool_param Clause.in_prop_solver clause new_clause;
	       Clause.inherit_history clause new_clause;
	       new_clause)
	       in
	       let new_input = (List.map renew_clauses_in_init input_clauses) in
	       let add_clause clause =
	       add_new_clause_to_passive clause
	       in
	       List.iter add_clause new_input
	       (*debug*)
	       (* let tmp_cl = Clause.create ([Parsed_input_to_db.bot_term]) in
	          add_clause tmp_cl;
	          let f cl = out_str "\nbot term is finalised!\n" in
	          Gc.finalise f tmp_cl *)
	     *)
	    
	    
	    (*-------------------Preprocessing only--------------------------*)
	    
    let rec res_preprocess rs =
      try
        while true
        do
          begin
	    incr_int_stat 1 res_num_of_loops;
	    try
	      let clause_from_pass = remove_from_passive rs in
	      (*	out_str ("Discount: removed from passive: "^(Clause.to_string clause)^"\n"); *)

	      let clause = simplify_light_new_clause rs clause_from_pass in
	      if (get_is_dead rs clause)
	      then (incr_int_stat 1 res_preprocessed;)  (* (out_str ("is dead or in active"^(Clause.to_string clause)^"\n");) *)
	      else
	        (
	         let _given_clause =
	           (
		    let given_clause = all_simplifications rs clause in
(*		add_to_subsumption_index feature_list given_clause; *)
		    (* prop solver exchange with instantiation *)
		    add_active_to_exchange given_clause;
		    given_clause
	           )
		     
	         in
	         (
	          (*	out_str ("Clause for inf: "^(Clause.to_string clause_for_inferences)^"\n"); *)
	          (*	
		    let selected_lits =
		    (try (Clause.get_res_sel_lits clause_for_inferences)
		    with Clause.Res_sel_lits_undef ->
		    failwith
		    "resolution_change_sel_loop_body: sel lit should be def. here \n ")
		    in
		    add_to_active clause_for_inferences selected_lits;
		    Clause.set_ps_in_active true clause_for_inferences;
	           *)

	          (*add_list_ref prep_input given_clause; *)
	          (*	out_str ("given_clause: "^(Clause.to_string clause_for_inferences)
		    ^" selected lit: "
		    ^(Term.term_list_to_string selected_lits));			
	           *)
	         )
	        )
	          (* out_str_debug
		     ("\n In Active: "^(Clause.to_string given_clause)) *)
	          (* else () *)
	          
	    with
	      
	    | Eliminated -> (incr_int_stat 1 res_preprocessed)
	    | Given_clause_is_dead -> (incr_int_stat 1 res_preprocessed)
	          (* out_str "\n Given_clause_is_dead \n" *)
          end
        done;
        failwith "res_preprocess: should not happen" 
      with 	
      | PassiveQueues.Passive_Empty ->
          (
           Clause.context_to_list ~non_dead:true (Simplify.sim_get_context rs.res_sim_state)
(*
  context_fold 
  !context 
  (fun c rest ->
  if (not (Clause.get_is_dead c)) 
  then 
  ((Clause.copy_clause c)::rest)
  else
  (
  incr_int_stat 1 res_preprocessed;
  rest			
  )	
  )
  []
 *)
          )
	    
	    
	    (*		 (* out_str ("Satisfiable context\n\n");
			    context_iter !context (fun c -> out_str ((Clause.to_string c)^"\n")); 
			  *)
	      Prep_finished !prep_context)
    	      )
	     *)

(*    let add_clause rs clause = add_new_clause_to_passive rs clause  *)
	
    let res_add_clause rs clause = 
(*
  let copied_clause = Clause.copy_clause clause in
  let new_clause = context_add !context copied_clause in
  
  (* when_born is 0 *)
  (*	Clause.clear_proof_search_param new_clause; *)
  (* replace with replacing dead with implied *)
  Clause.assign_is_dead false new_clause;
  Clause.assign_ps_when_born 0 new_clause;
  (*	out_str ("\n Discount Added: \n"^(Clause.to_string new_clause)^"\n"); *)
  ignore (context_add (!input_clauses_context) new_clause);
 *)
      dbg D_input (lazy ("res_add_clause: "^(Clause.to_string clause)));
      rs.res_input_clauses <- BCSet.add clause rs.res_input_clauses;
      add_new_clause_to_passive rs clause 
(*      add_clause rs clause *)


    let res_add_clause_list rs clause_list = List.iter (res_add_clause rs) clause_list

(*
  rs.res_input_clauses <- BCSet.add clause rs.res_input_clauses;
  add_input_clause rs clause
 *)


(*
    let create_res_state_clause_list ~res_prep_only clause_list =  
      let rs = create_res_state ~res_prep_only in
      List.iter (add_input_clause rs) clause_list 

    let create_res_state_context ~res_prep_only context = 
      let rs = create_res_state ~res_prep_only in
      context_iter context ~non_dead:true (add_input_clause rs)
  *)      

(*--------------------------------*)
(* replaced by create_res_state_clause_list/create_res_state_context *)
(*
  let init_resolution () =
  (*	out_str "\n init_resolution\n"; *)
  dbg_env D_input 
  (fun () -> 
  out_str ("Input clauses: \n "^(Clause.clause_list_to_string !input_clauses));
  );
  List.iter add_input_clause !input_clauses
  let _ = init_resolution ()
 *)

(*--------------------------------*)    

        
        (* for combination with e.g. instantiation, runs disount loop once *)
        (* and returns new clauses in exchanege  *)
        (* can raise Satisfiable, Unsatisfiable *)

    let resolution_loop_exchange rs =
      check_disc_time_limit ();
      (match !current_options.res_lit_sel with
      | Res_adaptive | Res_adaptive_neg | Res_adaptive_max  ->
          resolution_change_sel_loop_body rs;
      | Res_KBO_max | Res_neg_sel_max | Res_neg_sel_min | Res_pos_sel_max | Res_pos_sel_min | Res_neg_sel_nrc ->
          resolution_loop_body rs
      );

      
      (*------------*)
      (*
        let start_resolution input_clauses =
        init_resolution_input_clauses input_clauses;
        (* ClauseAssignDB.iter add_caluse !init_clause_db_ref; *)
        (* out_str_debug "initial clauses are added to passive \n";*)
        resolution_loop_exchange ()
        
       *)
      
      (* unassigns all structures related to resolution and runs GC.full_major*)

(* TODO: use rs_ref 
   let clear_all () =
   
   is_usable := false;

   (* a trick to keep old value of functional statistics*)
   (* like number of clauses and number in passive*)
   
   let num_in_passive = (get_val_stat_fun res_num_in_passive) in
   assign_fun_stat
   (fun () -> num_in_passive)
   res_num_in_passive;
   
   let num_of_clauses = (get_val_stat_fun res_num_of_clauses) in
   assign_fun_stat
   (fun () -> num_of_clauses)
   res_num_of_clauses;
   
   finalise_passive ();
   ss_index_ref := (SubsetSubsume.create ());
   subsumption_index_ref := (SubsumptionIndexM.create ());
   ClauseUnifIndex.clear !unif_index_ref;
   
   (* context_iter !context Clause.clear_clause; *) 
   res_context_reset ();
   

   input_clauses_context:= context_create 1;
   (* context_iter !simplified_input Clause.clear_clause; *)
   simplified_input := context_create 2;
   
 *)
      (* Memory is cleared separately by Lib.clear_mem ()*)
      
      (*-----------------End--------------------------*)
(* end *)



      
      (*--------------------Old without subs resol.-----------------------------*)
      (*
        let resolution_change_sel main_clause =
        let success = ref false in
        try
        (
        while (not !success) do
        let current_select_lits =
        (try (Clause.get_res_sel_lits main_clause)
        with Clause.Res_sel_lits_undef ->
        failwith "resolution_change_sel: sel lit should be def. here \n ")
        in
        (* out_str_debug ("Main Clause: "^(Clause.to_string main_clause)
           ^"Selected lit: "
           ^(Term.term_list_to_string current_select_lits)^"\n"); *)
        if (not (Clause.get_bool_param Clause.res_sel_max main_clause))
        then
        (* then only one lit is sel and it is neg*)
        let sel_lit =
        (match current_select_lits with
        | h::[] -> h
        | _ -> failwith "resolution_change_sel: more than one lit sel \n ")
        in
        let compl_sel_lit = add_compl_lit sel_lit in
        let unif_candidates =
        DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
        if (unif_candidates = [])
        then
        (success:= true)
        else
        (let _ = Selection.change_sel main_clause in ();
        res_num_change_sel:=!res_num_change_sel +1)
        else
        ( (* selection is final: maximal, can be several lits*)
        success:= true;
        let for_all_sel_lit sel_lit =
        let compl_sel_lit = add_compl_lit sel_lit in
        let unif_candidates =
        DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
        let for_all_candidates (lit, clause_list) =
        let prune_clause_list rest clause =
        if (not (Clause.get_bool_param Clause.res_sel_max clause))
        then
        (
        (* out_str_debug ("Removed from Active: "
           ^(Clause.to_string clause)
           ^"Selected lit: "
           ^(Term.term_list_to_string
           (Clause.get_res_sel_lits clause) )^"\n"); *)
        eliminate_from_unif_index clause;
        Clause.set_bool_param false Clause.in_active clause;
        incr_int_stat (-1) res_num_in_active;
        res_num_moves_active:=!res_num_moves_active +1;
        let _ = Selection.change_sel clause in ();
        res_num_change_sel:=!res_num_change_sel +1;
        (* out_str_debug ("New sel: "
           ^(Term.term_list_to_string
           (Clause.get_res_sel_lits clause))^"\n"); *)
        add_to_passive clause;
        rest)
        else
        clause:: rest
        in
        let side_clause_list =
        List.fold_left prune_clause_list [] clause_list
        in
        (try
        let conclusion_list =
        Inference_rules.resolution
        !forward_subs_resolution_flag !backward_subs_resolution_flag
        main_clause sel_lit compl_sel_lit side_clause_list lit term_db_ref
        in
        remove_deads_from_active side_clause_list;
        List.iter (add_conclusion_to_passive main_clause) conclusion_list
        with Unif.Unification_failed -> ()
        ) in
        List.iter for_all_candidates unif_candidates in
        List.iter for_all_sel_lit current_select_lits
        )
        
        done
        )
        with
        Inference_rules.Main_subsumed_by (by_conclusion) ->
        (num_forward_subs_resolution := !num_forward_subs_resolution +1;
        add_conclusion_to_passive main_clause by_conclusion)
        
       *)
      
      (*--------------Commented---------------------------------*)
      (*
        (*-------------New with subs. resol.------------------------------*)
        let resolution_change_sel main_clause =
        let success = ref false in
        try
        (
        while (not !success) do
        let current_select_lits =
        (try (Clause.get_res_sel_lits main_clause)
        with Clause.Res_sel_lits_undef ->
        failwith "resolution_change_sel: sel lit should be def. here \n ")
        in
        (* out_str_debug ("Main Clause: "^(Clause.to_string main_clause)
           ^"Selected lit: "
           ^(Term.term_list_to_string current_select_lits)^"\n"); *)
        if (not (Clause.get_bool_param Clause.res_sel_max main_clause))
        then
        (* then only one lit is sel and it is neg*)
        let sel_lit =
        (match current_select_lits with
        | h::[] -> h
        | _ -> failwith "resolution_change_sel: more than one lit sel \n ")
        in
        let compl_sel_lit = add_compl_lit sel_lit in
        let unif_candidates =
        DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
        (* subsumption resolution is proper now *)
        (*--*) if ((not !current_options.res_forward_subs_resolution)
        && (not !current_options.res_backward_subs_resolution))
        then
        (*---*)
        (if ( unif_candidates = [])
        then
        (success:= true)
        else
        (let _ = Selection.change_sel main_clause in ();
        incr_int_stat 1 res_num_sel_changes)
        )
        (*---*) else
        (* subsumption resolution part! *)
        let for_all_candidates rest (lit, clause_list) =
        (try
        let clause_list_before = remove_if_dead_from_active clause_list in
        let subsuming_list =
        Inference_rules.subs_resolution
        main_clause sel_lit compl_sel_lit clause_list_before lit term_db_ref
        in
        List.iter (add_conclusion_to_passive main_clause) subsuming_list;
        let clause_list_after =
        if !current_options.res_backward_subs_resolution
        then
        remove_if_dead_from_active clause_list_before
        else
        clause_list_before
        in
        clause_list_after@rest
        with
        Unif.Unification_failed -> rest
        )
        in
        
        let all_clause_list =
        List.fold_left for_all_candidates [] unif_candidates in
        if (all_clause_list = [])
        then
        (success:= true)
        else
        (let _ = Selection.change_sel main_clause in ();
        incr_int_stat 1 res_num_sel_changes)
        (*----- *)
        else
        ( (* selection is final: maximal, can be several lits*)
        success:= true;
        let for_all_sel_lit sel_lit =
        let compl_sel_lit = add_compl_lit sel_lit in
        let unif_candidates =
        DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
        let for_all_candidates (lit, clause_list) =
        let prune_clause_list rest clause =
        if (not (Clause.get_bool_param Clause.res_sel_max clause))
        then
        (
        (* out_str ("Removed from Active: "
           ^(Clause.to_string clause)
           ^"Selected lit: "
           ^(Term.term_list_to_string
           (Clause.get_res_sel_lits clause) )^"\n"); *)
        eliminate_from_unif_index clause;
        Clause.set_bool_param false Clause.in_active clause;
        incr_int_stat (-1) res_num_in_active;
        incr_int_stat 1 res_moves_from_active_to_pass;
        let _ = Selection.change_sel clause in ();
        incr_int_stat 1 res_num_sel_changes;
        
        (* out_str_debug ("New sel: "
           ^(Term.term_list_to_string
           (Clause.get_res_sel_lits clause))^"\n"); *)
        add_to_passive clause;
        rest)
        else
        clause:: rest
        in
        let side_clause_list =
        List.fold_left prune_clause_list [] clause_list
        in
        (try
        let conclusion_list =
        Inference_rules.resolution
        main_clause sel_lit compl_sel_lit side_clause_list lit term_db_ref
        in
        (
        remove_deads_from_active side_clause_list;
        (*debug*)
        (* let f cl =
           if (Clause.is_ground cl)
           then
           out_str ((Clause.to_string cl)^"\n")
           else ()
           in
           List.iter f conclusion_list;
         *)
        (*debug end*)
        List.iter (add_conclusion_to_passive main_clause) conclusion_list
        )
        with Unif.Unification_failed -> ()
        )
        in
        List.iter for_all_candidates unif_candidates in
        List.iter for_all_sel_lit current_select_lits
        )
        done
        )
        with
        Inference_rules.Main_subsumed_by (by_conclusion) ->
        (
        incr_int_stat 1 res_forward_subsumption_resolution;
        add_conclusion_to_passive main_clause by_conclusion)
        
       *)
  
  (*--------------end Commented---------------------------------*)
  
(* -------------------Commented--------------*)
(*
(* various debug tests*)

(*matching test*)
  let iter_all_pairs_of_trems f =
  let g term =
  TermDB.iter (f term) !term_db_ref in
  TermDB.iter g !term_db_ref

  let try_matching t1 t2 =
  try
  let subst = Unif.matches t1 t2 in
  out_str_debug
  ((Term.to_string t1)
  ^"Matches "
  ^(Term.to_string t2)^"\n"
  ^"  with subst: "^(Subst.to_string subst)^"\n" )
  with
  Unif.Matching_failed ->
  out_str_debug
  ((Term.to_string t1)
  ^" NOT Matches "
  ^(Term.to_string t2)^"\n")

  let try_matching_all () =
  iter_all_pairs_of_trems try_matching;
  out_str_debug "Matching finished \n"

(**subsumption test*)
  let iter_all_pairs_of_clauses f =
  let f' cl =
  ClauseAssignDB.iter (f cl) !clause_db_ref in
  ClauseAssignDB.iter f' !clause_db_ref

  let try_subsumption c1 c2 =
  try
  let subst = Unif.subsumes c1 c2 in
  out_str_debug
  ((Clause.to_string c1)
  ^"Subsumes "
  ^(Clause.to_string c2)^"\n"
  ^"  with subst: "^(Subst.to_string subst)^"\n" )
  with
  Unif.Subsumtion_failed ->
  out_str_debug
  ((Clause.to_string c1)
  ^" NOT Subsumes "
  ^(Clause.to_string c2)^"\n")

  let try_subsumption_all () =
  out_str_debug "start adding init cl to passive\n";
  let num_of_symb = SymbolDB.size !symbol_db_ref in
  let add_clause clause =
  out_str_debug ("Adding init cl to passive: "^(Clause.to_string clause)^"\n");
  add_new_clause_to_passive clause;
  SubsumptionIndexM.add_clause
  (get_feature_list clause) clause subsumption_index_ref
  in
  List.iter add_clause !init_clause_list_ref;
  out_str_debug "initial clauses are added to passive and subsumtion index\n";
  ClauseAssignDB.iter
  (fun c -> out_str_debug ("Clause in db: "^(Clause.to_string c)^"\n"))
  !clause_db_ref ;
  iter_all_pairs_of_clauses try_subsumption
(* uncomment for index subsumption
   let try_forward_subs clause =
   ( match
   (SubsumptionIndexM.is_subsumed
   (get_feature_list clause) clause subsumption_index_ref)
   with
   | Some((subsumer, subst)) ->
   out_str_debug
   ("Clause"^(Clause.to_string clause)^" is subsumed by "
   ^(Clause.to_string subsumer)^"\n")
   | None ->
   out_str_debug
   ("Clause"^(Clause.to_string clause)^" can not be subsumed \n")
   ) in
   ClauseAssignDB.iter try_forward_subs !clause_db_ref
 *)

 *)    (* End Comment for tests*)
