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
open Instantiation_env
open Instantiation_sel 

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_input
  | D_inst
  | D_active
  | D_active_to_passive
  | D_create_pq
  | D_finalise_pq
  | D_given
  | D_given_param
  | D_given_filtered
  | D_solve 
  | D_mem
  | D_sim
  | D_sel
  | D_splitting
  | D_soft
  | D_prop_impl_unit
  | D_dom_inst

(*  | D_unif_ind *)
      
let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_input -> "input"
  | D_inst -> "inst"
  | D_active -> "active"
  | D_active_to_passive -> "active_to_passive"
  | D_create_pq -> "create_passive_queue"
  | D_finalise_pq -> "finalise_passive_queue"
  | D_given -> "given"
  | D_given_param -> "given_param"
  | D_given_filtered -> "given_filtered"
  | D_solve -> "solve"
  | D_mem -> "mem"
  | D_sim -> "sim"
  | D_sel -> "sel"
  | D_splitting -> "splitting"
  | D_soft -> "soft"
  | D_prop_impl_unit -> "prop_impl_unit"
  | D_dom_inst -> "dom_inst"

(*  | D_unif_ind -> "unif_ind" *)

let dbg_groups =
  [
  D_trace; 
(*   D_input; *)
   (* D_inst;   *)
(*   D_create_pq; *)
(*   D_finalise_pq; *)   
    (* D_sim;   *)
    (* D_given;   *)
   (* D_given_param;  *)
   (* D_active;   *)
   (* D_active_to_passive;    *)
   (* D_given_filtered;  *)
   (* D_solve;  *)

(*   D_sel; *)
(*   D_splitting; *)
(*   D_mem; *) 
(*   D_soft; *)
(*   D_prop_impl_unit *)
   (* D_dom_inst; *)
 ]
    
let module_name = "instantiation_loop"
    
    
(*----- debug fixed part --------*)
    
let () = dbg_flag_msg dbg_flag module_name
    
let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy
    
let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)

type prop_lit = PropSolver.lit

type gr_atom_activity = 
    { 
      mutable ga_pos : int;
      mutable ga_neg : int;

    (* we try to change the lit value if *)
    (* activity diff is greater than change_acitivity_limit *)
      mutable change_activity_limit : int;
   }

type inst_state = 
    {
     (* TODO add res_options; separate from current options ? *)
     mutable inst_sim_state     : sim_state; (* all clauses are added first to sim  *)
     mutable inst_input_clauses : BCSet.t;   (* non-dead clauses are copied to res_context *)

     mutable inst_cl_params     : inst_cp BCMap.t;
     mutable inst_unif_index     : ClauseUnifIndex.t;
     mutable inst_passive_queue  : PassiveQueues.passive_queue;
     mutable inst_unprocessed    : clause list;
     mutable ga_activity         : gr_atom_activity TMap.t;
     mutable soft_assumptions    : TSet.t;
     mutable solver_num_cl_limit : int;
     mutable solver_counter      : int;
   }

exception Inst_satisfiable of inst_pre_model

let subsumtion_is_on () = !current_options.inst_subs_given || !current_options.inst_subs_new

let inst_create_state () = 
  Prop_solver_exchange.clear_soft_assumptions (); (* TODO: move this *)

  (* sim_state *) (* TODO: adjust to input/res_options *)
  let sim_options = 
    {
     sim_add_to_prop_solver = true;  (* TODO adjust *)
     sim_use_ss_index = true;
     sim_use_sub_index = subsumtion_is_on (); 
     sim_add_to_sub_index_test =  (fun c -> true); (* fun c -> (Clause.length c) <= 4;*) 
   }
  in
  let inst_sim_state = sim_create sim_options in

(* passive queue *)
  let passive_queue_type = !current_options.inst_passive_queue_type in
  let priorities = !current_options.inst_passive_queues in
  let mults = !current_options.inst_passive_queues_freq in
  dbg D_create_pq (lazy ("priorities:"^(pass_queues_type_to_str priorities)
                         ^", freqs:"^(passive_queue_freqs_to_str mults)));
  let inst_passive_queue = PassiveQueues.create_passive_queue passive_queue_type priorities mults in

(* stats *)
  assign_fun_stat
    (fun () -> context_size ~non_dead:true (Simplify.sim_get_context inst_sim_state)) inst_num_of_clauses;
  
  assign_fun_stat (fun () -> PassiveQueues.num_elem inst_passive_queue) inst_num_in_passive;

(* res_state *)
  {
(*   res_context          = res_context; *)
   inst_sim_state        = inst_sim_state;
   inst_input_clauses    = BCSet.empty;

   inst_cl_params        = BCMap.empty;
   inst_unif_index       = ClauseUnifIndex.create ();
   inst_passive_queue    = inst_passive_queue;
   inst_unprocessed      = [];
   ga_activity           = TMap.empty;
   soft_assumptions      = TSet.empty;
   solver_num_cl_limit   = 1;
   solver_counter        = 0;
 }


let inst_get_all_input_clauses is = is.inst_input_clauses 

let clause_in_is is clause = BCMap.mem clause is.inst_cl_params

let get_is_dead is clause = Simplify.sim_is_dead is.inst_sim_state clause

let get_cl_param is clause = 
  try 
    BCMap.find clause is.inst_cl_params
  with 
    Not_found -> failwith "instantiation_loop: cl_param should be defined"
        
        
let cl_list_to_cl_param_list is cl_list = 
  List.map (fun cl -> (cl, get_cl_param is cl)) cl_list

(* BCMap.cardinal is a killer *)
(* let get_num_of_clauses is = BCMap.cardinal is.inst_cl_params *)

let get_num_of_clauses is = sim_state_num_clauses is.inst_sim_state ~non_dead:false 

let get_pre_model is =  inst_cps_into_pre_model is.inst_cl_params


    (*------------ unprocessed --------------------*)

    (* unprocessed is a list of newly generated clauses *)
    (* we cannot put them to passive since some truth val of some var *)
    (* can be not defined at this stage *)
    
    
let add_clause_to_unprocessed is clause =
  dbg D_trace (lazy ("add_clause_to_unprocessed: "^(Clause.to_string clause)));
  is.inst_unprocessed <- clause::is.inst_unprocessed;
  incr_int_stat 1 inst_num_in_unprocessed
    
    (*--------------------Passive QUEUES-----------------*)

    (* passive queue shortcuts *)

let finalise_passive is =
  dbg D_finalise_pq (lazy ("finalise passive with size "
                           ^(string_of_int (PassiveQueues.num_elem is.inst_passive_queue))));
  PassiveQueues.finalise is.inst_passive_queue
    
    
let remove_from_passive is = PassiveQueues.remove_from_passive is.inst_passive_queue
    
let add_to_passive is clause = 
  check_empty_clause clause;
  dbg D_trace (lazy (" add_to_passive: "^(Clause.to_string clause)));
  PassiveQueues.add_to_passive is.inst_passive_queue clause
    
    (* change empty clause check to unprocessed*)
let add_clauses_to_passive is clauses =  
  List.iter check_empty_clause clauses;
  dbg_env D_trace
    (fun () ->
      List.iter (fun clause -> dbg D_trace (lazy (" add_to_passive: "^(Clause.to_string clause)))) clauses
    );
  
  (* add all clauses to passive *)
  PassiveQueues.add_list_to_passive is.inst_passive_queue clauses
    
    (*-------------------- end Passive QUEUES -----------------*)
    
    (*----------------- unification index -------------------------*)

let get_selected_lit cl_param =
  (* choose selected literal *)
  let sel_lit =
    try
      inst_cp_get_sel_lit cl_param
    with 
      Inst_sel_lit_undef ->
        failwith "get_selected_lit: clause should have selected literals here"
  in
  (* return that literal *)
  sel_lit


    (* add to unif index *)
    
let add_to_unif_index is clause_cp clause =

  let sel_lit = get_selected_lit clause_cp in
  ClauseUnifIndex.add_clause_with_sel is.inst_unif_index sel_lit clause


    (*--------------------------------*)
    
let eliminate_from_unif_index is main_clause_cp main_clause =
  let sel_lit = get_selected_lit main_clause_cp in
  try
    ClauseUnifIndex.elim_clause_with_sel is.inst_unif_index sel_lit main_clause
  with
    Not_found ->
      out_warning "eliminate_from_unif_index: the clause in not in the index!\n"

	(* eliminates all clauses indexed by lit from unif_index and returns*)
	(* the eliminated clause list   *)
	
let eliminate_lit_from_unif_index is lit =
  ClauseUnifIndex.eliminate_lit is.inst_unif_index lit

    (* get unification candidates for a (negated) literal *)
let get_compl_unif_candidates is lit =
  ClauseUnifIndex.get_unif_candidates is.inst_unif_index (add_compl_lit lit)

    (*---------------end  unification index -------------------*)
    

(*--------- soft assumptions --------*)

(* prop_solver can remove some soft assumptions which still can remain in is.soft_assumptions *)
let add_soft_assumptions_lit is lit = 
  if !current_options.soft_assumptions 
  then
    ( 
      dbg D_soft (lazy ("add: "^(Term.to_string lit)));
      assert (not (TSet.mem (add_compl_lit lit) is.soft_assumptions));          
      is.soft_assumptions <- TSet.add lit is.soft_assumptions;
      Prop_solver_exchange.add_soft_assumptions [lit]
     )

let add_soft_assumptions is lits = 
  if !current_options.soft_assumptions 
  then
    ( 
      List.iter (add_soft_assumptions_lit is) lits
     )

let remove_soft_assumptions is lit_list = 
  if !current_options.soft_assumptions 
  then
    ( 
      dbg D_soft (lazy ("rm: "^(Term.term_list_to_string lit_list)));
      Prop_solver_exchange.remove_solver_assumptions ~soft:true lit_list; 
      let lit_set = TSet.of_list lit_list in
      is.soft_assumptions <- TSet.diff is.soft_assumptions lit_set 
     )

let add_soft_assumptions_with_replacement_lit is lit = 
  if !current_options.soft_assumptions 
  then
    (
     let compl_lit = add_compl_lit lit in 
     (if (TSet.mem compl_lit is.soft_assumptions)
     then 
       remove_soft_assumptions is [compl_lit]
     );
     add_soft_assumptions_lit is lit
    )

let add_soft_assumptions_with_replacement is lits = 
  List.iter (add_soft_assumptions_with_replacement_lit is) lits

let add_soft_assumptions_sel is cl_param = 
  let sel_lit = get_selected_lit cl_param in
(*
  let sel_gr = Prop_solver_exchange.get_grounded_lit sel_lit in 
  add_soft_assumptions_lit is sel_gr
*)
(*  add_soft_assumptions_lit is sel_lit *)
  add_soft_assumptions_with_replacement_lit is sel_lit

(*--------- end soft assumptions -----------*)

let add_to_active is cl_param clause =
  if
    ((not (inst_get_in_active cl_param))
       &&
     (not (get_is_dead is clause)))
  then
    (
     dbg D_active (lazy ("add: "^(Clause.to_string clause)
                         ^" sel_lit: "^(Term.to_string (get_selected_lit cl_param))));
     inst_set_in_active true cl_param;
     add_to_unif_index is cl_param clause;
     add_soft_assumptions_sel is cl_param;
     incr_int_stat 1 inst_num_in_active;
    )
  else ()
      
let remove_from_active is cl_param clause =
  if (inst_get_in_active cl_param)
  then
    (eliminate_from_unif_index is cl_param clause;
     inst_set_in_active false cl_param;
     dbg D_active (lazy ("rm clause: "^(Clause.to_string clause)));
     (*     out_str ("\n Remove from Active: "^(Clause.to_string clause));*)
     (*     out_str ("Sel lit: "^(Term.to_string (Clause.get_sel_lits)))*)
     incr_int_stat (-1) inst_num_in_active
    )
  else ()

let remove_lit_from_active is lit =
  (*  out_str ("\n Remove Lit: "^(Term.to_string lit));*)
  let cl_list = eliminate_lit_from_unif_index is lit in
  let set_param clause =
    dbg D_active (lazy ("rm lit: "^(Clause.to_string clause)));
    (*    out_str ("\n Remove from Active: "^(Clause.to_string clause));*)
    let cl_param = get_cl_param is clause in
    inst_set_in_active false cl_param;
    incr_int_stat (-1) inst_num_in_active
      (*    out_str ("Removed from Unif: "^(Clause.to_string clause))*)
  in
  List.iter set_param cl_list;
  cl_list
    
let move_from_active_to_passive is cl_param clause =
  dbg D_active_to_passive (lazy (Clause.to_string clause));
  remove_from_active is cl_param clause;
  (* add_clause_to_unprocessed clause;*)
  (*  out_str ("move_from_active_to_passive: "^(Clause.to_string clause)^"\n");*)
  ((*if (not (in_passive clause)) then*)
   (* should not change when_born ! since it can be age priority queue *)
   (* which would destroy integrety of the queue*)
   ((*Clause.assign_when_born !num_of_instantiation_loops clause;*)
    add_to_passive is clause)
     (* else num_in_passive := !num_in_passive+1*)
  );
  incr_int_stat 1 inst_num_moves_active_passive
    
    (*  moves all clauses from univ index which are indexed *)
    (* by the same literal *)
    
let move_lit_from_active_to_passive is lit =
  dbg D_active_to_passive (lazy ((" move_lit: " )^(Term.to_string lit)));
  let cl_list = remove_lit_from_active is lit in

  (*    out_str ("Move lit form act to pass: "^(Term.to_string lit)^"\n");*)
  let to_pass clause =
    
    (*   add_clause_to_unprocessed clause;*)
    (*    Clause.assign_when_born (!num_of_instantiation_loops+2) clause;*)
    (*debug*)
    
    dbg_env D_active_to_passive 
      (fun () -> 
	let sel_lit = inst_cp_get_sel_lit (get_cl_param is clause) in
(*    let var_entry = get_prop_gr_var_entry sel_lit in *)
(*    out_str ("Sel Lit: "^(Term.to_string sel_lit)^"\n"
      ^"Var entry:"^(var_entry_to_string solver var_entry)^"\n");*)
	dbg D_active_to_passive (lazy ((Clause.to_string clause)^" sel:  "^(Term.to_string sel_lit)^"\n"));

      );
    (
     (*if (not (in_passive clause)) then*)
     ((*Clause.assign_when_born !num_of_instantiation_loops clause;*)
      (* out_str ("\n Act_to_Pass: "^(Clause.to_string clause)^"\n");*)
      add_to_passive is clause)
       (*else num_in_passive := !num_in_passive+1*)
    );
    incr_int_stat 1 inst_num_moves_active_passive
  in
  List.iter to_pass cl_list
    
    (*------------------------------------------------*)

(* eliminate_clause_cl_param  is clause cl_param; *)
(* clause is eliminated and assigned dead *)
(* if regenerated it will not be added    *)

let eliminate_clause_cl_param is clause cl_param =  
  dbg D_trace (lazy ("eliminate_clause_cl_param: "^(Clause.to_string clause)));

  Simplify.assign_dead_and_remove_from_indexes is.inst_sim_state clause; 
  remove_from_active is cl_param clause
    
let rec eliminate_clause is clause =  
  if (clause_in_is is clause) 
  then 
    begin
      eliminate_clause_cl_param is clause (get_cl_param is clause);
(* TODO: orphan elimination *)
(* TODO: orphan elimination is not compatible with domain instantiation (or we need to copy the eliminated clause after dom inst) *)
(*       Clause.assign_is_dead true clause; *)

(*
  incr_int_stat 1 inst_num_child_elim;
  (if (!current_options.inst_orphan_elimination) 
  (* TODO: check orpahn elimination; should not assign children is_dead as above *)
  then
  (
  let children = get_inst_children cl_param in
  List.iter (eliminate_clause is) children
  )
  else 
  ()
  )
*)
    end
  else 
    ()

(*------------------------------------------------*)
(* removes clause from the state and context;     *)
(* the clause can be regenerated and added later  *)

let remove_from_inst_state is clause = 
  dbg D_trace (lazy ("remove_from_inst_state: "^(Clause.to_string clause)));

  let cl_param = get_cl_param is clause in
  remove_from_active is cl_param clause;
  Simplify.remove_from_indexes_and_context is.inst_sim_state clause;
  is.inst_cl_params <- BCMap.remove clause is.inst_cl_params
(* TODO: add remove from passive; needs changes in passive queues for lazy removal based on sets; *)
(* at the moment we assume that this clause is already removed from passive *)

      
      
(*------------- Simplification -------------------*)
      
let sim_clause_mem is c = 
  try
    (Simplify.sim_mem_clause is.inst_sim_state c) 
  ||
    (not ((Simplify.forward_subset_subsume is.inst_sim_state c) == c))

  with 
    Eliminated -> true

let check_sim_mem is c = 
  (if (sim_clause_mem is c)       
  then 
    raise Eliminated
  else c
  )
    
(* can raise Empty_clause(clause) *)
let check_empty_clause_return clause = 
  check_empty_clause clause;
  clause

(* can raise Eliminated *)    
let sim_fwd_new_cl_fun_list is = 
  let o = !current_options in
(* sim functions in the list: f c -> c' or raise Eliminated,   *)
(* if c' is in sim_state then Eliminated will be raised so we assume that f does not add c' into the sim_state context *) 
  [ 
    check_sim_mem is;
    check_empty_clause_return;
    Simplify.tautology_elim; 

    if o.inst_eq_res_simp then Simplify.equality_resolution_simp else id_fun; 
     (* for some reason generally inst_eq_res_simp degrades the performance *)

    Simplify.forward_subset_subsume is.inst_sim_state; 

    if o.inst_subs_new then (Simplify.forward_subs_strict is.inst_sim_state) else id_fun;

    if o.inst_prop_sim_new &&
      ((get_val_stat inst_num_of_learning_restarts) >= o.inst_start_prop_sim_after_learn)
    then 
      (Simplify.forward_prop_subsume (* is.res_sim_state *))
    else
      id_fun;
  ]

(* simplify light and add to the inst_sim_state *)
(* can raise Eliminated *)
let simplify_light_new_clause is clause =
  dbg D_sim (lazy ("simplify_light_new_clause: "^(Clause.to_string clause)));

  let forward_light_fun_list = sim_fwd_new_cl_fun_list is in
  let sim_clause = fix_point (fold_left_fun_list forward_light_fun_list) clause in
  
  let (new_clause,s_subsumed_clauses) = Simplify.sim_add_clause is.inst_sim_state sim_clause in
  
  List.iter (eliminate_clause is) s_subsumed_clauses;
  
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

(* process new clause and  add to unprocessed *)
let process_new_clause is clause =
  dbg D_sim (lazy ("process_new_clause: "^(Clause.to_string clause))); 
  if (not (clause_in_is is clause))
  then
    (
     try
       let sim_clause = simplify_light_new_clause is clause in     
       Prop_solver_exchange.add_clause_to_solver sim_clause;       
       (if (!current_options.qbf_dom_pre_inst) (* TODO clean up *)
       then
         (
          let pre_inst_clauses = Inference_rules.dom_pre_inst SystemDBs.type_to_domain clause in
          dbg D_trace (lazy ("pre_inst: "^(Clause.clause_list_to_string pre_inst_clauses))); 

          (* only add pre_inst_clauses to sat solver *)
          List.iter Prop_solver_exchange.add_clause_to_solver pre_inst_clauses;          
         )
       );
       (if (not (clause_in_is is sim_clause))
       then
         (
          is.inst_cl_params <- BCMap.add sim_clause (inst_create_cp ()) is.inst_cl_params;
          add_clause_to_unprocessed is sim_clause;
         )
       )
       (* sim_clause *)
     with 
       Eliminated -> 
         (
          dbg D_sim (lazy ("process_new_clause: eliminated: "^(Clause.to_string clause))); 
         )
    )
  else 
    (
     dbg D_sim (lazy ("process_new_clause: in_is: "^(Clause.to_string clause))); 
    )

(*---------------*)
exception Given_clause_is_dead

let add_conclusion_to_unprocessd is ~given_clause ~concl_clause =
  process_new_clause is concl_clause;
  if (get_is_dead is given_clause)
  then 
    (* we abort all further
       inferences with the given clause,
       later we can also add elimination of all other conclusions
       with this clause but not this one!,
       also in general after backward subsumption we can eliminate
       all children of the subsumed clause provided that we add
       the clause which subsumes to the clause set *)
    ( 
      dbg D_sim (lazy ("process_new_clause: Given_clause_is_dead: "^(Clause.to_string given_clause))); 
      raise Given_clause_is_dead 
     )
  else ()
      


(*--------------------*)
let get_forward_simp_fun_list is = 
  let o = !current_options in
  [ 
    if o.inst_subs_given then (Simplify.forward_subs_strict is.inst_sim_state) else id_fun;
    (if o.inst_prop_sim_given &&
      ((get_val_stat inst_num_of_learning_restarts) >= o.inst_start_prop_sim_after_learn)
    then
      (Simplify.forward_prop_subsume) 
    else id_fun
    );

(* subsumption *) (* TODO: add strict subsumption *)
(*
  (match o.res_forward_subs with 
  |Subs_Full               -> (Simplify.forward_subs rs.res_sim_state) 
  |Subs_By_Length (length) -> failwith "Subs_By_Length: restore support"
  |Subs_Subset             ->  id_fun
  );

(* subs_res *)
  if o.res_forward_subs_resolution then (Simplify.forward_subs_res rs.res_sim_state) else id_fun;
 *)
  ]

exception Given_Eliminated

let simplify_given_clause is clause =
  dbg D_sim (lazy ("simplify_given_clause: "^(Clause.to_string clause)));       

  try
    let fwd_fun_list = get_forward_simp_fun_list is in
    let sim_clause = fix_point (fold_left_fun_list fwd_fun_list) clause in

(*      let new_clause = process_new_clause is sim_clause in *)
    
    if (not (sim_clause == clause))
    then
      (
       dbg D_sim (lazy ("simplify_given_clause: elim: "^(Clause.to_string clause)));       
       dbg D_sim (lazy ("simplify_given_clause: new: "^(Clause.to_string sim_clause)));       
       eliminate_clause is clause;
(*	 res_clause_register_subsumed_by ~by:new_clause clause;	 *)
       if (not (clause_in_is is sim_clause))
       then
         (
          is.inst_cl_params <- BCMap.add sim_clause (inst_create_cp ()) is.inst_cl_params;    
          Prop_solver_exchange.add_clause_to_solver sim_clause;
          sim_clause        
         )              
         (* sim_clause *)
       else
         (dbg D_sim (lazy ("simplify_given_clause: Given_Eliminated: "^(Clause.to_string sim_clause)));       
          raise Given_Eliminated (* sim_clause *)         
         )
      )
    else 
      clause
  with
    Eliminated -> 
      (
       eliminate_clause is clause;
       dbg D_sim (lazy ("simplify_given_clause: Given_Eliminated: "^(Clause.to_string clause)));       
       raise Given_Eliminated (* sim_clause *)
      )
        
(* can raise Eliminated *)    
let is_redundant_fun_list is = 

(* sim functions in the list: f c -> c' or raise Eliminated,   *)
(* if c' is in sim_state then Eliminated will be raised so we assume that f does not add c' into the sim_state context *) 
  [ 
    check_sim_mem is;
    check_empty_clause_return;
    Simplify.tautology_elim;  
    Simplify.forward_subset_subsume is.inst_sim_state; 
  ]

(* used in  all_instantiations below *)
let is_redundant is clause =
  dbg D_sim (lazy ("try is_redundant: "^(Clause.to_string clause)));

  let is_redundant_fun_list_is = is_redundant_fun_list is in
  try 
   ignore ((fold_left_fun_list is_redundant_fun_list_is) clause);
    false
  with 
    Eliminated -> true
 
    (*----------------------- End Simplification----------------------*)


    (*--------------------- Ground atom activity ---------------------*)

let get_lit_activity is lit =
  let gr_lit = Prop_solver_exchange.get_grounded_lit lit in 
  let gr_atom = Term.get_atom gr_lit in 
  let ga_act = 
    try 
      TMap.find gr_atom is.ga_activity 
    with 
      Not_found ->
        let new_ga_act =
          {
           ga_pos = 0; 
           ga_neg = 0;
           change_activity_limit = !current_options.inst_activity_threshold;
         }
        in
        is.ga_activity <- TMap.add gr_atom new_ga_act is.ga_activity;
        new_ga_act
  in 
  ga_act



let get_lit_activity_val is lit = 
  let ga_act =  get_lit_activity is lit in 
  if (Term.is_neg_lit lit)
  then ga_act.ga_neg
  else ga_act.ga_pos
      

let lit_activity_compare is l1 l2 =
  compare (get_lit_activity is l1) (get_lit_activity is l2)

(*
let activity_condition is lit =
  let activity = get_lit_activity_val is lit in
(*  (activity < ((get_val_stat inst_max_lit_activity) lsr 2 ))
 ||
*)
   (activity < !current_options.inst_activity_threshold)
*)

let incr_lit_activity is i lit =
  let ga_act = get_lit_activity is lit in 
  if (Term.is_neg_lit lit)
  then 
    (ga_act.ga_neg <- ga_act.ga_neg + i)
  else 
    (ga_act.ga_pos <- ga_act.ga_pos + i)

let incr_parent_activity is clause = 
  let main_parents = Clause.get_main_parents clause in 
  let f parent =  
    let sel_lit = inst_cp_get_sel_lit (get_cl_param is parent) in
    incr_lit_activity is 1 sel_lit
  in
  List.iter f main_parents (* main_parents is a singleton but anyway *)


(* if the literal is over active try to swap its value *)
(* true if lit val remains unchanged / false if either compl become true*)
let lit_activity_check is lit =
  if (not !current_options.inst_lit_activity_flag)
  then (true)
  else
    begin
       let ga_act = get_lit_activity is lit in 
       let make_change_test =
         if (Term.is_neg_lit lit)
         then 
           (ga_act.ga_neg >= ga_act.ga_pos + ga_act.change_activity_limit)
         else             
           (ga_act.ga_pos >= ga_act.ga_neg + ga_act.change_activity_limit)
       in
       if make_change_test 
       then
         begin
           let gr_lit = Prop_solver_exchange.get_grounded_lit lit in 
           let compl_gr_lit = add_compl_lit gr_lit in
           dbg D_solve (lazy ("lit_activity_check"));  

(*           remove_soft_assumptions is [compl_gr_lit]; *) (* might be not enough; so clear all soft assumptions *)
           remove_soft_assumptions is (TSet.elements is.soft_assumptions);
           if (Prop_solver_exchange.preserve_lits_vals_solver [compl_gr_lit]) 
           then
             (
	      incr_int_stat 1 inst_lit_activity_moves;
              ga_act.ga_neg <- 0;
              ga_act.ga_pos <- 0;
              ga_act.change_activity_limit <-
		(2 * ga_act.change_activity_limit);  
              false 
             )
           else (* compl_gr_lit is inconsistent with the solver *) 
             (
              ga_act.change_activity_limit <- 10000000; (*any big number*)                
              true (* old value remains *)
             )
         end
       else
         (true)
    end


(*--------------------- End Ground atom activity -----------------*)

(*-------- lit sel ------*)

let consistent_with_solver is lits = 
  let consist_lits = List.find_all 
      (fun lit -> 
        (Prop_solver_exchange.get_solver_lit_val_gr lit) 
   (*
        (Prop_solver_exchange.get_solver_lit_val_gr lit) 
*)
           &&
        (not (TSet.mem  
                (Prop_solver_exchange.get_grounded_lit (add_compl_lit lit)) is.soft_assumptions)) 
(*
        (not (TSet.mem  
                 (add_compl_lit lit) is.soft_assumptions)) 
*)
      )
      lits 
  in
  dbg D_inst (lazy ("consistent with solver: "^(Term.term_list_to_string consist_lits)));
  if (List.length consist_lits) > 0
  then 
    consist_lits
  else
    begin
      dbg D_solve (lazy ("all lits inconsistent: "^(Term.term_list_to_string lits)));
      match (Prop_solver_exchange.solve ~soft:true ()) with
      | PropSolver.Unsat ->
	  (             
                        dbg D_solve (lazy ("Unsatisfiable_gr in selection_renew_solver"));
	                raise Unsatisfiable_gr (* solve () can have default assumptions *)
	               ) 
      | PropSolver.Sat ->       
          begin
            (if !current_options.soft_assumptions 
            then 
                (* run once more asserting literals (and thier groundings) which are in the clause and 
                    true grounding of which is true in the previoud run *)
              
              let solver_true_gr_lit_ngr =  (* lits groundings of which are ture in solver *)
                List.find_all Prop_solver_exchange.get_solver_lit_val_gr lits in 
            
              dbg D_solve (lazy ("add_soft_assumptions_with_replacement: "^(Term.term_list_to_string solver_true_gr_lit_ngr)));
    
              add_soft_assumptions_with_replacement is solver_true_gr_lit_ngr; (* add them to soft without grounding *)
       
       
              let solver_true_gr_lit_gr = List.map Prop_solver_exchange.get_grounded_lit solver_true_gr_lit_ngr in

              dbg D_solve (lazy ("add_soft_assumptions_with_replacement: "^(Term.term_list_to_string solver_true_gr_lit_gr)));            
              add_soft_assumptions_with_replacement is solver_true_gr_lit_gr;

              match (Prop_solver_exchange.solve ~soft:true ()) with
              | PropSolver.Unsat ->
	          (             
                                dbg D_solve (lazy ("Unsatisfiable_gr in selection_renew_solver"));
	                        raise Unsatisfiable_gr (* solve () can have default assumptions *)
	                       ) 
              | PropSolver.Sat ->
                  ()
            ); (* end soft *)

            (* List.find_all Prop_solver_exchange.get_solver_lit_val_gr lits*)
            let new_consist_lits = 
              List.find_all    
                (fun lit -> 
                  (Prop_solver_exchange.get_solver_lit_val_gr lit) 
                    (*
                      (Prop_solver_exchange.get_solver_lit_val_gr lit) 
                     *)
                    &&
(*
                  (not (TSet.mem  
                          (add_compl_lit lit) is.soft_assumptions))
*)

                  (not (TSet.mem  
                          (Prop_solver_exchange.get_grounded_lit (add_compl_lit lit)) is.soft_assumptions))
 
                )
                lits
            in
            dbg D_solve (lazy ("new consistent lits: "^(Term.term_list_to_string new_consist_lits)));
            dbg_env D_inst 
              (fun () -> 
                if ((List.length new_consist_lits) = 0) 
                then 
                  (
                   let f lit = 
                     dbg D_inst (lazy ("lit: "^(Term.to_string lit)
                                       ^" lit_gr: "^(Term.to_string (Prop_solver_exchange.get_grounded_lit lit))
                                       ^" compl_mem: "^(string_of_bool 
                                                            (TSet.mem  
                                                               (add_compl_lit lit) is.soft_assumptions))
                                       ^" val: "^(string_of_bool (Prop_solver_exchange.get_solver_lit_val lit))
                                       ^" val_gr: "^(string_of_bool (Prop_solver_exchange.get_solver_lit_val_gr lit))
                                       ^" compl_gr_mem: "^(string_of_bool 
                                                             (TSet.mem  
                                                                (Prop_solver_exchange.get_grounded_lit (add_compl_lit lit)) is.soft_assumptions)
                                                          )));
                   in
                   List.iter f lits
                  );
                if (List.length new_consist_lits) = 0 
                then
                begin  
                  match (Prop_solver_exchange.solve ~soft:true ()) with
                  | PropSolver.Unsat ->
	              (             
                                    dbg D_solve (lazy ("Unsatisfiable_gr in selection_renew_solver"));
	                            raise Unsatisfiable_gr (* solve () can have default assumptions *)
	                           ) 
                  | PropSolver.Sat ->
                      ( failwith "consistent_with_solver: sat but no consistent lits")
                end
              ); (* end dbg *)
            
          

            assert ((List.length new_consist_lits) > 0);
            new_consist_lits      
          end           
    end
  
(* filters lits with minimal combined cl_measure of unif candidates in the index *)
(* cl_measure : cl -> int *)
let find_lits_min_side is cl_measure lits = 
  assert ((List.length lits) > 0);
  ClauseUnifIndex.filter_lits_min_unif_cand is.inst_unif_index cl_measure lits


let find_sel_lit is clause = 
 (*  Prop_solver_exchange.add_clause_to_solver clause; *)(* dbg *)
  let lits = consistent_with_solver is (Clause.get_lits clause) in

  assert ((List.length lits) > 0);
  let min_lits =
    if ((List.length lits) = 1)
    then 
      lits 
    else
      let side_measure_opt = !current_options.inst_lit_sel_side in
      match side_measure_opt with 
      |CM_none -> lits
      | _ ->  
          begin
            let cl_measure = Clause.cl_measure_to_fun side_measure_opt in
            find_lits_min_side is cl_measure lits
          end
  in
  assert ((List.length min_lits) > 0);

  let sel_lit = 
    if (List.length min_lits) = 1 
    then 
      List.hd min_lits 
    else
      let cmp_fun = (Term.lit_cmp_type_list_to_lex_fun 
		       !current_options.inst_lit_sel) in
      list_find_max_element cmp_fun min_lits
  in
  sel_lit  
    


    (*-----------------------All_instantiations----------------------*)
      
exception Activity_given_sel_changed

let all_instantiations is main_cl_param main_clause =
  dbg D_trace (lazy "");
  dbg D_trace (lazy "------------------ ");
  dbg D_trace (lazy "all_instantiations");
  
  try
    dbg D_inst (lazy ("main_clause: "^(Clause.to_string main_clause)));       
(*
  (*we assume that sel in main_clause is checked before *)
  (*on accordance with solver*)

(* TODO restore activity: *)
  let sel_lit_tmp = inst_get_sel_lit main_cl_param main_clause in
  
  (try
  ( (*uncommnet for lit activity!*)
  Prop_solver_exchange.lit_activity_check
  move_lit_from_active_to_passive sel_lit_tmp;
  Prop_solver_exchange.increase_lit_activity 1 sel_lit_tmp)
  with Prop_solver_exchange.Activity_Check ->
  (Prop_solver_exchange.selection_renew
  move_lit_from_active_to_passive Selection.inst_lit_sel main_clause));

  let sel_lit = Clause.inst_get_sel_lit main_clause in
 *)

    let sel_lit = find_sel_lit is main_clause in

    inst_assign_sel_lit sel_lit main_cl_param; 
(*
      if (sel_consistent_with_solver main_cl_param)
      then 
        (
         dbg D_inst (lazy ("old sel is consistent with solver"));
         inst_cp_get_sel_lit main_cl_param
        )
      else
        (
         let new_sel_lit = 
           if min_unif_flag 
           then 
             find_lit_min_unif is main_clause
           else
             inst_selection main_clause 
         in
         dbg D_inst (lazy ("old sel is undef or NOT consistent with solver"));
         inst_assign_sel_lit new_sel_lit main_cl_param; 
         new_sel_lit
        )
*)
    dbg D_inst (lazy ("sel lit: "^(Term.to_string sel_lit)));

    let unif_candidates = (get_compl_unif_candidates is sel_lit) in

    let for_all_candidates (lit, clause_cand_list) =
      
      dbg D_inst (lazy ("cand sel lit: "^(Term.to_string lit)));
      dbg_env D_inst 
        (fun () -> 
          dbg D_inst (lazy ("----- cand clause list: -----"));
          out_str (Clause.clause_list_to_string clause_cand_list);
          dbg D_inst (lazy ("---- end cand clause list: -----"));
        );
      (* out_str_debug ("inst_try cand_list:"^"Sel_lit: "^(Term.to_string lit)^"\n"
	 ^(Clause.clause_list_to_string clause_cand_list)^"\n"); *)
      
      (*Simplification turn later on *)
      try(

	let all_clause_list = clause_cand_list in
        let all_cl_param_list = cl_list_to_cl_param_list is all_clause_list in	    

        dbg_env D_inst 
          (fun () ->
            let f  (clause,cl_param) =
              dbg D_inst (lazy ("all side clause:"^(Clause.to_string clause)));             
              dbg D_inst (lazy ("all side sel: "^(Term.to_string (inst_cp_get_sel_lit cl_param))^"\n"));
            in
            List.iter f all_cl_param_list
          );
        
        
        let (cl_param_list, move_to_passive_cl_param_list) =  
          List.partition            
            (fun (_c,cl_param) -> 
              (* Prop_solver_exchange.add_clause_to_solver c;*) (* dbg *)
              (sel_consistent_with_solver cl_param) && (lit_activity_check is (inst_cp_get_sel_lit cl_param))  
            )
            all_cl_param_list 
        in


        List.iter 
          (fun (clause,cl_param) -> move_from_active_to_passive is cl_param clause) move_to_passive_cl_param_list;


(* preserve main selection in case it was changed by activity moves *)        
        (if (Prop_solver_exchange.preserve_lits_vals_solver_gr [sel_lit])
        then 
          ()
        else
          (
           add_clauses_to_passive is [main_clause]; (* move main clause to passive *)   
           raise Activity_given_sel_changed
          )
        );

	(*	let clause_list = simplify_clause_list  clause_cand_list  in*)
	(*      let clause_list = clause_cand_list in*)
	if (cl_param_list != [])
	then
	  try
	    (	   

(*   sel_lit_in_ui does not work with simplificaions
	      let sel_lit_in_ui =  ClauseUnifIndex.in_unif_index is.inst_unif_index sel_lit in
*)

(*
              let is_redundant_fun c = sim_clause_mem is c in
*)

(*              out_str "dbg: is_redundant_fun";
              let is_redundant_fun c = false in
*)
              let is_redundant_fun c = is_redundant is c in

              dbg_env D_inst 
                (fun () ->
                  let f  (clause,cl_param) =
                    dbg D_inst (lazy ("side clause:"^(Clause.to_string clause)
                                                        ^" sel: "^(Term.to_string (inst_cp_get_sel_lit cl_param))^"\n"))
                  in
                  List.iter f cl_param_list
                );

              dbg D_inst (lazy ("sel_lit: "^(Term.to_string sel_lit)
                                ^" val_gr  "^(string_of_bool (Prop_solver_exchange.get_solver_lit_val_gr sel_lit))));
         
              dbg D_inst (lazy ("side lit: "^(Term.to_string lit)
                                ^" val_gr  "^(string_of_bool (Prop_solver_exchange.get_solver_lit_val_gr lit))));
                



              assert ((Prop_solver_exchange.get_solver_lit_val_gr sel_lit) && (Prop_solver_exchange.get_solver_lit_val_gr lit));

(* before instantiation_domain_single (18/04/2018) *)

(*
	      let conclusion_list =
		Inference_rules.instantiation_norm 
                  ~is_redundant_fun (main_clause, main_cl_param) sel_lit cl_param_list lit in
*)
              
	      let conclusion_list =
                if !current_options.qbf_mode && (!current_options.qbf_dom_inst != QBF_dom_inst_none) (* TODO: clean-up this *)
                then                 
                  let result =
                    Inference_rules.instantiation_domain_single 
                      !current_options.qbf_dom_inst
                      SystemDBs.type_to_domain (main_clause, main_cl_param) sel_lit cl_param_list lit 
                  in
                   (* might have problems with subtyping as types might change; should not happen with QBF though *)
                  match result with 
                  |Main_dom_inst conclusions -> 
                      (
                       dbg D_dom_inst (lazy ("elim: main_clause: "));
                       dbg D_dom_inst (lazy (Clause.to_string main_clause));
                       dbg D_dom_inst (lazy ("conclusions: "));
                       dbg D_dom_inst (lazy (Clause.clause_list_to_string conclusions));                  
                       eliminate_clause is main_clause;  (* will be declared dead and not added later to active *)
                       conclusions
                      )
                  |Side_dom_inst conclusions ->
                      (
                       let (side_clauses, _param_list) = List.split cl_param_list in  
                       List.iter (eliminate_clause is) side_clauses;
                       conclusions
                      )
                else 
                  (* the default version *)
		  Inference_rules.instantiation_norm 
                    ~is_redundant_fun (main_clause, main_cl_param) sel_lit cl_param_list lit 
              in
     
(*	      out_str "conclusion_list after\n";*)
(*	      let conclusion_list = List.rev conclusion_list in*)
(* TODO restore activity: *)
(*	      Prop_solver_exchange.increase_lit_activity (List.length conclusion_list) lit; *)
	      
	      let apply_to_concl clause =
                try
                  begin
                    if !current_options.qbf_mode && (!current_options.qbf_dom_inst != QBF_dom_inst_none) (* TODO: clean-up this *)
                    then
                      (process_new_clause is clause; (* main_clause can be dead but conclusion is needed *)
                       incr_parent_activity is clause;
                      )
                    else (* default *)
                      (
                       add_conclusion_to_unprocessd is ~given_clause:main_clause ~concl_clause:clause;
                       incr_parent_activity is clause;
		       (* Prop_solver_exchange.add_clause_to_solver clause; *)		 
                      )
                  end
                with 
                  Eliminated -> 
                    (
                     dbg D_inst (lazy ("concl eliminated: "^(Clause.to_string clause)));
                    )
	      in
	      List.iter apply_to_concl conclusion_list;
	        )
	  with  
            Unif.Unification_failed -> 
              (
               dbg D_inst (lazy (" Unif.Unification_failed: compl: "^(Term.to_string sel_lit)^" "^(Term.to_string lit)));
              )
	else (* (cl_param_list = []) *)
          () 
       )
(* TODO restore activity: *)

      with Activity_Check -> 
	(
         dbg D_inst (lazy (" Activity_Check "));
	)
    in
    List.iter 
      for_all_candidates 
      unif_candidates;
  with
  |Given_clause_is_dead -> 
      (
       dbg D_inst (lazy (" Given_clause_is_dead: "));
       raise Given_Eliminated
      )
	
	(*-------------- end all_instantiations------------------*)
	
exception Given_Splitted


    


(*-----------------------------------------------*)
(* raise  Given_Splitted if given clause is splitted; and add splitting into is *)
(* if given is not splitted then return unit *)

let splitting_given is given_clause = 
  (match !current_options.splitting_mode with (* TODO: add splitting_cvd, splitting_nvd *)
  | Split_Full ->
      begin
        check_empty_clause given_clause;
        let splitted_clauses = Splitting.splitting Definitions.def_env_glb ~out_progress:false [given_clause] in
        match splitted_clauses with 
        |[_] -> () (* no splitting *)
        |_-> 
            
	    ( 
              dbg D_splitting (lazy ("rm: "^(Clause.to_string given_clause)));

	      remove_from_inst_state is given_clause;
	      let f new_clause =
                dbg D_splitting (lazy ("add: "^(Clause.to_string new_clause)));
	        Clause.assign_ps_when_born_concl
	          ~prem1:[given_clause] ~prem2:[] ~c: new_clause;
                process_new_clause is new_clause;
	      in
	    List.iter f splitted_clauses;	  
	      raise Given_Splitted
	     )
      end
  | _ -> ()
  )

(*----------------------------------------*)
(* can raise  PassiveQueues.Passive_Empty *)

(* let given_clause_ref = ref Undef *) (* TODO: used for multiple unsat cores; check/fix this *) 

let rec get_next_given_clause is = 
  let given_clause = remove_from_passive is in	
 (* given_clause_ref:= Def(given_clause); *)

  let given_param = get_cl_param is given_clause in
  dbg D_given (lazy 
		 (" removed from passive: "^ (Clause.to_string given_clause)^" ln: "
                  ^(string_of_int (Clause.length given_clause))
                  ^" when born: "^(string_of_int (Clause.get_ps_when_born given_clause))));  
  if      
    (
     (inst_get_in_active given_param) 
   ||
     (get_is_dead is given_clause))
  then 
    (
     dbg_env D_inst
       (fun () ->
         (if (inst_get_in_active given_param) 
         then 
           (
               dbg D_inst (lazy ("given already in_active: "^(Clause.to_string given_clause)));
           )   
         );
         (if (get_is_dead is given_clause) 
         then 
           (
            dbg D_inst (lazy ("given is dead: "^(Clause.to_string given_clause)));
           )   
         )
       ); (* end dbg *)
     get_next_given_clause is
    )
  else
    begin
      try
        let simplified_given_clause = simplify_given_clause is given_clause in
        dbg_env D_given 
          (fun () ->
            (if (not (simplified_given_clause == given_clause))
            then
              dbg D_given (lazy 			 
                             ("simplified is different: "
                              ^(Clause.to_string simplified_given_clause)
                            ^" when born: "^(string_of_int (Clause.get_ps_when_born simplified_given_clause))
                             )
                          );
            )
          );           
        splitting_given is simplified_given_clause;
        simplified_given_clause
      with
      | Given_Eliminated -> 
          (
           dbg D_inst (lazy "Given_Eliminated");
           get_next_given_clause is;
          )

      | Given_Splitted -> 
          (
           dbg D_inst (lazy "get_next_given_clause: Given_Splitted");
           get_next_given_clause is;
          ) 
    end


let reload_unprocessed is =
  dbg D_trace (lazy "reload_unprocessed");
  add_clauses_to_passive is is.inst_unprocessed;
  is.inst_unprocessed <- [];
  assign_int_stat 0 inst_num_in_unprocessed

let get_new_solver_num_cl_limit is =  
  let num_of_clauses =  (* (get_val_stat prop_num_of_clauses) *)  get_num_of_clauses is in
  ((int_of_float ((float_of_int num_of_clauses) *. !current_options.inst_solver_calls_frac)) + num_of_clauses + 1) 


(*----------------------------*)

(* TODO: clean: *)

(* let add_prop_unit_clauses_flag = true *)

(* let impl_unit_size_bound = 16 *)

let add_prop_impl_unit_clauses_flag () = !current_options.prop_impl_unit_size > 0


(*
let is_well_typed term = 
  try 
    Term.type_check term;
    true
  with 
    Term.Type_check_failed -> false
*)

let compose_prop_impl_unit_opt_list lit = 
  Term.compose_bool_prop_opt_list (&&) true !current_options.prop_impl_unit lit

let impl_unit_to_keep lit = 
  ((Term.get_num_of_symb lit) <= !current_options.prop_impl_unit_size) && 
  (compose_prop_impl_unit_opt_list lit) &&
  (Term.is_well_typed_term lit) 


(*
(* ground terms can cause problems with sub_typing: *)
(* grounding before typing does not adhere later sub-typing *)
(* re-typing literals does not help since we already instantiated before typing *)
(* either type check literals and eliminate that are not well typed *)
or use only non-ground lits  (not (Term.is_ground lit)) usually much less learnt non-ground
*)
    
(*
let _ = out_warning ("add_prop_unit_clauses_flag: "^(string_of_bool add_prop_unit_clauses_flag)
                     ^" impl unit size bound: "^(string_of_int impl_unit_size_bound))
*)    

(* TODO: these units are not passed to different schedule runs *)

let get_all_new_implied_units () = 
  if (!current_options.prop_impl_unit_size <= 0)
  then ([])
  else
    (
     Prop_solver_exchange.get_all_newly_implied_unit_clauses 
       ~is_relevant:impl_unit_to_keep
    )
 

(*---------*)      
(* can raise Unsatisfiable_gr *)
(* can reload unprocessed *)

let solver_check is = 
  let num_of_clauses = get_num_of_clauses is in 	
  is.solver_counter <- is.solver_counter + 1; 

  if (num_of_clauses  > is.solver_num_cl_limit || is.solver_counter > !current_options.inst_solver_per_active)      
  then
    begin
      let new_solver_num_cl_limit = get_new_solver_num_cl_limit is in 
      
      dbg D_solve (lazy ("solver_check: old solver_num_cl_limit="
			 ^(string_of_int is.solver_num_cl_limit )
			 ^(" new solver_num_cl_limit=")
			 ^((string_of_int new_solver_num_cl_limit))));      
      dbg_env D_mem 
	       (fun ()->
		 print_objsize "inst: passive:" is.inst_passive_queue;
		 print_objsize "inst: active (unif_index):" is.inst_unif_index;
		 print_objsize "inst: unprocessed:" is.inst_unprocessed;
		 Prop_solver_exchange.out_mem (); 
	       );
      
      is.solver_num_cl_limit <- new_solver_num_cl_limit;
      
      is.solver_counter <- 0; 
	
    (* adding unprocessd to solver before solving and moving to passive *)

      (if !current_options.inst_eager_unprocessed_to_passive then
        (List.iter Prop_solver_exchange.add_clause_to_solver is.inst_unprocessed)
      else
        ()
      );
            
      dbg D_solve (lazy "solver_check");
      if ((Prop_solver_exchange.solve ~soft:true ()) = PropSolver.Unsat)
	  (* || (PropSolver.solve solver_sim) = PropSolver.Unsat) *)
      then 
	(
	 raise Unsatisfiable_gr
	)
      else
	begin
          (if (add_prop_impl_unit_clauses_flag ())
          then
            (
             let new_implied_units = get_all_new_implied_units () in

             (if !current_options.share_sel_clauses
             then Shared_clauses.add_shared_clause_list new_implied_units;
             );
             dbg D_prop_impl_unit (lazy (Clause.clause_list_to_string new_implied_units));
             List.iter (process_new_clause is) new_implied_units 
            )
          else ()
          );
          (if !current_options.inst_eager_unprocessed_to_passive 
          then
	    (
	     reload_unprocessed is;
            )
	  else ()		
	  )
        end
    end
      

(*----------- process soft unsat ---------*)

let reduce_soft_unsat_core_smallest_cmp is cmp uc_soft_assumptions_set = 
 (* order by activity; remove the least active *)
  let sorted_list = List.sort cmp (TSet.elements uc_soft_assumptions_set) in
  dbg D_soft (lazy ("soft uc assumptions: "^(Term.term_list_to_string sorted_list)));
  match sorted_list with 
  | hd::tl -> 
      dbg D_soft (lazy ("soft uc removed: "^(Term.to_string hd)));
      remove_soft_assumptions is [hd]
(* unsat without soft assumptions *)
  | [] -> 
      (
       dbg D_soft (lazy ("unsat without soft assumptions"));
       raise Unsatisfiable_gr
      )



let reduce_soft_unsat_core_activity is uc_soft_assumptions_set = 
  (* order by activity; remove the least active *)
 reduce_soft_unsat_core_smallest_cmp is (lit_activity_compare is) uc_soft_assumptions_set


let reduce_soft_unsat_core_newest_term is uc_soft_assumptions_set = 
  let cmp t1 t2 = - (Term.compare t1 t2) in
  reduce_soft_unsat_core_smallest_cmp is cmp uc_soft_assumptions_set


let reduce_soft_unsat_core_full is uc_soft_assumptions_set = 
  let uc_soft_assumptions_list = TSet.elements uc_soft_assumptions_set in
  (if (uc_soft_assumptions_list = []) 
  then
    (dbg D_soft (lazy ("unsat without soft assumptions"));
    raise Unsatisfiable_gr
    )
  );
  remove_soft_assumptions is uc_soft_assumptions_list

let simple_uc_lemma uc = 
  let uc_assumptions = UnsatCore.get_assumptions uc in
  let uc_clauses = UnsatCore.get_clauses uc in 
  let compl_assumptions = List.map add_compl_lit uc_assumptions in
  let tstp_source = Clause.tstp_source_resolution uc_clauses [] in
  let lemma = create_clause tstp_source compl_assumptions in
  dbg D_soft (lazy ("lemma: "^(Clause.to_string lemma)));
  lemma

let reduce_soft_unsat_core is uc_soft_assumptions = 
(*  reduce_soft_unsat_core_newest_term is uc_soft_assumptions *)
  reduce_soft_unsat_core_activity is uc_soft_assumptions  
(* reduce_soft_unsat_core_full is uc_soft_assumptions *)


let process_soft_unsat is = 
  (* assume it was unsat last call *)
  let uc = Prop_solver_exchange.get_unsat_core ~soft:true () in 
  let uc_assumptions = UnsatCore.get_assumptions uc in 
  let uc_assumptions_set = TSet.of_list uc_assumptions in
  dbg D_soft (lazy ("all uc assumptions: "^(Term.term_list_to_string uc_assumptions)));
  dbg_env D_soft (fun () -> UnsatCore.print uc);
  let uc_soft_assumptions = TSet.inter uc_assumptions_set is.soft_assumptions in 
  reduce_soft_unsat_core is uc_soft_assumptions;

(* TODO: fix the case when  process_new_clause  raise Unsat, which will can be wrongly interperted as unsat without assumptions! *)
  (if (List.length uc_assumptions) <=  !current_options.soft_lemma_size 
  then 
    let lemma = simple_uc_lemma uc in
    try
      process_new_clause is lemma;
    with 
    | Unsatisfiable_gr_na -> raise Unsatisfiable_gr_na
    | x -> failwith (" process_soft_unsat: during adding lemma: exception: "^(Printexc.to_string x)) 
  else
    ()
   )

    
(*--------------------------LAZY LOOP BODY-----------------------------*)

let inst_lazy_loop_body is =
  dbg D_trace (lazy "");
  dbg D_trace (lazy "------------------ ");
  dbg D_trace (lazy "inst_lazy_loop_body");
  
 (* given_clause_ref := Undef; *) (* TODO: used for multiple unsat cores; check/fix this *) 
  let given_clause_ref = ref Undef in
  try
    begin
     
      solver_check is; (* can generate new unit clauses that can be used to simpl. given *)

     let given_clause = get_next_given_clause is in
     let given_clause_param = get_cl_param is given_clause in  

     given_clause_ref := Def(given_clause);    

(*     solver_check is; *) (* moving solver_check from above can lead to incompleteness due to dead given; inevstigate further  *)
     
     dbg D_given (lazy 
		    ((Clause.to_string given_clause)^" ln: "
                     ^(string_of_int (Clause.length given_clause))
                     ^" when born: "^(string_of_int (Clause.get_ps_when_born given_clause))));
     
     dbg_env D_given_param 
       (fun () -> 			
         Format.printf "@[%a @]@."
           (TstpProof.pp_clause_with_source_gs ~clausify_proof: false ) given_clause);
     
   
       dbg_env D_given_param 
       (fun () ->            
         Format.printf "@[%a @]@." 
             (Clause.pp_clause_params  Clause.param_out_list_all) given_clause;
       );
(*								
  Format.printf "@[%a @]@."
  (TstpProof.pp_clause_with_source_gs ~clausify_proof: false ) simplified_given_clause;
 *)		

(*
  Format.printf "@[%a @]@.@[%a @]@."
  (TstpProof.pp_clause_with_source_gs ~clausify_proof: false ) simplified_given_clause
  (Clause.pp_clause_params Clause.param_out_list_all) simplified_given_clause;
 *)	
	

       dbg_env D_given_filtered 
	 (fun () ->
	   let bc_imp_inh = (Clause.get_bc_imp_inh given_clause) in
	   let filter_cond = (bc_imp_inh !=  bc_imp_inh_default_val) in
	   if filter_cond
	   then
	     dbg D_given_filtered (lazy 			 
				     ("simpl clause: "
				      ^(Clause.to_string given_clause)
				      ^" bc_imp_inh "^(string_of_int bc_imp_inh)^" \n");
				  )
	 );

(*-----------------------------------------------*)
       all_instantiations is given_clause_param given_clause;
       add_to_active is given_clause_param given_clause;
(*-----------------------------------------------*)

    end 
  with
  | Unsatisfiable_gr ->

      dbg D_inst (lazy "Unsatisfiable_gr");
      (* put given clause back to the unprocessed *)
     
      (try
        (if !current_options.soft_assumptions
        then
          (
           process_soft_unsat is; 
           (match !given_clause_ref with 
           |Def(given_clause) ->
               add_to_passive is given_clause;
           |Undef -> 
               (
                dbg D_inst (lazy ("!given_clause_ref=Undef"));
               )
              (* failwith "inst_lazy_loop_body: !given_clause_ref is undefined" *)
    
           )
          )
        else
          raise Unsatisfiable_gr
        )
      with         
      |Unsatisfiable_gr -> (* without inst soft_assumptions*)
          (
           remove_soft_assumptions is (TSet.elements is.soft_assumptions);
       (*    Prop_solver_exchange.clear_soft_assumptions ();*)
           (if (val_of_override !current_options.bmc1_incremental) 
           then
             (Prop_solver_exchange.process_unsat_result ())
           else
             raise Unsatisfiable_gr
           )
          )
      |Unsatisfiable_gr_na -> 
          remove_soft_assumptions is (TSet.elements is.soft_assumptions);
          Prop_solver_exchange.clear_soft_assumptions ();
          raise Unsatisfiable_gr_na 
            
      )   
(* TODO: check that all clauses that all moves from passive to active are completed before the solver is called *)
(*
      (match !given_clause_ref with 
      |Def(given_clause) -> add_to_passive is given_clause
      |Undef -> 
          (
           if (val_of_override !current_options.bmc1_incremental) || !current_options.soft_assumptions
           then
             (failwith "inst_lazy_loop_body: !given_clause_ref is undefined")
          )
      );
      (* continue if necessary or throw an exception *)
      (if (val_of_override !current_options.bmc1_incremental) || !current_options.soft_assumptions
      then
        (Prop_solver_exchange.process_unsat_result ())
      )
*)
  | Unsatisfiable_gr_na -> 
      remove_soft_assumptions is (TSet.elements is.soft_assumptions);
      Prop_solver_exchange.clear_soft_assumptions ();
      raise Unsatisfiable_gr_na 
      

  | PassiveQueues.Passive_Empty ->
      (
       dbg D_inst (lazy "Passive_Empty");
       (
	if (is.inst_unprocessed = [])
	then
	  (
           dbg D_inst (lazy "Passive_Empty: is.inst_unprocessed=[]");
(*           assert(not ((Prop_solver_exchange.solve ()) = PropSolver.Unsat)); *)

           remove_soft_assumptions is (TSet.elements is.soft_assumptions);
           Prop_solver_exchange.clear_soft_assumptions ();
           (if (val_of_override !current_options.bmc1_incremental || !current_options.soft_assumptions)
           then
             (* if we are SAT but there were unsat cores there -- report *)
             (* can raise MultipleUnsat !unsat_cores *) 
             (Prop_solver_exchange.process_final_sat_result ();)
           );
           raise (Inst_satisfiable (get_pre_model is))
	  )
	else
          (
           reload_unprocessed is
          )
       )
      )
 
  | Given_Eliminated -> 
      (
       dbg D_inst (lazy "inst_lazy_loop_body: Given_Eliminated");      
      )
  | Activity_given_sel_changed ->
      (
       dbg D_inst (lazy "inst_lazy_loop_body: Activity_given_sel_changed");      
      )

  | x -> 
      (
       dbg D_inst (lazy ("inst_lazy_loop_body: uncaught exception: "^(Printexc.to_string x)));   
       raise x
      )

(*------------------------ Lazy Loop ---------------------*)
	
let rec instantiation_lazy_loop is =
  dbg D_trace (lazy "instantiation_lazy_loop");
  let stat_counter = ref 0 in
  let bound_iter = ref 0 in
  out_str !param_str_ref;
  while true do
    (* while !bound_iter < 10000 do*)
    (*    (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());*)
    inst_lazy_loop_body is;
    stat_counter := !stat_counter +1;
    bound_iter:=!bound_iter +1
  done
    
    (*------------------------Lerning Restart ------------------------*)
    (*
      let learning_restart input_clauses =
      clause_db_ref :=
      (ClauseAssignDB.create_name
      ("Instantiation_Clauses_DB"));
      clean_passive ();
      (* empty unif index *)
      unif_index_ref := (DiscrTreeM.create ());
      (* for all terms set in_unif_index to false  *)
      (* change later to terms in unif index only *)
      
      let f t =
      match t with
      | Term.Fun _ -> (Term.set_fun_bool_param false Term.inst_in_unif_index t)
      | _ -> ()
      in
      TermDB.iter f !term_db_ref;
      
      (* refresh the model *)
      
      (if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat)
      then raise Unsatisfiable);
      
      Prop_solver_exchange.clear_model ();
      
      unprocessed_ref := [];
      
      assign_int_stat 0 inst_num_in_active;
      (*   out_str("\n Learning Restart\n ");*)
      let add_cl clause =
      let new_clause =
      (Clause.normalise term_db_ref (Clause.create (Clause.get_literals clause)))
      in
      (*  let new_clause = Clause.normalise term_db_ref clause in *)
      let added_clause =
      ClauseAssignDB.add_ref new_clause clause_db_ref in
      add_clause_to_unprocessed added_clause;
      Clause.inherit_param_modif clause added_clause;
      Clause.inherit_bool_param Clause.in_prop_solver clause added_clause;
      Clause.assign_when_born 0 added_clause;
      
      (*debug*)
      (* out_str ((Clause.to_string added_clause)^"\n"^
	 (string_of_bool (Clause.get_bool_param Clause.in_prop_solver added_clause))^"\n");*)
      
      in
      List.iter add_cl input_clauses
      (* Memory is cleared separately by Lib.clear_mem ()*)
      
      (*  out_str "Major GC \n";*)
      (*  out_str "Major end  \n"*)
      (* out_str_debug ("Learning restart: "^(string_of_int !num_of_restarts)^"\n");*)
      (*      out_statistics ()*)
     *)
    
    (*------------------------End Lerning Restart----------------------*)
    
    (*----------------------Start Instantiation--------------------------*)
    
    (*
      let init_instantiation input_clauses =
      let add_input_to_unprocessed clause =
      let added_clause =
      (ClauseAssignDB.add_ref clause clause_db_ref) in
      Clause.set_bool_param true Clause.input_under_eq added_clause;
      (* for restarts we need to add input_under_eq for clauses ib init_clause_list*)
      Clause.set_bool_param true Clause.input_under_eq clause;
      Clause.assign_when_born 0 added_clause;
      add_clause_to_unprocessed added_clause
      in
      List.iter add_input_to_unprocessed input_clauses;
      (*  full_loop input_clauses;*)
      
     *)
    
(*-------------------*)
let inst_add_clause is clause =  
  dbg D_input (lazy ("inst_add_clause: "^(Clause.to_string clause)));
  is.inst_input_clauses <- BCSet.add clause is.inst_input_clauses;
(*
  out_str "dbg: instantiation_loop: Clause.assign_ps_when_born 0 clause;";
  Clause.assign_ps_when_born 0 clause;
*)
  process_new_clause is clause

let inst_add_clause_list is clause_list = 
  List.iter (inst_add_clause is) clause_list

(*
  let add_input_clause clause =  
  let copied_clause = Clause.copy_clause clause in
  let new_clause = context_add !context copied_clause in
  Clause.assign_is_dead false new_clause;
  Clause.assign_ps_when_born 0 new_clause;
  add_clause_to_unprocessed new_clause

  
  let add_clause clause = 
  input_clauses := clause::!input_clauses;
  add_input_clause clause
 *)

(*-------------------*)
(*
  let init_instantiation () =
  (* out_str "\n\n init instantiation\n\n"; *)

  List.iter add_input_clause !input_clauses
 *)      
    
(*-------------------*)
(*    let _ = init_instantiation () *)
    
    (*------------------Clears All---------------------------*)
(*        
          let clear_all () =
          
          (* out_str "\n\n clear_all instantiation \n\n"; *)
          (* a trick to keep old value of functional statistics*)
          (* like number of clauses and number in passive*)
          
          let num_in_passive = (get_val_stat_fun inst_num_in_passive) in
          assign_fun_stat
          (fun () -> num_in_passive)
          inst_num_in_passive;
          
          let num_of_clauses = (get_val_stat_fun inst_num_of_clauses) in
          assign_fun_stat
          (fun () -> num_of_clauses)
          inst_num_of_clauses;
          
          (* context_iter !context Clause.clear_clause; *)
          
          (* clear clause db *)
          inst_context_reset ();
          
          (* clear passive_queue *)
          finalise_passive ();
          
          (* empty unif index *)
          ClauseUnifIndex.clear !unif_index_ref;
          
          (* refresh the model *)
          Prop_solver_exchange.clear_model ()

 *)  
    
    (*---------------End--------------------------------*)
(* end *) (* Instantiation.Make *)

(*--------------Commented Part-----------------------*)

(*
(* it's better to simplify before splitting ... add later*)
  let simplify_input init_clause_list_ref =
(* need to add to solver before simplifying *)
  let add_to_prop_solver clause =
  add_clause_to_solver solver_sim solver grounding_term clause
  in List.iter add_to_prop_solver !init_clause_list_ref;
  let subs clause =
  let new_clause = prop_subsumption clause in
  if ground_splitting_input || ground_splitting_full
  then
  let split_result =
  (Splitting.ground_split_clause
  symbol_db_ref term_db_ref split_map_ref clause) in
  num_of_splits := !num_of_splits + (Splitting.get_num_of_splits split_result);
  Statistics.incr_int_stat (Splitting.get_num_of_splits split_result);
  num_of_split_atoms :=
  !num_of_split_atoms + (Splitting.get_num_of_split_atoms split_result);
  init_clause_list_ref:= Splitting.get_split_list split_result);
 *)

(*
  let simplify_input init_clause_list =
  let simplify_clause rest clause =
  try
  (prop_subsumption clause):: rest
  with
  Simplified_exists
  -> rest
  in
  List.fold_left simplify_clause [] init_clause_list
 *)

(*
  let start_instantiation ()
  try
(* signals:*)
  let signal_handler signal =
  if
  (
(*      signal = Sys.sigquit ||*)
(*	signal = Sys.sigvtalrm ||*)
  signal = Sys.sigint  (*||*)
(*	signal = Sys.sigalrm || 	*)
(*	signal = Sys.sigterm || *)
(*	signal = Sys.sigtstp *)
  )
  then
  (out_stat ();
  raise Termination_Signal)
  else failwith "Unkown Signal"
  in
(*    Sys.set_signal Sys.sigquit (Sys.Signal_handle signal_handler);*)
  Sys.set_signal Sys.sigint (Sys.Signal_handle signal_handler);
(*    Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigkill (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigalrm  (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigterm (Sys.Signal_handle signal_handler);*)
(*    Sys.set_signal Sys.sigtstp (Sys.Signal_handle signal_handler);*)

(*  lit_sel_fun_ref:=lit_sel_fun;*)

(*    let grounding_term = get_term_for_grounding  () in*)
(*    let grounding_term = bot_term in*)
(*  out_str_debug ("Term for grounding: "^(Term.to_string grounding_term)^"\n");*)
(*    let solver = PropSolver.create_solver () in*)
(* solver used for simplifications *)
(*    let solver_sim = PropSolver.create_solver () in*)
  let equality_axioms = Eq_axioms.axiom_list () in
  init_clause_list_ref:= equality_axioms@(!init_clause_list_ref);
(* (if (Symbol.is_input Symbol.symb_equality)
   then resolution_mult:= (!resolution_mult /10));*)

(* out_str_debug ("Equality Axioms:\n"
   ^(Clause.clause_list_to_string equality_axioms)^"\n"); *)
(* out_str_debug
   ("Init Clauses: \n"
   ^(Clause.clause_list_to_string !init_clause_list_ref)); *)
(* it's better to simplify before splitting ... add later*)
(*    simplify_input init_clause_list_ref;*)

(* out_str_debug
   ("After Split: \n"
   ^(Clause.clause_list_to_string !init_clause_list_ref));*)

(*----------add clause to prop solver------------*)
  List.iter
  Prop_solver_exchange.add_clause_to_solver !init_clause_list_ref;

  (if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat )
(*||
  (PropSolver.solve Prop_solver_exchange.solver_sim) = PropSolver.Unsat *)
  then raise Unsatisfiable
  else ());

(*-----------------should assign params before simplifying?------------*)
(*-------should be simplified_init later----------*)

  init_clause_list_ref:=
  simplify_input !init_clause_list_ref;

  let split_map_ref = ref (Splitting.create_split_map ()) in
  (match !current_options.ground_splitting with
  | Split_Input | Split_Full ->
  let split_result =
  (Splitting.ground_split_clause_list !init_clause_list_ref) in
  incr_int_stat
  (Splitting.get_num_of_splits split_result) num_of_splits;
  incr_int_stat
  (Splitting.get_num_of_split_atoms split_result) num_of_split_atoms;
  init_clause_list_ref:= Splitting.get_split_list split_result
  | _ -> ()
  );

  let add_input_to_unprocessed clause =
  let added_clause =
  (ClauseAssignDB.add_ref clause clause_db_ref) in
  Clause.set_bool_param true Clause.input_under_eq added_clause;
(* for restarts we need to add input_under_eq for clauses ib init_clause_list*)
  Clause.set_bool_param true Clause.input_under_eq clause;
  Clause.assign_when_born 0 added_clause;
  add_clause_to_unprocessed added_clause
  in
  List.iter add_input_to_unprocessed !init_clause_list_ref;
  full_loop ();

(*
  let add_cl_to_solver_and_unprocessed clause =
(* try
   let simplified_clause = simplify_new clause in *)
  (try
  add_clause_to_solver solver_sim solver grounding_term clause;
(* we have normalised clauses before, also normalisation will lose params*)
(* such as conj_dist *)
(*(Clause.normalise term_db_ref clause)*)
  let added_clause =
  (ClauseAssignDB.add_ref clause clause_db_ref) in
  Clause.set_bool_param true Clause.input_under_eq added_clause;
(* for restarts we need to add input_under_eq for clauses ib init_clause_list*)
  Clause.set_bool_param true Clause.input_under_eq clause;
  Clause.assign_when_born 0 added_clause;
  add_clause_to_unprocessed added_clause
(*out_str_debug ((Clause.to_string added_clause)^"\n")*)
  with PropImplied -> () )
(*  with New_Clause_Simplified -> ()   *)
  in
  List.iter add_cl_to_solver_and_unprocessed !init_clause_list_ref;
 *)

  with
  | Unsatisfiable | PropSolver.Unsatisfiable ->
  out_str "PROVED (by instnatiation)\n";
  out_stat ()
  | Satisfiable ->
  out_str "SATISFIABLE (by instnatiation)\n";
  out_stat ()
  | Discount.Unsatisfiable ->

(*      out_str "PROVED (by resolution)\n";*)
  out_stat ()

  | Discount.Satisfiable ->
  out_stat ()

 *)

(*out_str (test_sel ())*)

(*
  let start_instantiation () =
(* get term for grounding*)
  let num_of_symb = SymbolDB.size !symbol_db_ref in
  (if num_of_symb < !actual_num_of_symb_groups_ref
  then actual_num_of_symb_groups_ref := num_of_symb);
  partition_symbols !actual_num_of_symb_groups_ref;
  let add_clause clause =
  add_new_clause_to_passive clause clause
  in
  List.iter add_clause !init_clause_list_ref;
(* ClauseAssignDB.iter add_caluse !init_clause_db_ref; *)
(* out_str_debug "initial clauses are added to passive \n";*)
  try discount_loop () with
  | Unsatisfiable ->
  out_str "\n PROVED";
  out_statistics ()
  | Satisfiable ->
  out_str "\n SATISFIABLE";
  out_statistics ()

 *)

(* tests *)
(*
  let test_sel () =
  let truth_f term = true in
  let sel_lit clause =
  Selection.lit_neg_gr_shallow truth_f clause in
  let to_str rest clause =
  rest^"Clause: "^(Clause.to_string clause)^"\n"
  ^"Sel: "^(Term.to_string (sel_lit clause))^"\n" in
  List.fold_left to_str "" !init_clause_list_ref
 *)

(*
  end
 *)

(************ all_instantiations_sel with the selection: *)
(************ lit is sel if it has the least  number     *)
(************ of unif. compl lits in unif index          *)
(*
  let all_instantiations_sel solver_sim solver gr_by main_clause =
  try
  let accord lit =
  let var_entry = get_prop_gr_var_entry lit in
  change_model_solver solver var_entry in
  Clause.iter accord main_clause;
  let sel_cand_lits =
  Clause.find_all consistent_with_model main_clause in
(* returns list (lit, unif_cand_list_[] ) *)
  let lits_unif =
  let get_unif_cand lit =
  (lit, (DiscrTreeM.unif_candidates !unif_index_ref (add_compl_lit lit))) in
  List.map get_unif_cand sel_cand_lits
  in
  let comp_cand (l1, unif_list1) (l2, unif_list2) =
  - (compare (List.length unif_list1) (List.length unif_list2)) in
  let (sel_lit, unif_candidates) =
  Lib.list_find_max_element comp_cand lits_unif in
  Clause.assign_inst_sel_lit sel_lit main_clause;
  ass_if_consistent sel_lit main_clause;
  let compl_sel_lit = add_compl_lit sel_lit in
(*old part*)
  let for_all_candidates (lit, clause_list) =
(*out_str_debug ("inst_try: "^(Clause.to_string main_clause)*)
(*^(Clause.clause_list_to_string clause_list)); *)
  try
  (let var_entry = get_prop_gr_var_entry lit in
(*	if (model_accords_solver solver var_entry)
  then *)
  (
  let conclusion_list =
  Inference_rules.instantiation_norm dismatch_switch
  term_db_ref clause_db_ref main_clause sel_lit compl_sel_lit
  clause_list lit in
  let apply_to_concl clause =
(*try *)
(* uncomment this if back to  constraint checking then simplified *)
(* let simplified_clause = simplify clause in	 *)
  let simplified_clause = clause in
(* uncomment this if back to  constraint checking then simplified *)
(* let added_clause =
   ClauseAssignDB.add_ref clause clause_db_ref in *)
  let added_clause = clause in
  add_clause_to_solver solver_sim solver gr_by added_clause;
  add_clause_to_unprocessed added_clause
(* with Clause_Simplified -> ()*)
  in
  List.iter apply_to_concl conclusion_list
  )
(*	else ()*) (*  model_accords_solver will move all clauses to passive!*)
  )
  with Unif.Unification_failed -> ()
  in
  List.iter for_all_candidates unif_candidates
  with
  Clause.Inst_sel_lit_undef ->
  failwith "all_instantiations: clause should have selected literals here"

 *)
(************ end all_instantiations ********)

(**************** instantiation_exhaustive_loop *********************)
(* we exhaustivelly apply instantiations util passive is empty *)
(* then apply prop_solver *)
(*
  let rec instantiation_exhaustive_loop solver_sim solver gr_by =
  let stat_counter = ref 0 in
  while true do
(* out_str_debug
   ("instantiation_exhaustive_loop \n "
   ^(string_of_int !num_of_instantiation_loops));*)
  num_of_instantiation_loops := !num_of_instantiation_loops + 1;
  stat_counter := !stat_counter +1;
(* often output of statistic *)
(*  (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());*)
  try
(*  let clause = remove_from_simple_passive () in*)
  let clause = remove_from_passive () in
  if ((Clause.get_bool_param Clause.is_dead clause) ||
  (Clause.get_bool_param Clause.in_active clause))
  then ()
  else
(* sp for simple passive *)
  (selection_renew solver clause;
  all_instantiations solver_sim solver gr_by clause;
  add_to_active clause)
  with
  | Passive_Empty ->
  (if (PropSolver.solve solver) = PropSolver.Unsat
  then raise Unsatisfiable
  else
  try
  List.iter add_new_clause_to_passive !unprocessed_ref;
  unprocessed_ref:=[];
  apply_new_model solver;
  num_of_solver_calls := !num_of_solver_calls +1
(* out_str_debug (model_sel_to_string ())*)
  with
  Sel_Unchanged ->
  if (passive_is_empty ())
  then raise Satisfiable
  else())
  | PropSolver.Unsatisfiable -> raise Unsatisfiable
  done

 *)

(**************** instantiation loop with each clause added to passive *)
(******************solver called**************)
(* replace here simple passive to passive*)
(*
  let rec instantiation_each_loop solver_per_active solver_sim solver gr_by =
  let stat_counter = ref 0 in
  let solver_counter = ref 0 in
  while true do
(* out_str_debug
   ("instantiation_exhaustive_loop \n "
   ^(string_of_int !num_of_instantiation_loops));*)
  num_of_instantiation_loops := !num_of_instantiation_loops + 1;
  stat_counter := !stat_counter +1;
  solver_counter:=!solver_counter +1;
(* often output of statistic *)
(*  (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());*)

  try
(* test run solver every loop *)
(* if (PropSolver.solve solver) = PropSolver.Unsat
   then raise Unsatisfiable
   else *)
  (if ((!solver_counter > solver_per_active ) ||
  (passive_is_empty ()))
  then
  if (!unprocessed_ref = []) && (passive_is_empty ())
  then raise Satisfiable
  else
  (solver_counter:=0;
  if (PropSolver.solve solver) = PropSolver.Unsat
  then raise Unsatisfiable
  else
  (List.iter add_new_clause_to_passive !unprocessed_ref;
  unprocessed_ref:=[];
  try
  apply_new_model solver
  with
  Sel_Unchanged ->
  if (passive_is_empty ())
  then raise Satisfiable
  else()
  )
  )
  else
  let clause = remove_from_passive () in
  if ((Clause.get_bool_param Clause.is_dead clause) ||
  (Clause.get_bool_param Clause.in_active clause))
  then ()
  else
  (selection_renew solver clause;
  all_instantiations solver_sim solver gr_by clause;
  add_to_active clause)
  )
  with
  | Passive_Empty -> ()
  | PropSolver.Unsatisfiable -> raise Unsatisfiable
  done
 *)
(****************end instantiation_each_loop***************)

(***************instantiation lazy loop***********************)
(*we change model patially and lazily for literals detected having different *)
(* value in the solver vs in the model *)

(*
  let rec instantiation_lazy_loop solver_per_active solver gr_by =
  let stat_counter = ref 0 in
  let solver_counter = ref 0 in
  while true do
(* out_str_debug
   ("instantiation_exhaustive_loop \n "
   ^(string_of_int !num_of_instantiation_loops));*)
  num_of_instantiation_loops := !num_of_instantiation_loops + 1;
  stat_counter := !stat_counter +1; (* out statistic after some steps*)
  solver_counter:=!solver_counter +1;
(* often output of statistic *)
  (if !stat_counter > 1000 then (stat_counter:=0; out_statistics ()) else ());
  try
  (if !solver_counter > solver_per_active
  then
  (num_of_solver_calls := !num_of_solver_calls +1;
  if (PropSolver.solve solver) = PropSolver.Unsat
  then raise Unsatisfiable
  else solver_counter:=0));
  let clause = remove_from_passive () in
  if
  ((Clause.get_bool_param Clause.is_dead clause) ||
  (Clause.get_bool_param Clause.in_active clause))
  then ()
  else
  ((*out_str_debug ("Given Clause: "^(Clause.to_string clause)^"\n");*)
  selection_renew solver clause;
(* out_str_debug ("Sel in Given: "^ *)
(*		(Term.to_string (Clause.get_inst_sel_lit clause)^"\n"));*)
(* out_str_debug (model_sel_to_string solver); *)
  all_instantiations solver_sim solver gr_by clause;
  add_to_active clause)
  with
  | Passive_Empty ->
  ( num_of_solver_calls := !num_of_solver_calls +1;
  if (PropSolver.solve solver) = PropSolver.Unsat
  then raise Unsatisfiable
  else
  try
  List.iter add_new_clause_to_passive !unprocessed_ref;
  unprocessed_ref:=[];
  num_in_unprocessed:=0;
  apply_new_model solver;
  num_of_solver_calls := !num_of_solver_calls +1
(* out_str_debug (model_sel_to_string ())*)
  with
  Sel_Unchanged ->
  (if (*!simple_passive_ref =[] *)
  !passive_queue_ref = PassQueue.empty
  then ((*out_str_debug (model_sel_to_string solver); *)
  raise Satisfiable)
  else())
  )
  | PropSolver.Unsatisfiable -> raise Unsatisfiable
  done
 *)

(*let ()= add_param_str "all_instantiations_sel\n"*)

(*
  let return_solver_state solver =
  let apply_entry var_entry =
  let prop_var = get_prop_var_var_entry var_entry in
  let prop_neg_var = get_prop_neg_var_var_entry var_entry in
  match var_entry.truth_val with
  | Def(PropSolver.True) ->
  let _ = PropSolver.solve_assumptions solver [prop_var] in ()
  | Def(PropSolver.False) ->
  let _ = PropSolver.solve_assumptions solver [prop_neg_var] in ()
  | _ -> ()
  in
  TableArray.iter apply_entry var_table
 *)

(* auxilary *)
(* nonsense
   let rec check_same_sel_desc clause desc_clause =
   if ((Clause.get_bool_param Clause.in_active desc_clause)
   & ((Clause.compare_sel_place clause desc_clause) = 0))
   then
   (out_str ("parent: "^(Clause.to_string desc_clause)
   ^"Sel: "^(Term.to_string (Clause.get_inst_sel_lit desc_clause))^"\n");
   true)
   else
   false
   let parent = Clause.get_parent desc_clause in
   match parent with
   | Def(p) -> check_same_sel_desc clause p
   | Undef -> false

   let check_parent_same_sel clause =
   let parent = Clause.get_parent clause in
   match parent with
   | Def(p) -> check_same_sel_desc clause p
   | Undef -> false
 *)
