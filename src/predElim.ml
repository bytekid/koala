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
open Simplify


(*----- debug modifiable part-----*)

let dbg_flag = false
    
type dbg_gr = 
  |D_cycle
  |D_cycle_check
  |D_add_to_elim_pred_set
  |D_remove_from_protected
  |D_add_new_clause_to_pe_state
  |D_remove_clause_from_pred_to_elim
  |D_remove_clause
      
  |D_res_prop
  |D_res_basic
  |D_res_lifted
      
  |D_lcl_bwd_ss
  |D_lcl_bwd_subs
  |D_lcl_bwd_subs_res
      
  |D_glb_bwd_ss
  |D_glb_bwd_subs
  |D_glb_bwd_subs_res
  |D_pe_process_concl
      
  |D_iterate_inf
  |D_single_pred_elim
      
let dbg_gr_to_str = function 
  |D_cycle -> "cycle"
  |D_cycle_check -> "cycle_check"
  |D_add_to_elim_pred_set -> "add_to_elim_pred_set"
  |D_remove_from_protected -> "remove_from_protected"	
  |D_add_new_clause_to_pe_state -> "add_new_clause_to_pe_state"
  |D_remove_clause_from_pred_to_elim -> "remove_clause_from_pred_to_elim"
  |D_remove_clause -> "remove_clause"
  |D_res_prop -> "res_prop"
  |D_res_basic -> "res_basic"
  |D_res_lifted -> "res_lifted"
        
  |D_lcl_bwd_ss -> "lcl_bwd_ss"
  |D_lcl_bwd_subs -> "lcl_bwd_sub"
  |D_lcl_bwd_subs_res -> "lcl_bwd_subs_res"
        
  |D_glb_bwd_ss -> "glb_bwd_ss"
  |D_glb_bwd_subs -> "glb_bwd_subs"
  |D_glb_bwd_subs_res -> "glb_bwd_subs_res"
        
  |D_pe_process_concl -> "pe_process_concl"
  |D_iterate_inf -> "iterate_inf"
        
  |D_single_pred_elim -> "single_pred_elim"
	
        
let dbg_groups =
  [
   
   D_cycle;
   D_cycle_check;
   D_add_to_elim_pred_set;
   D_remove_from_protected;
   D_add_new_clause_to_pe_state;
   D_remove_clause_from_pred_to_elim;
   D_remove_clause;
   
    D_res_prop;
    D_res_basic;
    D_res_lifted; 
   
   (* D_lcl_bwd_ss; *)
   (* D_lcl_bwd_subs; *)
   (* D_lcl_bwd_subs_res; *)
   
   (* D_glb_bwd_ss; *)
   (* D_glb_bwd_subs; *)
   (* D_glb_bwd_subs_res; *)

    D_pe_process_concl;  
   
    D_iterate_inf;  
    D_single_pred_elim; 
   
   D_cycle;  
   D_single_pred_elim;  

 ]
    
let module_name = "pred_elim"
    
(*----- debug fixed part --------*)
    
let () = dbg_flag_msg dbg_flag module_name
    
let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy
    
let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)
    
(*----------------- elimination queue -----------------------------*)
    
exception PE_timeout

module PQS = Priority_queue.MakePQInt (Symbol.Key) (* symbol elimination queue *)
type elimination_queue = PQS.t


(*----------- priority based on estimated number of lits  after elimination ------------*)

type cl_size_to_num_cl = int IntMap.t (* maps number of lits in a clause -> number of such clauses  *)
      
let fill_cl_size_to_num bcset = 
  let f c rest = 
    let num_lits = Clause.length c in 
    let new_num_cl = 
      try 
        let num_cl = IntMap.find num_lits rest in 
        num_cl + 1          
      with 
        Not_found -> 1
    in
    IntMap.add num_lits new_num_cl rest
  in
  BCSet.fold f bcset IntMap.empty

let estimate_elim_num_lits bcset1 bcset2 = 
  let size_to_num1 = fill_cl_size_to_num bcset1 in 
  let size_to_num2 = fill_cl_size_to_num bcset2 in 

  let f size1 num1 estim1 = 
    let g size2 num2 estim2 =
      (size1 + size2 -2)*num1*num2 + estim2 
    in
    IntMap.fold g size_to_num2 estim1
  in 
  IntMap.fold f size_to_num1 0



(*---------------------------------------*)

type pe_options = 
    {
     pe_has_eq : bool; 
     
     (* pe_has_eq can be true even if input does not contain equality explicitly, since it can be added by later operations *)
     
     mutable pe_estim_num_of_lits : int; 
     (* do not eliminate symbol if the number of potential resulting clauses is greater than  pe_estim_num_of_cl *)
     
     
     mutable pe_conclusion_limit_test : clause -> bool; 
       (* do not eliminate symbol if (pe_conclusion_limit_test concl) is false *)
       
       mutable pe_preprocess_conclusion_extern : clause -> clause; (* preprocess conclusion, used in qbf *)
         
(*     pe_keep_elim :   num_cl_before:int -> num_cl_after:int -> bool; *)
         
         pe_keep_elim :  elim_symb: symbol -> clauses_before_elim: clause list -> clauses_after_elim: clause list -> bool;
(* num_lit_before:int -> num_lit_after:int -> num_cl_before:int -> num_cl_after:int -> bool;  *)
           
(* if  pe_keep_elim is true we keep elimination of the predicate otherwise abort it *)
(* based on the number of clauses before elimination and after elimination *)
           
           pe_elim_order_cmp_fun : context -> (symbol -> symbol -> int); 
             
	     (* based on current context compare function on symbols; elimination from smaller to larger, currently static *)
             
	     pe_elimination_set : SSet.t ; 
(*  predicates for elimination *)
             
             
(* one can exclude symbols that should not be eliminated: *)
             
(* hepler function:  get_most_preds_to_eliminate  below can be used  *)
(* for generating elimination set consisiting of most symbols in the input minus specisal symbols *)
(* such as  e.g. equality, verification symbols; *)
(* some other symbols that should not be eliminated like input/output of aiger should be remove by hand *)        
             
             pe_time_limit : float; (* time limit if <=0. then unlimited *)
             
(*------- simplifications ---------*)
             
	     (* Options.res_subs_type: type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int *)
	     (* for backward simplifications we can restrict length of the given clause *)
	     (* subset subsumtion is implicitly on in both directions *)
             
	     prop_glb_subs : bool; (* prop global subsumption*)
             
(* limit on clause to clause subsumptions *)
	     subs_cl_to_cl_limit : int;
             
(* local *) 
             
             lcl_add_to_sub_index_test : clause -> bool;
	       lcl_fwd_subs : bool;
	       lcl_fwd_subs_res : bool;
	       
	       lcl_bwd_subs : Options.res_subs_type; 
	       lcl_bwd_subs_res : Options.res_subs_type; 
               
(* global *)
               glb_add_to_sub_index_test : clause -> bool;
	         glb_fwd_subs : bool;
	         glb_fwd_subs_res : bool;
	         
	         glb_bwd_subs : Options.res_subs_type; 
	         glb_bwd_subs_res : Options.res_subs_type; 
   }
      
      
type elim_clauses = 
    {
     mutable elim_cl_pos : BCSet.t; 
     mutable elim_cl_neg : BCSet.t
   }
      
type pred_to_elim_clauses = elim_clauses SMap.t
      
      
(*------------------------------------- *)
type pe_state = 
    {
     
     mutable pe_opt : pe_options;
     
     pe_global_sim_state :  sim_state;
     (* pe_global_sim_state contains clauses from the input that are getting simplified during elimination *)
     (* the result of the pred_elim will be non-dead clauses in main_sim_state *)
     (* invariant: at any moment non-dead clauses in pe_global_sim_state are equi-sat to input clauses *)
     
     mutable pe_clauses : BCSet.t;
     
     mutable pe_local_sim_state : sim_state option; 
     (* local sim_state which is refreshed with each pred. elimination *)
     
     mutable pe_elimination_queue : elimination_queue;
     
     
     mutable pe_pred_to_elim_clauses : pred_to_elim_clauses; 
     
     (* pred_to_clauses is a map: pred -> elim_clauses *)
     (* where for each pred, elim_clauses consists of all clauses which are  *)
     (* pred-eligible for elimination;  *)
     (* clause is pred-eligible for elim. if this pred occurs only once in the clause  *)
     (* (other preds can have any number of occurences);  *)
     (* if a pred occurs more than once in a clause then this clause is in the pe_protected under this pred *)
     
     (* clauses in pred_to_clauses are from pe_global_sim_state and indexed by basic_clause *)  
     
     mutable pe_protected : BCSet.t SMap.t; 
     
     (* pred -> clause_set  symbols that have double occurences in clauses  *)
     (* pe_protected can be moved to pe_re_try if all clauses in the pred got removed *)
     
     (* assertion: all predicates are either in pe_pred_to_elim_clauses \cup pe_protected \cup aborted or in eliminated_pred_set *)
     
     mutable pe_aborted : SSet.t; 
     (* elimination of these preds was aborted due to exeeding some limits *)
     (* pe_aborted can be moved to re_try *)
     
     mutable pe_re_try : SSet.t; 
     (* set of preds that where either at some point aborted or protected but due to changes in pred_to_clauses *)
     (* they are moved to pe_re_try and can be retried again *)
     (* invariant: pe_aborted and pe_re_try are disjoint  *)
     
     mutable eliminated_pred_set : SSet.t; 
     
(* predicates which where affected by current single elimination *)
     mutable pe_currently_affected_preds : SSet.t;
     
(* statistics *)
     mutable pe_start_time : float;
     mutable pe_stat_num_elim : int;
     mutable pe_stat_cycle_num : int;
     mutable pe_stat_report_bound : int; (* we report only exp increments *)
     mutable pe_stat_report_next_start_time : float; (* also exp synchronised with pe_stat_report_bound *)
   }
      
(*------------*)      
let check_time pe_state =
  if (pe_state.pe_opt.pe_time_limit > 0.) 
  then 
    (
     let curr_time =  Unix.gettimeofday () in
     if ((curr_time -. pe_state.pe_start_time) > pe_state.pe_opt.pe_time_limit)
     then 
       (raise PE_timeout)
    )
      
(*---------------*)
let get_local pe_state = 
  match pe_state.pe_local_sim_state with 
  |Some ls -> ls
  |None -> failwith ("get_local local state is not defined ")
        
let glb_is_dead pe_state clause=
  Simplify.sim_is_dead pe_state.pe_global_sim_state clause
    
let lcl_is_dead pe_state clause=
  Simplify.sim_is_dead (get_local pe_state) clause
    
(*---------------------------*)
    
let pred_in_elim_set pe_state pred =  
  SSet.mem pred pe_state.pe_opt.pe_elimination_set
    
let pred_in_protectd pe_state pred = 
  SMap.mem pred pe_state.pe_protected 
    
let pred_in_aborted pe_state pred =
  SSet.mem pred pe_state.pe_aborted
    
let pred_in_affected pe_state pred =
  SSet.mem pred pe_state.pe_currently_affected_preds
    
let pred_in_eliminated pe_state pred = 
  SSet.mem pred pe_state.eliminated_pred_set
    
(*
  let pred_in_re_try pe_state pred = 
  SSet.mem pred pe_state.pe_re_try
 *)
    
(*-------------------------------------------*)
(*
  let stat_pred_elim_report_bound = ref 1
  let stat_pred_elim_report_next_start_time = ref 0.
 *)
    
let stat_incr_pred_elim pe_state =
  Statistics.incr_int_stat 1 Statistics.pred_elim; 
  pe_state.pe_stat_num_elim <- pe_state.pe_stat_num_elim +1;
  
  let num_elim = pe_state.pe_stat_num_elim in 
(*Statistics.get_val_stat  Statistics.pred_elim in*)
  if (num_elim >= pe_state.pe_stat_report_bound)
  then
    (
     let end_time = Unix.gettimeofday () in
     let time = truncate (end_time -. pe_state.pe_stat_report_next_start_time) in

     pe_state.pe_stat_report_next_start_time <- end_time;
     
     print_string  (" pe:"^(string_of_int num_elim)^":"^(string_of_int time)^"s");
     if dbg_flag then (out_str " ";); (*new line*)
     pe_state.pe_stat_report_bound  <- 2 * (pe_state.pe_stat_report_bound);
     flush stdout;
    )
  else ()
      
(*----------------------------------------*)
let add_to_eliminated_pred_set pe_state pred = 
  (if (SSet.mem pred pe_state.eliminated_pred_set) 
  then 
    (
     dbg D_add_to_elim_pred_set 
       (lazy ("warning: "^(Symbol.to_string pred)^" was already eliminated"));
    )
  );
  dbg D_add_to_elim_pred_set (lazy (Symbol.to_string pred));
  stat_incr_pred_elim pe_state;
  pe_state.eliminated_pred_set <- SSet.add pred pe_state.eliminated_pred_set;
  pe_state.pe_aborted <- SSet.remove pred pe_state.pe_aborted;
  pe_state.pe_currently_affected_preds <- SSet.remove pred pe_state.pe_currently_affected_preds
      
(*  pe_state.pe_re_try <- SSet.remove pred pe_state.pe_re_try *)
      
(*----------------------------------------*)
(*  returns ((pos_set,neg_set),mult_set) *)
(* where preds in pos_set, neg_set are single occurrence in the clause and mult with multiple occurrences *)
(* todo: hash into map not to recompute every time *)
      
let get_single_mult_preds pe_state clause = 
  let f ((pos_set,neg_set), mult_set) sign pred = 
    if (not (pred_in_elim_set pe_state pred))  ||  (SSet.mem pred mult_set) 
    then (* skip *)
      ((pos_set,neg_set), mult_set)
    else
      if (SSet.mem pred pos_set) 
      then 
        let new_mult_set = SSet.add pred mult_set in
        let new_pos_set =  SSet.remove pred pos_set in
        ((new_pos_set,neg_set), new_mult_set)
      else
        if (SSet.mem pred neg_set) 
        then 
          let new_mult_set = SSet.add pred mult_set in
          let new_neg_set =  SSet.remove pred neg_set in
          ((pos_set,new_neg_set), new_mult_set)
        else
	  if sign (* positive *)
	  then
            let new_pos_set =  SSet.add pred pos_set in
            ((new_pos_set,neg_set), mult_set)
	  else (* sing neg *)
            let new_neg_set =  SSet.add pred neg_set in
            ((pos_set,new_neg_set), mult_set)
  in
  Clause.fold_pred f ((SSet.empty,SSet.empty),SSet.empty)  clause

(*----------------------*)
let add_to_protected pe_state clause pred = 
  let new_cl_set = 
    try 
      let cl_set =  SMap.find pred pe_state.pe_protected in
      BCSet.add clause cl_set      
    with 
      Not_found ->
	BCSet.add clause BCSet.empty
  in
(*  pe_state.pe_aborted <- SSet.remove pred pe_state.pe_aborted; *)
  pe_state.pe_protected <- SMap.add pred new_cl_set pe_state.pe_protected  
      
      
let add_to_affected pe_state pred = 
  pe_state.pe_currently_affected_preds <- SSet.add pred pe_state.pe_currently_affected_preds 
      
      
let add_to_affected pe_state pos_set neg_set mult_set = 
  SSet.iter (add_to_affected pe_state) pos_set;
  SSet.iter (add_to_affected pe_state) neg_set;
  SSet.iter (add_to_affected pe_state) mult_set
    
(*
  let move_aborted_to_re_try pe_state pred = 
  (if (not (SSet.mem pred pe_state.eliminated_pred_set)) && 
(*    (pred_in_elim_set pe_state pred)*)
  (SSet.mem pred pe_state.pe_aborted) 
  then
  (
  pe_state.pe_aborted <- SSet.remove pred pe_state.pe_aborted;
  pe_state.pe_re_try <- SSet.add pred pe_state.pe_re_try)
  )
 *)
    
    
(* removes clause from protected and in case a predicate get removed from protected it is added to pe_re_try *)    
(* also move preds that become unprotected from aborted to re-try *)
    
(* when removing a clause; other clauses may be in waiting for adding *)
(* therefore we can not add pred to eliminated *)
let remove_from_protected pe_state mult_set clause = 
(*
  let ((_pos_set,_neg_set), mult_set) = get_single_mult_preds pe_state clause in
 *)
  let f pred =  
    try 
      let cl_set =  SMap.find pred pe_state.pe_protected in
      let new_cl_set = BCSet.remove clause cl_set in 
      if (BCSet.is_empty new_cl_set) 
      then 
        (
(*
  if (not (SMap.mem pred pe_state.pe_pred_to_elim_clauses)) 
  then (* pred got implicitely eliminated *)
  (
  dbg D_remove_from_protected (lazy (("pred got eliminated: ")^(Symbol.to_string pred)));
  add_to_eliminated_pred_set pe_state pred;	      
  )
  else
 *)
         begin
	   dbg D_remove_from_protected (lazy (("add to re_try: ")^(Symbol.to_string pred)));
	   pe_state.pe_protected <- SMap.remove pred pe_state.pe_protected;
(*	     move_aborted_to_re_try pe_state pred; *)
         end
        )
      else
        (
         pe_state.pe_protected <- SMap.add pred new_cl_set pe_state.pe_protected
        )
    with 
      Not_found -> 
	(
	 dbg D_remove_from_protected (lazy ("warning: removing clause "^(Clause.to_string clause)
					    ^" from protected but "^(Symbol.to_string pred)^" is not there"));
	)
  in
  SSet.iter f mult_set
    

(* TODO: for backward subsumed add remove from protected *)
    
(*----------------------------------------*)    
let add_to_pred_to_elim_clauses pe_state clause ~sign pred  = 
  let elim_clauses =
    try 
      SMap.find pred pe_state.pe_pred_to_elim_clauses 
    with
      Not_found -> 
	{
	 elim_cl_pos = BCSet.empty;
	 elim_cl_neg = BCSet.empty;
       }
  in
  (if sign then 
    elim_clauses.elim_cl_pos  <- BCSet.add clause elim_clauses.elim_cl_pos
  else
    elim_clauses.elim_cl_neg <- BCSet.add clause elim_clauses.elim_cl_neg
  );
  pe_state.pe_pred_to_elim_clauses <- SMap.add pred elim_clauses pe_state.pe_pred_to_elim_clauses
      
      
      
(*
  let remove_from_protected pe_state clause = 
 *)
      
(*
  let eligible_for_elim pe_state pred = 
  (not (SSet.mem pred pe_state.pe_protected)) && (SSet.mem pred pe_state.pe_opt.pe_elimination_set)
 *)
      
      
(* when removing a clause; other clauses may be in waiting for adding *)
(* therefore we can not add pred to eliminated *)
(*----------------------------*)
let remove_clause_from_pred_to_elim_clauses pe_state ~pos_set ~neg_set clause = 
  let f sign pred = 
    try 
(*
  (if (not (pred_in_protectd pe_state pred))
  then 
  move_aborted_to_re_try pe_state pred;
  );
 *)
      let elim_clauses = SMap.find pred pe_state.pe_pred_to_elim_clauses in
      (if sign 
      then 
        (elim_clauses.elim_cl_pos <- BCSet.remove clause elim_clauses.elim_cl_pos;)
      else
        (elim_clauses.elim_cl_neg <- BCSet.remove clause elim_clauses.elim_cl_neg;)
      );
      (if ((BCSet.is_empty elim_clauses.elim_cl_pos) && (BCSet.is_empty elim_clauses.elim_cl_neg) )
      then
        (	 
	   pe_state.pe_pred_to_elim_clauses <- SMap.remove pred pe_state.pe_pred_to_elim_clauses;
(*
  (if (not (SMap.mem pred pe_state.pe_protected)) 
  then (* pred got implicitely eliminated *)
  (
  dbg D_remove_clause_from_pred_to_elim (lazy (("pred got eliminated: ")
  ^(Symbol.to_string pred)));
  add_to_eliminated_pred_set pe_state pred;	      
  )
  )
 *)
	  )
      else
        ()
      )
    with 
      Not_found -> ()
  in
  SSet.iter (f true) pos_set;
  SSet.iter (f false) neg_set
    
let remove_clause_from_global pe_state clause = 
  Simplify.remove_from_indexes_and_context pe_state.pe_global_sim_state clause;
  pe_state.pe_clauses <- BCSet.remove clause pe_state.pe_clauses
      
      
(*---- main removing -------*)
let remove_clause pe_state clause = 
  if (BCSet.mem clause pe_state.pe_clauses)
  then
    begin
      dbg D_remove_clause (lazy (Clause.to_string clause));
      let ((pos_set,neg_set), mult_set) = get_single_mult_preds pe_state clause in
      remove_from_protected pe_state mult_set clause;  
      remove_clause_from_pred_to_elim_clauses pe_state ~pos_set ~neg_set clause;
      add_to_affected pe_state pos_set neg_set mult_set;
      remove_clause_from_global pe_state clause
    end
  else 
    ()
      
(*----------------------------*)
(* input clause is copied and sim_global version is used in pred_to_clauses *)
      
let add_new_clause_to_pe_state pe_state input_clause =   
  if (Simplify.sim_is_dead pe_state.pe_global_sim_state input_clause) 
  then 
    (dbg  D_add_new_clause_to_pe_state (lazy (" input_clause is dead: "^(Clause.to_string input_clause)));
     (*  can not remove since in the context a copy might be not dead *)
    )
  else
(* we cannot ignore if clause is already in sim_state because it can be added automatically after simplification *)
(* but we also need to add it to pred_to_elim_clauses/protected *)
(*
  if sim_mem_bclause pe_state.pe_global_sim_state input_clause 
  then 
  ()
  else
 *)
    begin
      let (clause, ss_subsumed) = sim_add_clause pe_state.pe_global_sim_state input_clause in
      List.iter (remove_clause pe_state) ss_subsumed;
      
      check_empty_clause clause;
      dbg D_add_new_clause_to_pe_state (lazy (Clause.to_string clause));
      if (Simplify.sim_is_dead pe_state.pe_global_sim_state clause)
      then 
        (dbg D_add_new_clause_to_pe_state (lazy ("is dead: "^(Clause.to_string clause)));
	 remove_clause pe_state clause)
      else
        if (not (BCSet.mem clause pe_state.pe_clauses))
        then 
          begin
            pe_state.pe_clauses <- BCSet.add clause pe_state.pe_clauses;
            let ((pos_set,neg_set), mult_set) = get_single_mult_preds pe_state clause in
	    SSet.iter (add_to_protected pe_state clause) mult_set;               
	    SSet.iter (add_to_pred_to_elim_clauses pe_state clause ~sign:true) pos_set;
	    SSet.iter (add_to_pred_to_elim_clauses pe_state clause ~sign:false) neg_set;
            add_to_affected pe_state pos_set neg_set mult_set;
          end
    end
      
(*----- simplification options -------*)
      
let sim_global_opt pe_options = 
  {
(*   sim_copy_clauses = true; *)
   sim_add_to_prop_solver = 
   if pe_options.prop_glb_subs 
   then 
     true
   else
     false;
   
   sim_use_ss_index = true;
   sim_use_sub_index = true;
   sim_add_to_sub_index_test = pe_options.glb_add_to_sub_index_test
 }
    
let sim_local_opt pe_options = 
  {
(*   sim_copy_clauses = true; *)
   
   sim_add_to_prop_solver = 
   (if pe_options.prop_glb_subs 
   then 
     true
   else
     false);
   
   sim_use_ss_index = true;
   sim_use_sub_index = true;
   sim_add_to_sub_index_test = pe_options.lcl_add_to_sub_index_test
 }
    
(*---------------------------------------------*)
let get_elim_clauses_size elim_clauses = 
  let num_cl_pos = BCSet.cardinal elim_clauses.elim_cl_pos in
  let num_cl_neg = BCSet.cardinal elim_clauses.elim_cl_neg in
  num_cl_pos + num_cl_neg  
    
let get_elim_clauses_concl_estimated_size elim_clauses = 
  let num_cl_pos = BCSet.cardinal elim_clauses.elim_cl_pos in
  let num_cl_neg = BCSet.cardinal elim_clauses.elim_cl_neg in
  num_cl_pos * num_cl_neg  
    

let get_concl_estimated_size pe_state pred = 
  try 
    let elim_clauses = SMap.find pred pe_state.pe_pred_to_elim_clauses in
    get_elim_clauses_concl_estimated_size elim_clauses
  with 
    Not_found -> 0
        
let get_num_of_list_cl_bset cl_bset = 
  let f c n = (Clause.length c) + n in
  BCSet.fold f cl_bset 0

let get_elim_num_of_lits elim_clauses= 
  let num_lits_pos = get_num_of_list_cl_bset elim_clauses.elim_cl_pos in
  let num_lits_neg = get_num_of_list_cl_bset elim_clauses.elim_cl_neg in
  num_lits_pos + num_lits_neg

(*---------------------------------------------*)
let compute_pred_elim_priority pe_state pred = 
  let estim_num_of_cl = get_concl_estimated_size pe_state pred in 
  if (estim_num_of_cl > 
      pe_state.pe_opt.pe_estim_num_of_lits)
  then
    estim_num_of_cl
  else
    begin
      try       
        let elim_clauses = SMap.find pred pe_state.pe_pred_to_elim_clauses in 
        estimate_elim_num_lits elim_clauses.elim_cl_pos elim_clauses.elim_cl_neg 
      with 
        Not_found -> 0
    end
      
(*---------------------------------------------*)
      
(* input is of type context_list *)
(*---------main create------------*)
let pe_create_state pe_options input =
(*  let input_size = cl_size input in *)
  let pe_state = 
    {
     pe_opt = pe_options;    
     pe_global_sim_state = Simplify.sim_create (sim_global_opt pe_options); 
     pe_clauses = BCSet.empty;
     pe_local_sim_state = None; (*sim_create sim_local_opt 23;*) (* local will be reassigned anyway *)
     
     pe_elimination_queue = PQS.create ();
     
     
     pe_pred_to_elim_clauses = SMap.empty;
     pe_protected = SMap.empty; (* pe_options.input_protected; *)
     pe_aborted = SSet.empty;
     pe_re_try = pe_options.pe_elimination_set;     
     eliminated_pred_set = SSet.empty;
     pe_currently_affected_preds = SSet.empty;
     
(* statistics *)
     pe_start_time = Unix.gettimeofday ();
     pe_stat_num_elim = 0;
     pe_stat_cycle_num = 1;
     pe_stat_report_bound = 1; (* we report only exp increments *)
     pe_stat_report_next_start_time = Unix.gettimeofday ();
   }
  in
  let add_clause clause = 
(*    let feature_list = get_feature_list clause in     *)
    add_new_clause_to_pe_state pe_state clause
  in
  cl_iter add_clause input;

  pe_state.pe_currently_affected_preds <- pe_state.pe_opt.pe_elimination_set;

(*
  let fill_elim_queue pe_state = 
  let f pred = 
  let prt = compute_pred_elim_priority pe_state pred in 
  pe_state.pe_elimination_queue <- eq_add_pred pe_state.pe_elimination_queue prt pred
  in
  SSet.iter f pe_state.pe_opt.elimination_set
  in
  fill_elim_queue pe_state;
 *)
(* fill_protected/ remove pred with double occurrences  in clauses *)
  pe_state
    

let pe_create_state_fom_context pe_options input_context = 
  pe_create_state pe_options (Clause.CL_Context (input_context))
    
let pe_create_state_from_list pe_options input_list = 
  pe_create_state pe_options (Clause.CL_List (input_list))
    
    
    
    
let clear_local pe_state = 
  pe_state.pe_local_sim_state <- None
      
      
(*--- resolution move to inference --------*)
      
      
(*----------------------------*)
      
let resolution_prop (l1, c1, rest_lits1) (l2, c2, rest_lits2) = 
  assert ((Term.get_atom l1) == (Term.get_atom l2));
  let tstp_source = Clause.tstp_source_resolution [c1;c2] [l1;l2] in    
  let conclusion = create_clause tstp_source (rest_lits1@rest_lits2) in       
(* debug *)
  dbg D_res_prop (lazy ("resolution_prop: "^(Clause.to_string c1)^" "^(Clause.to_string c2)));
  dbg D_res_prop (lazy ("concl: "^(Clause.to_string conclusion)));

(* debug *) 
  conclusion
    
(*----------------------------*)
let resolution_basic mgu (l1, c1, rest_lits1) (l2, c2, rest_lits2) = 
  let tstp_source = Clause.tstp_source_resolution [c1;c2] [l1;l2] in    
  let conclusion = 
    create_clause tstp_source 
      (normalise_blitlist_list 
         mgu [(1,rest_lits1);(2,rest_lits2)])     
  in
(* debug *)
  dbg D_res_basic (lazy ("resolution_basic: "^(Clause.to_string c1)^" "^(Clause.to_string c2)));
  dbg D_res_basic (lazy ("concl: "^(Clause.to_string conclusion)));
(* debug *)
  conclusion
    

(* lifted resolution: P(t1,..,tn)\/ C  ~P(s1,..,sn)  \/D |- t1 != s1 \/..\/ t_n != s_n \/ C \/ D *)
(* for good results should be followed by unflattening *)

(*----------------------------*)
let resolution_lifted (l1, c1, rest_lits1 ) (l2_to_rename, c2, rest_lits2_to_rename) =
  (* we first need to rename l2 and rest_lits2 away from lits in c1 *)
  let v1_set = List.fold_left Term.add_var_set VSet.empty (l1::rest_lits1) in
  let away_vars = VSet.elements v1_set in 
  let (fresh_vars_env, init_rename_subst) = Subst.rename_term_init away_vars in 
  let (l2_rename_subst,l2) = Subst.rename_term_env term_db_ref fresh_vars_env init_rename_subst l2_to_rename in
  let (_rename_subst,  rest_lits2) = 
    Subst.rename_term_list_env term_db_ref fresh_vars_env l2_rename_subst rest_lits2_to_rename in

  let atom1 = Term.get_atom l1 in 
  let atom2 = Term.get_atom l2 in 
  let pred = Term.get_top_symb atom1 in
  assert (pred == (Term.get_top_symb atom2) && (not ((Term.is_neg_lit l1) == (Term.is_neg_lit l2))));
  let tstp_source = Clause.tstp_source_resolution_lifted [c1;c2] [l1;l2] in    
  let conclusion =
    match (Symbol.get_stype_args_val pred) with
    | Def (type_args, type_value) ->
        if type_args = []
        then
	  (* P is propositional *)
	  create_clause tstp_source (rest_lits1@rest_lits2) 	 
        else				
          let rec get_dis_lits 
              current_type_args args1 args2 dis_eq_lits =
            (match current_type_args, args1, args2 with
            | type_h:: type_tl, h_args1::args1_tl, h_args2::args2_tl ->
                let dis_lit = add_typed_disequality_sym type_h h_args1 h_args2 in
                let new_dis_eq_lits = dis_lit::dis_eq_lits in
                get_dis_lits type_tl args1_tl args2_tl new_dis_eq_lits
            | _ -> 
	        assert (current_type_args = [] && args1 = [] && args2 = []);			
	        dis_eq_lits
            )
              (* in inverse order but this does not matter *)
          in
          let args1 = Term.arg_to_list (Term.get_args atom1) in 
          let args2 = Term.arg_to_list (Term.get_args atom2) in 
          let dis_eq_lits = get_dis_lits type_args args1 args2 [] in 	  
          create_clause tstp_source (dis_eq_lits@rest_lits1@rest_lits2)
    | Undef -> failwith "resolution_lifted: pred type should be defined"
  in
(* debug *)
  dbg D_res_lifted (lazy ("resolution_lifted: "^(Clause.to_string c1)^" "^(Clause.to_string c2)));
  dbg D_res_lifted (lazy ("concl: "^(Clause.to_string conclusion)));
(* debug *)
  conclusion

(*----------------------------*)
let resolution_lifted_unflatted (l1, c1, rest_lits1) (l2, c2, rest_lits2) =
  let res_concl = resolution_lifted (l1, c1, rest_lits1) (l2, c2, rest_lits2) in 
  Inference_rules.unflatten_clause res_concl


(* let prepare_for_resolution pred_clauses = *)
    (* rearrange in the form
       
       atom_1 -> [ 
       pos_lit1 =  [(c, rest_lits);..]
       neg_lit1 =  [(c, rest_list)...]
       atom = atom_1
       neg_atom = ~atom_1
       ]
       inside one atom we can do resolution in "propositional style"
       
       crosswise resolutions: 
       unify (1,atom_1) (2,atom_2) and apply crosswise pos/negative
       (or eq lifted resolution)
       
       atom_2 -> 
       [ 
       pos_lit1 =  [(c, rest_lits);..]
       neg_lit1 =  [(c, rest_list)...]
       atom = atom_2
       neg_atom = ~atom_2
       ]   
       split into  inner level iteration and outer level iteration 
       
     *)

(* (c, rest_lits)  where res_lits = clause_lits - (lit_resolve_upon) *)
type res_clause_slpit = clause * (lit list)
      
type res_atom_clauses = 
    {
     mutable res_cl_pos : res_clause_slpit list; (* clauses *)
     mutable res_cl_neg : res_clause_slpit list;
     res_atom : lit;
     res_neg_atom : lit;
   }
      
type res_atom_clauses_map = res_atom_clauses TMap.t
      
(* returns res_atom_clauses_map *)
      
      
let get_res_atom_map pred elim_clauses =
  let f current_map clause = 
    let all_lits = get_lits clause in 
    let (pred_lits,rest_lits) = List.partition (fun lit -> (Term.lit_get_top_symb lit) == pred) all_lits in 
    let pred_lit = 
      match pred_lits with 
      |[pred_lit] -> pred_lit 
      |_-> failwith "prepare_for_resolution: pred should occur exactlu once"
    in
    let atom = Term.get_atom pred_lit in 
    let res_atom_clauses = 
      try
        TMap.find atom current_map
      with 
        Not_found -> 
	  {
	   res_cl_pos = []; (* clauses *)
	   res_cl_neg = [];
	   res_atom = atom;
	   res_neg_atom = add_neg_atom atom;
	 }	 
    in
    let c_split = (clause,rest_lits) in
    (
     if (Term.is_pos_lit pred_lit)
     then 
       (res_atom_clauses.res_cl_pos <- c_split::res_atom_clauses.res_cl_pos)
     else
       (res_atom_clauses.res_cl_neg <- c_split::res_atom_clauses.res_cl_neg)
    );    
    let new_atom_map = TMap.add atom res_atom_clauses current_map in 
    new_atom_map
  in
  List.fold_left f 
    TMap.empty 
    ((BCSet.elements elim_clauses.elim_cl_pos)@ (BCSet.elements elim_clauses.elim_cl_neg))
    
(*-------------------*)

let check_subs_cl_to_cl_limit pe_state = 
  (get_val_stat res_clause_to_clause_subsumption) <= pe_state.pe_opt.subs_cl_to_cl_limit
    
let get_forward_simplification_fun_list pe_state = 
  let o = pe_state.pe_opt in
  [
(* self simplifications *)
(*   Simplify.self_simplify;*)

   o.pe_preprocess_conclusion_extern; 

   Simplify.equality_resolution;
   Inference_rules.bmc1_merge_next_func;
   Simplify.tautology_elim; 
   Simplify.eq_tautology_elim;
   

(* forward local/global *)
   Simplify.forward_subset_subsume (get_local pe_state);
   Simplify.forward_subset_subsume pe_state.pe_global_sim_state;
   if o.prop_glb_subs then (Simplify.forward_prop_subsume (* (get_local pe_state) *)) else id_fun;

   if o.lcl_fwd_subs && (check_subs_cl_to_cl_limit pe_state) then Simplify.forward_subs (get_local pe_state) else id_fun;
   if o.glb_fwd_subs && (check_subs_cl_to_cl_limit pe_state) then Simplify.forward_subs pe_state.pe_global_sim_state else id_fun;
   if o.lcl_fwd_subs_res && (check_subs_cl_to_cl_limit pe_state) then Simplify.forward_subs_res (get_local pe_state) else id_fun;
   if o.glb_fwd_subs_res && (check_subs_cl_to_cl_limit pe_state) then Simplify.forward_subs_res pe_state.pe_global_sim_state else id_fun;
  
 ]


let bwd_opt_check subs_opt clause =
  match subs_opt with 
  |Subs_Full -> true 
  |Subs_By_Length (l) ->  l >= (Clause.length clause)
  |Subs_Subset -> false 
        
        
let backward_sim_local pe_state clause = 
  let o = pe_state.pe_opt in

(*  let feature_list = Simplify.get_feature_list clause in *)


  (* local subset subsumed *)
  let local_subset_subsumed = Simplify.backward_subset_subsume (get_local pe_state)  clause in 
  let f_local_ss c = 
    dbg D_lcl_bwd_ss (lazy ((Clause.to_string c)^" by: "^(Clause.to_string clause)));
  in
  List.iter f_local_ss local_subset_subsumed;


(* local subsumed *)
  (if (bwd_opt_check o.lcl_bwd_subs clause)
  then
    begin
      let local_subsumed = Simplify.backward_subs_full (get_local pe_state) clause in 
      let f_local_subs c = 
	dbg D_lcl_bwd_subs (lazy ((Clause.to_string c)^" by: "^(Clause.to_string clause)));
      in
      List.iter f_local_subs local_subsumed;
    end
  );

(* local resolution subsumed *)  
  (if (bwd_opt_check o.lcl_bwd_subs_res clause)
  then
    begin 
      (* assertion: local subsumption resolution never produces clause with the predicate that we are elimininating ! *)
      (* since neither given nor clauses in local contain the elim-pred *)
      (* local subumption resolution *)          
      let local_subs_res_subsumed_new_list = Simplify.backward_subs_res (get_local pe_state) clause in 
      let f_local_subs_res (subsumed_list, new_cl) = 
	dbg D_lcl_bwd_subs_res  (lazy ((Clause.clause_list_to_string subsumed_list)^" by: "^(Clause.to_string new_cl)));
        ignore (Simplify.sim_add_clause (get_local pe_state) new_cl)
      in
      List.iter f_local_subs_res local_subs_res_subsumed_new_list
    end
  )


(*------------------------- global backward simplifications ---------------*)
(*-------- global simplifications only can be done after the resolve all is finished -----------*)
(*-------- otherwise interferes with the  current resolving state since claueses become dead *)
(*-------  but new with the same predicate are not taken into account (due to e.g. subsumption resoltution) ------*)

let backward_sim_global pe_state clause =     
  let o = pe_state.pe_opt in
(*  let feature_list = Simplify.get_feature_list clause in *)
  
  (* global subset subsumed *)
  let global_subset_subsumed = 
    Simplify.backward_subset_subsume pe_state.pe_global_sim_state clause in 
  

  let f_global_ss c = 
    dbg D_glb_bwd_ss  (lazy ((Clause.to_string c)^" by: "^(Clause.to_string clause)));
(*    remove_clause_from_pred_to_clauses pe_state c;*)
    remove_clause pe_state c;
  in
  List.iter f_global_ss global_subset_subsumed;
  
  (if (global_subset_subsumed != [])
  then
    (add_new_clause_to_pe_state pe_state  clause)
  );
  
(*---- expensive ------*)

  
(* global subsumed *)

  (if (bwd_opt_check o.glb_bwd_subs clause)
  then
    begin
      
      let global_subsumed = Simplify.backward_subs_full pe_state.pe_global_sim_state  clause in 
      
      let f_global_subs c = 
	dbg D_glb_bwd_subs (lazy ((Clause.to_string c)^" by: "^(Clause.to_string clause)));
	(* remove_clause_from_pred_to_clauses pe_state c;*)
	remove_clause pe_state c;
      in
      List.iter f_global_subs global_subsumed;
      
      (
       if (global_subsumed !=[])
       then
	 ( add_new_clause_to_pe_state pe_state clause)
      );
    end
  );

(* global resolution subsumed *)
  
  (if (bwd_opt_check o.glb_bwd_subs_res clause)
  then
    begin 
      
      (* assertion: if elimination is not aborted then *)
      (* global subsumption resolution is applied only after removal all clauses with the predicate that we eliminating *)
      (* this guarantees that we do not introduce new clauses with the predicate that we eliminating *)
      
      (* never produces clause with the predicate the we are elimininating ! *)
      (* global subsumption resolution *)
      
      let global_subs_res_subsumed_new_list  =  Simplify.backward_subs_res pe_state.pe_global_sim_state clause in 
      let f_global_subs_res (subsumed_list, new_cl) = 
	dbg D_glb_bwd_subs_res (lazy ((Clause.clause_list_to_string subsumed_list)^" given clause: "^(Clause.to_string clause)^" result: "^(Clause.to_string new_cl)));
	(* remove_clause_from_pred_to_clauses pe_state subsumed; *)       
	List.iter (remove_clause pe_state) subsumed_list;
	add_new_clause_to_pe_state pe_state new_cl;
      in
      List.iter f_global_subs_res global_subs_res_subsumed_new_list
        
    end
  )



(*-------------------*)
let pe_process_concl pe_state concl = 
  let forward_fun_list = get_forward_simplification_fun_list pe_state in
  let new_concl = fold_left_fun_list forward_fun_list concl in

(* debug *)
  dbg_env D_pe_process_concl (
  fun () ->   
    if (Clause.equal_bc concl new_concl) 
    then 
      (
       dbg D_pe_process_concl (lazy ("concl not simpl: "^(Clause.to_string concl)));
      )
    else
      ( 
        dbg D_pe_process_concl (lazy ("concl before simpl "
				      ^(Clause.to_string concl)^" clause length: "^(string_of_int (Clause.length concl))));
        dbg D_pe_process_concl (lazy ("concl after simpl "^(Clause.to_string new_concl)));
        
       )
 );
  
  check_empty_clause new_concl;
  backward_sim_local pe_state new_concl;
  new_concl



(*-------------------------*)
exception Abort_elimination
    
(*-------------------------*)
let check_ver_epr_concl concl = 
  if (is_ver_epr ()) 
  then
    (* check that conclusion does not have multiple occurrences of Next/Init/Property and does not mix them *)
    (* in theory multiple occurrences should be OK but give rise to big mess and needs fixing *)
    let is_bmc1_special_pred pred = 
      (pred == Symbol.symb_ver_next_state) || 
      (pred == Symbol.symb_ver_reachable_state) || 
      (pred == Symbol.symb_ver_init) ||
      (pred == Symbol.symb_ver_property) 
    in    
    let count_sp num _sign pred  = 
      if (is_bmc1_special_pred pred)
      then 
        num+1
      else
        num
    in
    let num_of_sp = Clause.fold_pred count_sp 0 concl in 
    if (num_of_sp > 1)
    then 
      raise Abort_elimination
    else
      ()    
  else
    ()
      
(* can raise Abort_elimination *)
(*-------------------*)
let iterate_inf pe_state inf l1 cl_split_list1  l2 cl_split_list2 = 
  let f (c1, rest_lits1) = 
    let g (c2, rest_lits2) = 
(*      if (not (Clause.get_is_dead c1)) && (not (Clause.get_is_dead c2)) *)
      if (not (glb_is_dead pe_state c1)) && (not (glb_is_dead pe_state c2))  
      then
        let concl = inf (l1, c1, rest_lits1) (l2, c2, rest_lits2) in 
        try 
          let new_concl = pe_process_concl pe_state concl in 
          check_ver_epr_concl concl;
          (if (not (pe_state.pe_opt.pe_conclusion_limit_test new_concl))
          then 
            (
             
	     dbg D_iterate_inf (lazy ("aborting elimination of this predicate due to clause length limit for: "
				      ^(Clause.to_string new_concl)));
	     raise Abort_elimination	    
            )
          else ()
          );
(*
  let new_concl_length = (Clause.length new_concl) in
  (if 
  ( new_concl_length > pe_state.pe_opt.pe_clause_length_limit) 
  &&
  (new_concl_length > (Clause.length c1))	      &&
  (new_concl_length > (Clause.length c2))
  
  then 
  (
  dbg D_iterate_inf (lazy ("aborting elimination of this predicate due to clause length limit for: "
  ^(Clause.to_string new_concl)));
  raise Abort_elimination
  )
  );
 *)
(*	  let feat = Simplify.get_feature_list new_concl in*)
          ignore  (Simplify.sim_add_clause (get_local pe_state) new_concl)
            
        with
          Eliminated -> 
	    (dbg D_iterate_inf  (lazy ("eliminated: "^(Clause.to_string concl))))
      else () (* one of premises is dead *)
    in
    List.iter g cl_split_list2 (* pred_clauses.res_neg_cl; *)
  in
  List.iter f cl_split_list1 (* pred_clauses.res_pos_cl; *)
    
    

(*
  let eligible_for_elim pe_state pred = 
  (pred_in_elim_set pe_state pred) &&
  (not (pred_in_protectd pe_state pred)) &&
  (not (pred_in_aborted pe_state pred)) 
 *)

(*----------- *)
let get_elim_clause_list elim_clauses = 
  (BCSet.elements elim_clauses.elim_cl_pos)@(BCSet.elements elim_clauses.elim_cl_neg)
                                               
(*
  let get_non_dead_context context = 
  let f c rest = 
  if (not (Clause.get_is_dead c))
  then 
  (c::rest)
  else
  rest
  in
  context_fold context f []
 *)
                                               
(* can raise Abort_elimination *)
                                               
(*-------------------*)
let resolve_all_pred pe_state pred elim_clauses = 
  (*assert (eligible_for_elim pe_state pred);*)
  
  let res_atom_map = get_res_atom_map pred elim_clauses in
(*  let local_size = get_elim_clauses_concl_estimated_size elim_clauses in *)
  (* maybe change to get_elim_clauses_size *)
  (* pe_state.pe_local_sim_state <- Some (Simplify.sim_create (sim_local_opt pe_state.pe_opt) local_size);  *)
  pe_state.pe_local_sim_state <- 
    Some (Simplify.sim_create (sim_local_opt pe_state.pe_opt));  

  (* inner level *)
  let inner_level_resolution _atom res_atom_clauses = 
    let l1 = res_atom_clauses.res_atom in
    let l2 = res_atom_clauses.res_neg_atom in
    let inf = 
      let mgu = Unif.unify_bterms (1,l1) (2,l1) in
      (resolution_basic mgu)   
    in
    iterate_inf pe_state inf l1 res_atom_clauses.res_cl_pos l2 res_atom_clauses.res_cl_neg
      (*    iterate_inf pe_state resolution_prop l1 res_atom_clauses.res_pos_cl l2 res_atom_clauses.res_neg_cl*)
  in
  TMap.iter inner_level_resolution res_atom_map;
  
  (* outer_level *)
(*      let outer_level_resolution atom res_atom_clauses =*)
  let f atom1 res_atom_clauses1 rest_map = 
    let new_map = TMap.remove atom1 rest_map in
    let g atom2 res_atom_clauses2 =
      try 
        let inf_fun = 
          if (pe_state.pe_opt.pe_has_eq)
          then
            resolution_lifted_unflatted
          else (* non-equational problem can just use resolution_basic*)		
            (* can raise Unif.Unification_failed *)
            let mgu = Unif.unify_bterms (1,res_atom_clauses1.res_atom) (2,res_atom_clauses2.res_atom) in
            (resolution_basic mgu)
        in
        
        (* positive atom1 with neg atom2 *)
        let l1_pos = res_atom_clauses1.res_atom in
        let l2_neg = res_atom_clauses2.res_neg_atom in
        iterate_inf pe_state inf_fun l1_pos res_atom_clauses1.res_cl_pos l2_neg res_atom_clauses2.res_cl_neg;
        
        (* neg atom1 with pos atom2 *)
        let l1_neg = res_atom_clauses1.res_neg_atom in
        let l2_pos = res_atom_clauses2.res_atom in 
        iterate_inf pe_state inf_fun l1_neg res_atom_clauses1.res_cl_neg l2_pos res_atom_clauses2.res_cl_pos;
      with
        Unif.Unification_failed -> ()
    in
    TMap.iter g new_map;
    new_map
  in
  ignore (TMap.fold f res_atom_map res_atom_map)

    
(*
  let context_num_non_dead context = 
  let f c rest = 
  if (not (Clause.get_is_dead c))
  then 
  rest+1 
  else
  rest
  in
  context_fold context f 0 
 *)
    
let context_num_lit_in_non_dead context = 
  let f c rest =  rest + (Clause.length c) in
  context_fold context ~non_dead:true f 0
(*
  let f c rest = 
  if (not (Clause.get_is_dead c))
  then 
  rest + (Clause.length c)
  else
  rest
  in
  context_fold context f 0 
 *)


(* form local to global: backward simplify global and add to global then clear local *)

(* if add_all is true than all non-dead clauses from local are added to global (as in successful elimination) *)
(* if add_all is false only clauses used in backward simplifications are added automatically (as in aborted elimination)  *)

let from_local_to_global ~add_all pe_state = 
  let g clause =       
(*    (if (not (Simplify.sim_is_dead (get_local pe_state) clause)) 
      then
      (	   
 *)

    backward_sim_global pe_state clause;   
    if add_all
    then
      (add_new_clause_to_pe_state pe_state clause;  )
    else ()
(*
  )
  );    *)
  in
  context_iter ~non_dead:true (Simplify.sim_get_context (get_local pe_state)) g;
  clear_local pe_state


(*-------------------------------------*)
exception Pred_to_elim_is_empty
    
let single_pred_elim pe_state pred = 
  
  assert (not (pred_in_aborted pe_state pred));
  assert (not (pred_in_affected pe_state pred));
  assert (pred_in_elim_set pe_state pred);
  assert (not (pred_in_protectd pe_state pred));
  dbg D_single_pred_elim (lazy ("--------------------"));       
  dbg D_single_pred_elim (lazy ("starting eliminating "^(Symbol.to_string pred)));       
  (* it can happen that protected got moved to re_try so we remove it for there *)
(*
(*  if (not (eligible_for_elim pe_state pred)) *)
  if (not (pred_in_elim_set pe_state pred)) 
  then 
  (     
  dbg D_single_pred_elim (lazy ("not eligible for elim: "^(Symbol.to_string pred)));
(*	    pe_state.pred_to_clauses <- SMap.remove pred pe_state.pred_to_clauses *)
  )
  else
  if (pred_in_protectd pe_state pred)
  then 
  (    
  dbg D_single_pred_elim (lazy ("in protected: add to aborted: "^(Symbol.to_string pred)));   
  pe_state.pe_aborted <- SSet.add pred pe_state.pe_aborted;
  )
  else      
 *)
  begin
    try	
(* TODO change! estimated clauses move to cycle *)
      let elim_clauses = 
        try
          SMap.find pred pe_state.pe_pred_to_elim_clauses 
        with 
          Not_found -> raise Pred_to_elim_is_empty
      in       
      
(*
  let estimated_concl_size = get_elim_clauses_concl_estimated_size elim_clauses in 
  let elim_clauses_size = (get_elim_clauses_size elim_clauses) in

  if (estimated_concl_size > pe_state.pe_opt.pe_estim_num_of_cl) 
  &&
  (estimated_concl_size > elim_clauses_size) (* do not skip if one side is <= 1 *)	  
  then
  begin	   
  dbg D_single_pred_elim (lazy ("skipping pred: "^(Symbol.to_string pred)^" estimated num clauses: "
  ^(string_of_int estimated_concl_size)^">"
  ^(string_of_int pe_state.pe_opt.pe_estim_num_of_cl)));       
  
  pe_state.pe_aborted <- SSet.add pred pe_state.pe_aborted;
(*	    pe_state.pred_to_clauses <- SMap.remove pred pe_state.pred_to_clauses *)
  end
  else
 *)
      begin
	dbg D_single_pred_elim (lazy ("--------------------"));       
	dbg D_single_pred_elim (lazy ("eliminating pred: "^(Symbol.to_string pred)));       	     
	
	
	(*------- resolving all------*)
	try	
	  resolve_all_pred pe_state pred elim_clauses;    (* can raise Abort_elimination *)
	  
	  let local_context = Simplify.sim_get_context (get_local pe_state) in
          
	  if (pe_state.pe_opt.pe_keep_elim 
                ~elim_symb:(pred)
                ~clauses_before_elim:(get_elim_clause_list elim_clauses) 
                ~clauses_after_elim:(Clause.context_to_list local_context ~non_dead:true)
             ) 
	  then   (* keep the elimination *)
	    begin
	      add_to_eliminated_pred_set pe_state pred;
              
	      dbg D_single_pred_elim (lazy ("eliminated pred: "^(Symbol.to_string pred)));
	      
	      (* 1. remove eliminated from everywhere *)
	      (*    from global *)
	      
	      (* 2. apply backward simplfications by new clauses to global *)
	      (* 3. add new non-dead clauses to pos/neg and global context *)
              
	      
	      (* 1. *)
	      let f c = 		 
		remove_clause pe_state c;
	      in
	      BCSet.iter f elim_clauses.elim_cl_pos;
	      BCSet.iter f elim_clauses.elim_cl_neg;
  	      
	      (* 2. 3. *)
	      from_local_to_global ~add_all:true pe_state;
	      (* pe_state.pe_re_try <- SSet.remove pred pe_state.pe_re_try; *)
	    end
	  else  (* aborted: do not keep elimination *)
 	    (
 	     (* still backward simplify global and add corresponding clauses *)
             pe_state.pe_aborted <- SSet.add pred pe_state.pe_aborted;
	     from_local_to_global ~add_all:false pe_state;	    
	    )
	with
	  Abort_elimination ->
	    ( (* still backward simplify global and add corresponding clauses *)
	      pe_state.pe_aborted <- SSet.add pred pe_state.pe_aborted;
	      from_local_to_global ~add_all:false pe_state;	 
	     )
      end
	
    with 
      Pred_to_elim_is_empty ->
	(
         
	 add_to_eliminated_pred_set pe_state pred;
	 dbg D_single_pred_elim (lazy ("eliminated pred: "^(Symbol.to_string pred)
			               ^(" all clauses with have been eliminated during previous eliminations")));
	)
    |x -> 
        ((* dbg D_single_pred_elim (lazy " should not happen ");*) 
          (* can happen when derive the empty clause *)
          
          raise x;
(*          failwith "single_pred_elim uncaught exception"*)
   ) 
(* let pred_clauses = SMap.find pred pe_state.pred_to_clauses *)
  end
    
    
(* move later *)
let get_pred_depth p = 
  match (Symbol.get_defined_depth p) with 
  |Def(d) -> 
      (*  out_dbg ~g:10 (lazy ("depth: "^(Symbol.to_string p)^" : "^(string_of_int d))); *)
      d
  |Undef -> 	 
      (* out_dbg ~g:10 (lazy ("depth undef: "^(Symbol.to_string p))); *)
      100000
        
        
(*----------------- elimination queue -----------------------------*)
(*
  type elimination_queue = 
  {
  mutable eq_prt_to_pred : SSet.t IntMap.t; (* prt -- priority *)
  mutable eq_pred_to_prt : int SMap.t
  }

  let create_eq () =
  {
  eq_prt_to_pred = IntMap.empty;
  eq_pred_to_prt = SMap.empty;
  }

  let eq_mem_pred eq pred = 
  SMap.mem pred eq.eq_pred_to_prt 

(* the pred should not be in the eq *)
  let eq_add_pred eq prt pred = 
  assert((not eq_mem_pred eq pred));

  let pred_prt_set = 
  try 
  IntMap.find ptr eq.eq_prt_to_pred 
  with 
  Not_found -> SSet.empty
  in
  let new_prt_set = SSet.add pred pred_prt_set in 
  eq.eq_prt_to_pred <- IntMap.add prt new_prt_set eq.eq_prt_to_pred;
  eq.eq_pred_to_prt <- SMap.add pred ptr eq.eq_pred_to_prt

  let eq_pred_prt eq pred = 
  SMap.find pred eq.eq_pred_to_prt

  let eq_remove_pred eq pred = 
  try 
  let prt = SMap.find pred eq.eq_pred_to_prt in 
  let pred_prt_set = IntMap.find ptr eq.eq_prt_to_pred in
  let new_pred_prt_set = SSet.remove pred pred_prt_set in 
  (
  if (SSet.is_empty new_pred_prt_set) 
  then 
  eq.eq_prt_to_pred <- IntMap.remove ptr eq.eq_prt_to_pred
  else
  eq.eq_prt_to_pred <- IntMap.add ptr new_pred_prt_set eq.eq_prt_to_pred
  );
  eq.eq_pred_to_prt <- SMap.remove pred eq.eq_pred_to_prt
  with 
  Not_found -> ()

  let eq_update eq prt pred = 
  eq_remove_pred eq pred;
  eq_add_pred eq prt pred
  
(* can raise Not_found if eq is empty *)  
(* returns one of the max priority preds but does not remove it *)
  let eq_max_pred eq = 
  let pred_prt_set = IntMap.max_binding eq.eq_prt_to_pred in   
  SSet.max_elt pred_prt_set (* max here is just for a canonical element from the set *)

  let eq_min_pred eq = 
  let pred_prt_set = IntMap.min_binding eq.eq_prt_to_pred in   
  SSet.max_elt pred_prt_set (* max here is just for a canonical element from the set *)

(* also removes *)
  let eq_max_pred_rm eq = 
  let max_pred = eq_max_pred eq in 
  eq_remove_pred eq max_pred;
  max_pred

  let eq_min_pred_rm eq = 
  let min_pred = eq_min_pred eq in 
  eq_remove_pred eq min_pred;
  min_pred


(*----------- priority based on estimated number of lits  after elimination ------------*)

  type cl_size_to_num_cl = int IntMap.t (* maps number of lits in a clause -> number of such clauses  *)

  let fill_cl_size_to_num bcset = 
  let f c rest = 
  let num_lits = Clause.length c in 
  let new_num_cl = 
  try 
  let num_cl = IntMap.find num_lits rest in 
  num_cl + 1          
  with 
  Not_found -> 1
  in
  IntMap.add num_lits new_num_cl rest
  in
  SSet.fold f bset IntMap.empty

  let estimate_elim_num_lits bcset1 bcset2 = 
  let size_to_num1 = fill_cl_size_to_num bcset1 in 
  let size_to_num2 = fill_cl_size_to_num bcset2 in 

  let f size1 num1 estim1 = 
  let g size2 num2 estim2 =
  (size1 + size2 -2)*num1*num2 + estim2 
  in
  IntMap.fold g size_to_num2 estim1
  in 
  IntMap.fold f size_to_num1 0


 *)  
        
(*----------------- main function -----------------------------*)
        
let predicate_elimination pe_options input =
  print_string " pe_s "; flush stdout;
(*  let start_time = Unix.gettimeofday () in *)
  let pe_state = pe_create_state pe_options input in
  begin
    try
      while 
        ((not (PQS.is_empty pe_state.pe_elimination_queue)) ||
        (not (SSet.is_empty pe_state.pe_currently_affected_preds))
   )
      do
        check_time pe_state;
        let process_affected pred = 
          if (pred_in_eliminated pe_state pred) 
          then
            ()
          else
            if (pred_in_protectd pe_state pred) 
            then
              (
               pe_state.pe_aborted <- SSet.add pred pe_state.pe_aborted;
               PQS.remove pe_state.pe_elimination_queue pred;
              )
            else
              begin (* not in protected *)
                (if (pred_in_aborted pe_state pred)
                then 
                  (
                   pe_state.pe_aborted <- SSet.remove pred pe_state.pe_aborted
                  )
                );
                
                let prt = compute_pred_elim_priority pe_state pred in 
                (*    let prt = get_concl_estimated_size pe_state pred in *)
                PQS.update_pr pe_state.pe_elimination_queue pred prt;         
              end          
        in
        SSet.iter process_affected pe_state.pe_currently_affected_preds;
        pe_state.pe_currently_affected_preds <- SSet.empty;
        (
         try    
           let (min_prt, elim_pred) = PQS.min_el_rm pe_state.pe_elimination_queue in     
           
           dbg D_cycle (lazy (" next to elim pred: "^(Symbol.to_string elim_pred)
                              ^" priority: "^(string_of_int min_prt)^"\n"));
           let estim_num_of_lits = min_prt in
           
           if (estim_num_of_lits > pe_state.pe_opt.pe_estim_num_of_lits) (* TODO: decouple priorities and estim_num_of_lits *)
           then 
             ( dbg D_cycle (lazy ("skipping pred: "^(Symbol.to_string 
                                                       elim_pred)
                                  ^" estimated num of lits: "
			          ^(string_of_int estim_num_of_lits)^">"
			          ^(string_of_int pe_state.pe_opt.pe_estim_num_of_lits)));       	  
	       pe_state.pe_aborted <- SSet.add elim_pred pe_state.pe_aborted;          
              )
           else
             single_pred_elim pe_state elim_pred;
         with 
           Not_found -> () (* pe_elimination_queue is empty *)
        );
(*

  assert (not (pred_in_aborted pe_state pred));
  assert (not (pred_in_affected pe_state pred));
  assert (pred_in_elim_set pe_state pred);
  assert (not (pred_in_protectd pe_state pred));    
 *)
        pe_state.pe_stat_cycle_num <- pe_state.pe_stat_cycle_num +1;
        Statistics.incr_int_stat 1 Statistics.pred_elim_cycles;    
        
      done;
    with PE_timeout -> ()
  end;
  let new_clause_list = Clause.context_to_list (Simplify.sim_get_context pe_state.pe_global_sim_state) ~non_dead:true (* ~non_dead:false *) in  
  let end_time = Unix.gettimeofday () in
  
(* statistics *)
  let input_size = cl_size input in 
  let new_clause_list_size = List.length new_clause_list in 
  let num_elim_clauses = (input_size - new_clause_list_size) in
  Statistics.incr_int_stat num_elim_clauses Statistics.pred_elim_cl;
  Statistics.add_float_stat (end_time -. pe_state.pe_start_time) Statistics.pred_elim_time;
  print_string " pe_e "; flush stdout;  
  new_clause_list
    

(*
(*================== OLD ==============*)	

  let predicate_elimination pe_options input =
  print_string " pe_s "; flush stdout;
  let start_time = Unix.gettimeofday () in
  let pe_state = pe_create_state pe_options input in
  
  let end_time = Unix.gettimeofday () in
  
(*----------------- main function -----------------------------*)
(* input is Cl_Context(clause_context) | Cl_List (clause_list)*)

(*

  
  stat_pred_elim_report_next_start_time := start_time;
 *)

  let orgin_opts = {pe_state.pe_opt with pe_has_eq = pe_state.pe_opt.pe_has_eq} in  (* copy *)

  let incr_limits_opts pe_state =
  let o = pe_state.pe_opt in
  let o_o = orgin_opts in (* original opts *)
  let new_pe_estim_num_of_cl = 2 * o.pe_estim_num_of_cl in         (* exp *)
  let new_pe_clause_length_limit = o.pe_clause_length_limit * 2 in (* linear *) 

  (if (new_pe_estim_num_of_cl <= o_o.pe_estim_num_of_cl) 
  then 
  ( dbg D_cycle (lazy ("incr : pe_estim_num_of_cl = "^(string_of_int new_pe_estim_num_of_cl)));
  o.pe_estim_num_of_cl <- new_pe_estim_num_of_cl
  )
  else 
  (o.pe_estim_num_of_cl <- o_o.pe_estim_num_of_cl)
  );

  (if (new_pe_clause_length_limit <= o_o.pe_clause_length_limit)
  then
  (dbg D_cycle (lazy ("incr : pe_clause_length_limit = "^(string_of_int new_pe_clause_length_limit)));
  o.pe_clause_length_limit <- new_pe_clause_length_limit
  ) 
  else 
  (o.pe_clause_length_limit <- o_o.pe_clause_length_limit )
  );
  in

  let opts_limits_eq_to_origin pe_state = 
  let o = pe_state.pe_opt in
  let o_o = orgin_opts in (* original opts *)
  ((o.pe_estim_num_of_cl = o_o.pe_estim_num_of_cl) && (o.pe_clause_length_limit = o_o.pe_clause_length_limit))
  in

  let init_new_opts_limits pe_state =
  let o = pe_state.pe_opt in
  o.pe_estim_num_of_cl <- 2;
  o.pe_clause_length_limit <-2
  in

  let _ = init_new_opts_limits pe_state in

  let retry_bound = 100 in (* TODO: move to options !*)

  (* next cycle possible *)

  (* incremental extend the est. num of clauses bound; can be  changed later *)
  
  let opts_limit_exeeded = ref false in 
  while (not !opts_limit_exeeded) 
  do
  let retry_count = ref 0 in 
  while (not (SSet.is_empty pe_state.pe_re_try)) && (!retry_count < retry_bound) 
  do
  retry_count := !retry_count + 1;
  let cycle_start_time = Unix.gettimeofday () in
  let cycle_number = pe_state.pe_stat_cycle_num in  
  dbg D_cycle (lazy ("start cycle:"
  ^(string_of_int cycle_number)
  ^" pe_re_try size: "^(string_of_int (SSet.cardinal pe_state.pe_re_try))));
  
(* high depth first which corresponds to inputs (invert depth in preprocess in reasoning or not ?) *)
  (*   let cmp_depth_inv_fun p1 p2 = Pervasives.compare (get_depth p2) (get_depth p1) in
       let cmp_fun = 
       ( if (val_of_override !current_options.bmc1_incremental)
       then 
       lex_combination [cmp_depth_inv_fun;  pe_options.pe_elim_order_cmp] 
       else
       pe_options.pe_elim_order_cmp
       )
       in
   *)
  
  let gbl_context = (Simplify.sim_get_context pe_state.pe_global_sim_state) in
  
  let cmp_fun =  (pe_options.pe_elim_order_cmp_fun gbl_context) in
  
  dbg D_cycle (lazy 
  (" Retry: "^(list_to_string Symbol.to_string (SSet.elements pe_state.pe_re_try) "," )^"\n\n")
  );

(*
  dbg D_cycle (lazy (" Global context \n\n "^(Clause.context_to_string gbl_context) ));
 *)    
  
  pe_state.pe_elimination_queue <- List.sort cmp_fun  (SSet.elements pe_state.pe_re_try);
  
  pe_state.pe_re_try <- SSet.empty;
  
  let f pred =  
  dbg D_cycle (lazy ("trying elim pred: "^(Symbol.to_string pred)
  ^" : depth "^(string_of_int (get_pred_depth pred))));
  single_pred_elim pe_state pred 
  in

  List.iter f pe_state.pe_elimination_queue;
  
  clear_local pe_state;    
  
  let cycle_end_time = Unix.gettimeofday () in
  
  let num_eliminated_pred = SSet.cardinal pe_state.eliminated_pred_set in
  let num_of_protected_pred = SMap.cardinal pe_state.pe_protected in
  dbg D_cycle (lazy ("end cycle:"
  ^(string_of_int cycle_number)
  ^" number of elim preds: "^(string_of_int num_eliminated_pred)
  ^" used time "^(string_of_float (cycle_end_time -. cycle_start_time) )
  ^" num of protected: "^(string_of_int  num_of_protected_pred )));
  

(* debug *)
  dbg_env D_cycle_check (
  fun () ->
  (
  assert   (
  let f pred cl_set = 
  let g c = 
  dbg D_cycle_check  (lazy ("protected clause "
  ^(Clause.to_string c)^" in protected on "
  ^(Symbol.to_string pred) ));
  if (Clause.get_is_dead c) 
  then 
  failwith ("pred_elim: clause "^(Clause.to_string c)^" in protected on "
  ^(Symbol.to_string pred) ^" is dead which should not happen")
  else ()
  in
  BCSet.iter g cl_set 
  in
  SMap.iter f pe_state.pe_protected;
  true 
  );
  
  assert(
  let f cl =
  let g _sign pred = 
  (if (SSet.mem pred pe_state.eliminated_pred_set)
  then
  (failwith 
  ("pred_elim: clause "^(Clause.to_string cl)^" in global non-dead but pred  "
  ^(Symbol.to_string pred) ^" is eliminated! ")
  )
  else ()
  )
  in
  if (not (Clause.get_is_dead cl))
  then
  (Clause.iter_pred g cl)
  else ()
  in
  context_iter (Simplify.sim_get_context pe_state.pe_global_sim_state) f;
  true
  )
  )
  );

  (* debug *)
  pe_state.pe_stat_cycle_num <- pe_state.pe_stat_cycle_num +1;
  Statistics.incr_int_stat 1 Statistics.pred_elim_cycles;    
  done; 
  
  pe_state.pe_re_try <- SSet.union pe_state.pe_re_try pe_state.pe_aborted;
  pe_state.pe_aborted <- SSet.empty;
  
  opts_limit_exeeded := (opts_limits_eq_to_origin pe_state);      
  incr_limits_opts pe_state;
  done;


  let new_clause_list =  Simplify.get_non_dead_clauses_list pe_state.pe_global_sim_state in 
  
  let end_time = Unix.gettimeofday () in
  
(* statistics *)
  let input_size = cl_size input in 
  let new_clause_list_size = List.length new_clause_list in 
  let num_elim_clauses = (input_size - new_clause_list_size) in
  Statistics.incr_int_stat num_elim_clauses Statistics.pred_elim_cl;
  Statistics.add_float_stat (end_time -. start_time) Statistics.pred_elim_time;

  print_string " pe_e "; flush stdout;  
  new_clause_list

(*================== OLD ==============*)	
 *)
(*----------------------------------------------------------------------------------------------------------*)
(*---- get_most_preds_to_eliminate:  auxilary function for pre-filling pe_opt.pe_elimination_set  ----------*)


(*
  let get_not_to_elim_symb_set () = special_symbols_set
 *)
(*
  let f rest_set p  = 
  SSet.add p rest_set
  in
  List.fold_left f SSet.empty Symbol.special_symbols
 *)

let is_bmc1_protected pred = 
  (
   (Symbol.get_bool_param Symbol.is_clock pred) 
 || 
   (Parser_types.is_less_or_range_symb pred)
 ||
   (AigClausifier.aig_is_input_var pred)
  )
    
let is_finite_models_protected pred = 
  (Symbol.get_property pred) = Symbol.DomainPred
    
(* resturns set of pred from the input for elimination and map from pred to number of occurrenses *)
(* includes most predicates from the input but not special_symbols *)
(* one can remove extra symbols from the resulting set *)
    
    
let get_most_preds_to_eliminate input = 
  let add_occ_map pred occ_map = 
    let old_num = 
      try 
        SMap.find pred occ_map
      with 
        Not_found -> 0
    in
    let new_num = old_num + 1 in
    SMap.add pred new_num occ_map 
  in
  let f (pred_set, occ_map) c = 
    let g (c_pred_set, c_occ_map)  _sign pred =
      if  
        (Symbol.is_special_symb pred) || 
        (is_bmc1_protected pred) || 
        (is_finite_models_protected pred) 
         || 
        ((is_ver_epr ()) && (Symbol.get_bool_param Symbol.is_conj_symb pred)) (* do not eliminate conjecture symbols*)
      then 
        (c_pred_set, c_occ_map)
      else 	
        (SSet.add pred c_pred_set, add_occ_map pred c_occ_map)
    in
(*
  if (Clause.get_is_dead c) 
  then
  (pred_set,occ_map) 
  else
 *)
    (Clause.fold_pred g (pred_set,occ_map) c)
  in
(*  context_fold input ~non_dead:true f (SSet.empty, SMap.empty) *)
  cl_fold f (SSet.empty, SMap.empty) input 

