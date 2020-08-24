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
open Prop_var
open Prop_env

let pure_lit_flag = false

(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_preprocess
  | D_trace
  | D_add_clause
  | D_remove_clause
  | D_decide 
  | D_ext_state
  | D_up 
  | D_ur
  | D_br
  | D_upq
  | D_tw
  | D_rm_wt_var
  | D_conflict 
  | D_pl

let dbg_gr_to_str = function 
  | D_preprocess -> "preprocess"	
  | D_trace -> "trace"
  | D_add_clause ->  "add"
  | D_remove_clause -> "rm"
  | D_decide -> "decide"
  | D_ext_state -> "ext_state"
  | D_up -> "up" (* unit propagation *)
  | D_ur -> "ur" (* unit resolution *)
  | D_br -> "br" (* binary resolution *)
  | D_upq -> "upq" (* unit prop. queue *)
  | D_tw -> "tw" (* two watch *) 
  | D_rm_wt_var -> "rm_wt_var"
  | D_conflict -> "conflict"
  | D_pl -> "pl" (* pure literal *)

let dbg_groups =
  [
(*   D_preprocess;*)

   D_trace; 
(*   D_add_clause; *)
(*   D_remove_clause; *)
   D_decide;
(*   D_ext_state; *)
   D_up;
   D_ur;
   D_br;
(*   D_upq; *)
(*   D_tw; *)
(*   D_rm_wt_var; *)
   D_conflict;
   D_pl;
 ]

let module_name = "dpll_fun"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)



(*-------- dpll_state_smp ---------*)

(* dpll_state invariants: *)

(*  0. smp_clauses constians all non-unit clauses; all_clauses = smp_clauses U smp_up_queue *)

(*  1. all vars = (vars in model) U var_queue = vars in two_watch_list *)
(*  2. vars in var_queue can be in model and should be checked separetely *)
(*  3. lits are added to model before to unit_prop_queue *)

    type smp_dpll_state = 
        {
         smp_clauses : CSet.t; 
         smp_model : model;             (* current partial model *)
         smp_watch : watch_el VMap.t;   (* all non-unit clauses clauses where lit occurs *)
         smp_up_queue : clause LMap.t; (* propagation queue: lit -> implication clause *)
         smp_var_queue : var_priority_queue; (* not decided yet *)      
       }


	    
(*----- init_sate --------*)
          
    let init_smp_state = 
      {
       smp_clauses = CSet.empty;
       smp_model = create_model ();  
       smp_watch = VMap.empty; 
       smp_up_queue = LMap.empty;
       smp_var_queue = create_var_priority_queue (); 
     }



(*-------- up_queue  --------*)
	
    let smp_add_up_queue smp_state lit impl_clause = 
      let better_impl_clause c1 c2 = (* true c1 is better impl. clause than c2*)
	(List.length (clause_get_lits c1)) < (List.length (clause_get_lits c2))  (* TODO exp. with decision level *)
      in
      
      let smp_up_queue = smp_state.smp_up_queue in
      try
	let old_impl = LMap.find lit smp_up_queue in 
	if (better_impl_clause impl_clause old_impl) 
	then
	  (
	   dbg D_upq (lazy ("new_better_impl: "^(lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
	   let new_up_queue = LMap.add lit impl_clause smp_up_queue in 
	   {
	    smp_state with 
	    smp_up_queue = new_up_queue
	  }
	  )
	else
	  (
	   dbg D_upq (lazy ("old_better_impl: "^(lit_to_string lit)^" : "^(clause_to_string old_impl)));  
	   smp_state
	  )
      with 
	Not_found -> 
	  (
	   let new_up_queue = LMap.add lit impl_clause smp_up_queue in 
	   dbg D_upq (lazy ("new:"^(lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
	   {
	    smp_state with 
	    smp_up_queue = new_up_queue
	  }
	  )

    exception UPQ_Empty

    let smp_remove_max_up_queue smp_state = 
      try
	let (lit, impl_clause) =  LMap.max_binding smp_state.smp_up_queue in
	dbg D_upq (lazy ("rm: "^(lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
	let new_state = 
	  {
	   smp_state with 
	   smp_up_queue = LMap.remove lit smp_state.smp_up_queue
	 }
	in
	((lit,impl_clause),new_state)
      with 
	Not_found -> raise UPQ_Empty


    let in_up_queue up_queue lit = 
      LMap.mem lit up_queue

(*----------*)
    let out_up_queue smp_state =       
      let f lit impl_clause = 
	out_str ((lit_to_string lit)^" <- "^(clause_to_string impl_clause));
      in     
      out_str ("------ up queue -------");
      LMap.iter f smp_state.smp_up_queue;
      out_str ("------ end up queue ---")



(*---------- adding/removing clauses----*)

(* smp_modif_watch can be used for adding/removing clauses from smp_watch by using for f: CSet.add/CSet.remove *)

(* TODO pure literals are collected, note that pure here is wrt to clauses of length >=2 *)

    let smp_modif_watch f up_queue smp_init_watch c = 
      let modif_lit_watch c (smp_watch, pure_lit_cset) l = 
	let (pol,var) = lit_to_var l in
	let wt_el =
	  try  
	    VMap.find var smp_watch 
	  with 
	    Not_found -> 
	      {
	       wt_pos = CSet.empty;
	       wt_neg = CSet.empty;
	     }
	in 
	let new_wt_el = 
	  if pol 
	  then 
	    {
	     wt_el with 
	     wt_pos = f c wt_el.wt_pos;
	   }
	  else
	    {
	     wt_el with 
	     wt_neg = f c wt_el.wt_neg;
	   }
	in
	
	let new_watch = 
	  if ((new_wt_el.wt_pos = CSet.empty) && (new_wt_el.wt_neg = CSet.empty))
	  then 
	    (dbg D_rm_wt_var (lazy ((var_to_string var)));  
	     VMap.remove var smp_watch)
	  else 	   
	    (VMap.add var new_wt_el smp_watch)
	in  
	let new_pure_lit_cset = 
	  if pure_lit_flag 
	  then 
	    let pos_lit = var_to_lit true var in 
 	    let neg_lit = var_to_lit false var in 
	    if (new_wt_el.wt_pos = CSet.empty) && (not (in_up_queue up_queue pos_lit))
	    then
	      (
	       dbg D_pl (lazy (lit_to_string neg_lit));  
	       CSet.union new_wt_el.wt_neg pure_lit_cset)
	    else
	      if (new_wt_el.wt_neg = CSet.empty) && (not (in_up_queue up_queue neg_lit))
	      then
		(dbg D_pl (lazy (lit_to_string pos_lit));  
		 CSet.union new_wt_el.wt_pos pure_lit_cset
		)
	      else
		pure_lit_cset
	  else
	    pure_lit_cset
	in
	(new_watch, new_pure_lit_cset)
      in
      let lits = clause_get_lits c in 
      let new_smp_watch_plcs = List.fold_left (modif_lit_watch c) (smp_init_watch, CSet.empty) lits  in 
      new_smp_watch_plcs
	

(*---*)	 
    let smp_add_clause_to_watch up_queue smp_watch c = 
      let (new_smp_watch, _plcs) = smp_modif_watch CSet.add up_queue smp_watch c in
      new_smp_watch
	
(*--------------*)
	
    let smp_add_clause smp_state c = 
      if  (CSet.mem c smp_state.smp_clauses)
      then 
	smp_state
      else
	begin
	  dbg D_add_clause (lazy (clause_to_string c));  
	  let lits = clause_get_lits c in       
	  match lits with
	  |[] ->
	      raise (Unsatisfiable (c)) (* can only happen with the empty clause derived at the top level *)
		
	  |[lit] -> 
	      let impl_clause = get_implying c in
	      smp_add_up_queue smp_state lit impl_clause
		
	  |_non_unit ->
	      let new_smp_clauses =  CSet.add c smp_state.smp_clauses in
	      let new_smp_watch = smp_add_clause_to_watch smp_state.smp_up_queue smp_state.smp_watch c in
	      let new_state =
		{smp_state with 
		 smp_clauses = new_smp_clauses;
		 smp_watch = new_smp_watch;
	       }
	      in
	      new_state
	end


(*------------*)

    let smp_remove_clause_from_watch up_queue smp_watch c = 
      let (new_smp_watch, pure_lit_cset) = smp_modif_watch CSet.remove up_queue smp_watch c in
      (new_smp_watch, pure_lit_cset)

	
    let rec smp_remove_clause_set smp_state cset = 
      if cset = CSet.empty 
      then 
	smp_state
      else
	let up_queue = smp_state.smp_up_queue in
	let f c (smp_watch, all_clauses, cset_to_remove) = 
	  let (new_smp_watch, new_pure_lit_cset) = smp_remove_clause_from_watch up_queue smp_watch c in
	  let new_all_clauses = CSet.remove c all_clauses in
	  dbg D_remove_clause (lazy (clause_to_string c));  
	  (new_smp_watch, new_all_clauses, (CSet.union new_pure_lit_cset cset_to_remove))
	in
	let (new_smp_watch, new_smp_clauses, new_cset_to_remove) = 
	  CSet.fold f cset (smp_state.smp_watch, smp_state.smp_clauses, CSet.empty) in
	let new_smp_state = 
	  {
	   smp_state with 
	   smp_clauses = new_smp_clauses;
	   smp_watch = new_smp_watch;
	 }
	in
	smp_remove_clause_set new_smp_state new_cset_to_remove

	  
	  

(* assert that c is not unit *)	  
    let rec smp_remove_clause smp_state c = 
      assert((List.length (clause_get_lits c)) >=2);

      if (CSet.mem c smp_state.smp_clauses)
      then 
	smp_remove_clause_set smp_state (CSet.singleton c)
      else
	smp_state


(*-- init clist --*)
    let init_smp_state_clist clist = 
      List.fold_left smp_add_clause init_smp_state clist



(*-- out --*)
    let smp_out_clauses smp_state =
      let f c = out_str (clause_to_string c) in
      CSet.iter f (smp_state.smp_clauses)
	
    let out_up_clauses smp_state = 
      let f lit _impl = 
	out_str ((lit_to_string lit)^" 0\n");
      in
      LMap.iter f smp_state.smp_up_queue 

(*-- debug --*)
    let test_smp_state () = 
      let all_clauses = dimacs_stdin () in     
      let smp_state = init_smp_state_clist all_clauses in
      out_str ("smp_state unit clauses: \n ");
      out_up_clauses smp_state;
      out_str ("smp_state clauses: \n ");
      smp_out_clauses smp_state

(*-----------*)

(*-- decide --*)

(* can raise Not_found if all vars are decided *)

    let smp_decide smp_dpll_state = 
      
      let is_undecided v = 
	not (in_model smp_dpll_state.smp_model v) && (VMap.mem v smp_dpll_state.smp_watch) (* TODO: fixme *)
      in
      
      let rec get_undecided_var var_queue = 
	let (var,var_priority,new_var_queue) = 
	  try
	    remove_max_var_pq var_queue 
	  with 
	    Not_found ->
	      raise (Satisfiable (smp_dpll_state.smp_model))	
	in 
	if (is_undecided var)
	then
	  (var, var_priority, new_var_queue)
	else
	  get_undecided_var new_var_queue
      in
      let (d_var,d_priority,new_var_queue) = get_undecided_var smp_dpll_state.smp_var_queue in
      
(* decide polatiry based on a heirustic *)
      let get_d_pol smp_dpll_state var = 
	(* as a heiristic get polarity which will make true more clauses *)
	let watch = VMap.find var smp_dpll_state.smp_watch in
	let pos_w_size = get_watch_size true watch in
	let neg_w_size = get_watch_size false watch in
	if pos_w_size >= neg_w_size 
	then
	  true 
	else 
	  false
      in

      let d_pol = get_d_pol smp_dpll_state d_var in
      let d_lit = var_to_lit d_pol d_var in


      let new_state = 
	{
	 smp_dpll_state with 
	 smp_var_queue = new_var_queue;
       }
      in
      dbg D_decide (lazy ((lit_to_string d_lit)^":p "^(string_of_int d_priority)));
      
      (d_var, d_pol, d_priority, new_state)
	
    	
(*-----------*)

    let smp_unit_propagate smp_state lit =

      let (pol,var) = lit_to_var lit in	
      let var_model_val = find_model smp_state.smp_model var in

      try
	let smp_watch = VMap.find var smp_state.smp_watch in		

	let (clauses_to_elim, clauses_to_resolve) =
    	  if pol
    	  then
    	    (smp_watch.wt_pos, smp_watch.wt_neg)
    	  else 
    	    (smp_watch.wt_neg, smp_watch.wt_pos)
	in
	let resolve_fun c current_state =
	  let new_cl = unit_resolve_model var_model_val c in      
	  let new_state = smp_add_clause current_state new_cl in 
	  new_state
	in		
	let smp_resolved_state = CSet.fold resolve_fun clauses_to_resolve smp_state in
	let rm_state = CSet.fold 
	    (fun c state -> smp_remove_clause state c) 
	    (CSet.union clauses_to_elim clauses_to_resolve)  smp_resolved_state  
	in 
	rm_state
      with 
	Not_found -> (* var is not in  smp_state.smp_watch, may be in up_queue *)
	  smp_state

(*----- fill_priority after first unit propagation -----*)	  

    let smp_fill_priority smp_state = 
      let f var watch_el pq =
	let max_size = 
	  list_find_max_element compare 
	    [(CSet.cardinal watch_el.wt_pos);(CSet.cardinal watch_el.wt_neg)]
	in
	add_var_pq max_size var pq
      in
      let new_pq = VMap.fold f smp_state.smp_watch smp_state.smp_var_queue 
      in
      {
       smp_state with 
       smp_var_queue = new_pq
     }

(*-------*)

    let check_empty_clause c = 
      (if ((clause_get_lits c) = [])
      then 
	raise (Unsatisfiable (c))
      else ()
      )
	
(*-----------------------------------------*)
	
    type dpll_ret_type = clause 

(* smp_dpll_rec: returns conflict clause; SAT/UNSAT via exceptions *)

    let rec smp_dpll_rec smp_state = 
      try 
	let ((lit, impl_clause), before_model_ext_state) =  smp_remove_max_up_queue smp_state in 

	dbg D_up (lazy ((lit_to_string lit)^" <- "^(clause_to_string impl_clause)));
	
(* check model *)
	
	match (check_model smp_state.smp_model lit) with 
	|M_True _ ->	   
	    smp_dpll_rec before_model_ext_state 

	|M_False (var_model_val) -> 
	    (
	     dbg D_conflict (lazy (clause_to_string impl_clause));
	     impl_clause (* impl_clause is a conflict clause *)
	    )
	|M_Undef -> 
	    let (pol,var) = lit_to_var lit in 
	    let var_model_val = 
	      {
	       var = var;
	       var_val = pol; 
	       var_impl_type = Implied (impl_clause);
	       var_dlevel = -1; (* not used in smp_dpll *)
	     }
	    in

	    dbg D_up (lazy ("ext model: "^(lit_to_string lit)));

	    let new_model = add_to_model before_model_ext_state.smp_model var var_model_val  in
	    
	    let model_ext_state = {before_model_ext_state with smp_model = new_model} in

	    let prop_state = smp_unit_propagate model_ext_state lit in
	    
	    let confl_clause = smp_dpll_rec prop_state in 
	    let compl_lit = compl_lit lit in 		

	    if (in_clause compl_lit confl_clause) 
	    then
	      let new_confl_clause = resolve lit impl_clause confl_clause in 	     
	      dbg D_conflict (lazy (clause_to_string new_confl_clause));
	      check_empty_clause new_confl_clause;
	      new_confl_clause
	    else
	      confl_clause
      with 
	UPQ_Empty ->  (* all propagated *)
	  begin (*assume all lit are propagated *)	 
	    let (d_var, d_pol, d_priority, decide_state) = smp_decide smp_state in (* can raise Satisfiable *)
	    let lit = var_to_lit d_pol d_var in
	    let var_model_val = 
	      {
	       var = d_var;
	       var_val = d_pol;
	       var_impl_type = Decided;
	       var_dlevel = -1; (* not used in smp_dpll *)
	     }	  
	    in
	    let ext_model_state = { decide_state with 
				    smp_model = add_to_model decide_state.smp_model d_var var_model_val} in 
	    let prop_state = smp_unit_propagate ext_model_state lit in 
	    let confl_clause = smp_dpll_rec prop_state in
	    
	    let compl_lit = compl_lit lit in 
	    (* TODO: optionally also add the conflict clause to the clause set *)
	    
	    if (in_clause compl_lit confl_clause) 
	    then 
	      let impl_state = smp_add_up_queue decide_state compl_lit confl_clause in 
	      smp_dpll_rec impl_state 		  
	    else
	      confl_clause	   
	  end	    


(*-------------*)
    let dpll_func_run_stdin () =
      let all_clauses = dimacs_stdin () in     
      let smp_state = init_smp_state_clist all_clauses in
(*
  out_str ("smp_state unit clauses: \n ");
  out_up_clauses smp_state;
  out_str ("smp_state clauses: \n ");
 *)
      smp_out_clauses smp_state;
      let new_smp_state = smp_fill_priority smp_state in
      out_str (pref_str^"Solving...");
      begin
	try
	  ignore (smp_dpll_rec new_smp_state)
	with
	  Satisfiable (smp_model) -> 
	    (
	     out_str "SATISFIABLE\n";
	     out_model smp_model;
	    )
	|Unsatisfiable c -> 
	    out_str "UNSATISFIABLE"
        | Termination_Signal -> 
            out_str ("\n\n User Terminated\n\n");
(*            out_stats state.stats; *) (* TODO add statistics as in dpll_imp*)
            exit 1;
        | x ->
            (
      (*       out_stats state.stats; *) (* TODO add statistics as in dpll_imp*)
             if dbg_flag then
	       Format.eprintf "Unexpected error after main.Backtrace:@\n%s@\n@." (Printexc.get_backtrace ());	    
             raise x
            )	
	    
      end


let _ = dpll_func_run_stdin ()

(*-----------------------------*)
