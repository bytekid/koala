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

(*----- debug modifiable part-----*)

let dbg_flag = true

type dbg_gr = 
  | D_preprocess
  | D_trace
  | D_add_clause
  | D_decide 
  | D_up 
  | D_conflict 


let dbg_gr_to_str = function 
  | D_preprocess -> "preprocess"	
  | D_trace -> "trace"
  | D_add_clause ->  "add_clause"
  | D_decide -> "decide"
  | D_up -> "up"
  | D_conflict -> "conflict"

let dbg_groups =
  [
(*   D_preprocess;*)
   D_trace; 
   D_add_clause;
   D_decide;
   D_up;
   D_conflict;
 ]

let module_name = "dpll"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)



(* input clauses : unit propagate*)
exception Satisfiable 
exception Unsatisfiable 

module type VarLit = 
  sig
    type v   (* var *)
    type l   (* lit *)
    val var_to_lit : bool -> v -> l (* pol. as bool *)
    val lit_to_var : l -> bool * v 
    val is_pos_lit : l -> bool
    val compl_lit : l -> l
    val make_var : int -> v (* pos int *)
    val make_lit : int -> l (* +- v *)	
    val get_lit_id : l -> int (* do not mix var and lit ids *)
    val get_var_id : v -> int 
    val var_to_string : v -> string
    val lit_to_string : l -> string
  end


module IntVarLit = 
  struct 
    type v = int  (* start from 1  *)
    type l = int  (* pos even, neg odd  *)

    let var_to_lit pol v = 
      if pol
      then
	(v lsl 1)
      else
	((v lsl 1) +1)    

    let is_pos_lit l = ((l mod 2) = 0)
	  
    let lit_to_var l = 
      if (is_pos_lit l)
      then
	(true, (l lsr 1))
      else
	(false, (l lsr 1))
	  
    let compl_lit l = 
      let (pol,v) = lit_to_var l in
      var_to_lit (not pol) v

    let get_var_id v = v

    let get_lit_id l = l

    let make_var n = 
      (assert (n >0));
      n
 
    let make_lit n = 
      assert (n != 0);
      let v = make_var (abs n) in
      if n > 0 
      then
	var_to_lit true v 
      else
	var_to_lit false v 

    let next_var v = v + 1
	
    let var_to_string v = string_of_int v 
	
    let lit_to_string l = 
      let (pol,v) = lit_to_var l in 
      let l_int = 
	if pol 
	then
	  v
	else
	  (-v)
      in
      string_of_int l_int
  end 
    
    
module VKey (VarLit:VarLit) =  
  struct  
    type t = VarLit.v
    let compare v1 v2 = Pervasives.compare (VarLit.get_var_id v1) (VarLit.get_var_id v2)
  end
 
module VMap_Make(VarLit:VarLit) = Map.Make(VKey (VarLit))
module VSet_Make(VarLit:VarLit) = Set.Make(VKey (VarLit))

(*
  struct 
    include Map.Make(VKey (VarLit))
  end
*)
    
(* type var_type =  *)
(*     V_Decided *)
(*   | V_Implied (clause) *)

(* module Model(VarLit) =  *)
(*   struct  *)
(*     type var = VarLit.v *)
(*     type lit = VarLit.lit *)
	  
(*     type var_impl_type =  *)
(* 	V_Decided *)
(*       | V_Implied (clause) *)

(*     type var_val =  *)
(* 	{ *)
(* 	 var_val = bool; *)
	 
(*        } *)
(*   end *)

(*
module Clause (VarLit:VarLit) =
   struct 
     
   end

module DPLLParse(VarLit:VarLit) = 
  struct 
    
  end
*)

module DPLLMake(VarLit:VarLit) = 
  struct 
    type var = VarLit.v
    type lit = VarLit.l
    module VMap = VMap_Make(VarLit) 

    let lit_compare l1 l2 = Pervasives.compare (VarLit.get_lit_id l1) (VarLit.get_lit_id l2)
    let lit_equal l1 l2 = ((VarLit.get_lit_id l1) = (VarLit.get_lit_id l2))
    let lit_eq = lit_equal 
	 

(*----- clauses -------*)	  
    type clause = 
	{
	 lit_list : lit list;
	 parents : parents; 
       }
    and
	  parents = 
	P_Input
      | P_BRes of lit * clause * clause 
      | P_URes of (* var_model_val *) clause  
           (* original clause (implied) by the inital set such that if we unit resolve all model literals we obtain the resulting child clause *)



    and
(*------ model -------*)
     var_impl_type = 
	Decided (* of int*) (* decision level *)
(* | UP_Implied of clause *)
      | Unit_clause of clause (* literal is a derived unit clause *)
    and
	  var_model_val = 
	{
	 var : var;
	 var_val : bool;
	 var_impl_type : var_impl_type;
       }	  
	  

(*--------*)
    type model = var_model_val VMap.t 

    type model_res = 
      |M_False of var_model_val 
      |M_True of var_model_val
      |M_Undef 


    let in_model model var  = 
      VMap.mem var model

    let find_model model var = 
      VMap.find var model 

(* assert that var is not in the model *)
    let add_to_model model var var_model_val = 
      assert (not (VMap.mem var model));
      VMap.add var var_model_val model
	
    let check_model model lit = 
      let (pol,var) = VarLit.lit_to_var lit in 
      try 
	let var_model_val = VMap.find var model in 
	if (pol = var_model_val.var_val) 
	then 
	  M_True(var_model_val)
	else
	  M_False (var_model_val)
      with 
	Not_found -> M_Undef

(*--------*)
    let clause_create lit_list parents =       
      let sorted_list = list_remove_duplicates_ordered_non_ptr (List.sort lit_compare lit_list) in 
      {
       lit_list = sorted_list;
       parents = parents
     }

    let clause_get_lits c = c.lit_list

    module CKey = 
      struct
	type t = clause 
	let compare c1 c2 = list_compare_lex lit_compare (clause_get_lits c1) (clause_get_lits c2)
      end
	
    module CMap = Map.Make(CKey)
    module CSet = Set.Make(CKey)
	

    let is_unit_clause c = 
      match (clause_get_lits c) with 
      |[_] -> true
      |_-> false
      
    let clause_to_string c = (list_to_string VarLit.lit_to_string c.lit_list " ")^(" "^(string_of_int 0))

    let clause_list_to_string c_list = 	list_to_string clause_to_string c_list "\n"



(*------- parsing -------*)    
	
(* returns list of clauses *)

    let dimacs_stdin () =
      let rec parse acc = 
	try
	  begin
	  let rec first_non_comment_line () = 
	    let to_skip l =  
	      if l = "" then true 
	      else
		let first_char_str =  Str.first_chars l 1 in		
		(first_char_str = "c") ||	(first_char_str = "p")
	    in
	    let l = read_line () in
	    if (to_skip l)
	    then first_non_comment_line ()
	    else l 
	  in
	  let line =  first_non_comment_line () in
		
	  let str_list = Str.split (Str.regexp " ") line in	  
	  let int_list_with_0 = List.map int_of_string str_list in 
	  let int_list = 
	    match (list_remove_last int_list_with_0) with 
	    |Some (zero, int_list) -> assert (zero = 0); int_list (* remove last element *)	  
	    |None -> failwith "empty imput line"
	  in
	  let lit_list = List.map VarLit.make_lit int_list in 
	  let clause = clause_create  lit_list P_Input in
	  parse (clause::acc)
	  end
	with 
	  End_of_file -> acc
      in
      parse []
   
    let test_parser () = 
      let all_clauses = dimacs_stdin () in     
      out_str ("c clauses: "^(string_of_int (List.length all_clauses))^"\n");
      out_str (clause_list_to_string all_clauses) 

(*-- unit resolve with model val  --*)	  
(*-- --*)

    let unit_resolve_model var_model_val c = 
      let compl_mod_lit = VarLit.var_to_lit (not var_model_val.var_val) var_model_val.var in
      let c_lits = (clause_get_lits c) in
      let new_lits = List.filter (fun l -> not (lit_equal compl_mod_lit l)) c_lits  in

      if (List.length c_lits) = (List.length new_lits)
      then
	c
      else
	(
	 let new_parents = 
	   match c.parents with 
	   | P_Input  | P_BRes _ -> P_URes c 
           | P_URes _pc -> c.parents 	  
		 
	 in clause_create new_lits new_parents
	)

(* lit from main_clause *)
    let resolve lit main_clause side_clause =             
      let compl_lit = VarLit.compl_lit lit in
      let main_lits = (clause_get_lits main_clause) in
      let side_lits = (clause_get_lits side_clause) in
      assert (List.exists (lit_eq lit) main_lits);
      assert (List.exists (lit_eq compl_lit) side_lits);
      let (_,new_main_part) = List.partition (lit_eq lit) main_lits in 
      let (_,new_side_part) = List.partition (lit_eq compl_lit) side_lits in 
      let new_parent =  P_BRes (lit, main_clause, side_clause) in 
      clause_create (new_main_part@new_side_part) new_parent
   
(* get the clause that is implied by S and is implying c modulo current model *)
    let get_implying c = 
      match c.parents with 
      |P_Input | P_BRes _ -> c
      |P_URes implying -> implying

(* *)
    let unit_resolve_conflict uc c = 
      match (clause_get_lits uc) with 
      |[uc_lit] ->	  
	  let compl_uc_lit = VarLit.compl_lit uc_lit in 
	  if (List.exists (lit_eq compl_uc_lit) (clause_get_lits c)) 
	  then 
	    let implying = get_implying uc in 
	    resolve uc_lit implying c
	  else
	    c
      |_-> failwith "unit_resolve_conflict: not unit"


(*---- dpll ---------*)


(* two watch *)
    type watch_el = 

	{
	 wt_pos : CSet.t;
	 wt_neg : CSet.t;
       }
  
(* TODO: extend with counters to avoid cardinal *)
    let get_watch_size pol watch_el = 
      if pol 
      then 
	CSet.cardinal watch_el.wt_pos
      else 
	CSet.cardinal watch_el.wt_neg
       
(*------- var priority queue --------*)

    type priority_var = int * var 
(*
    module PV_Key = 
      struct 
	type t = priority_var 
	let compare pv1 pv2 = pair_compare_lex Pervasive.compare VarLit.compare pv1 pv2
      end
	
    module PQ_Var = Set.Make(PV_Key) (* priority queue implemented as a set; TODO change into list of PQs *)
*)
  
    type var_priority_queue = 
	{
	 v_to_pr : int VMap.t; (* var -> priority *)
	 pr_to_v : (var list) IntMap.t   (* set ordered with priority *)
       }

    let var_priority_queue_init = 
      {
       v_to_pr = VMap.empty;
       pr_to_v = IntMap.empty;
     }

(* remove_max_pq_var returns (max_priority_var, rest_queue) *)
(* raises Not_found if the queue is empty *)

    let remove_max_var_pq pq =
      let (max_pr,max_pr_var_list) = IntMap.max_binding pq.pr_to_v in
      match max_pr_var_list with 
      | v::tl -> 	 
	  let new_pr_to_v = 
	    if tl = [] (* h is the last var with max priority *)
	    then 
	      IntMap.remove max_pr pq.pr_to_v
	    else
	     IntMap.add max_pr tl pq.pr_to_v
	  in
	  let new_v_to_pr = VMap.remove v pq.v_to_pr in
	  let new_pq = 
	    {
	     v_to_pr = new_v_to_pr;
	     pr_to_v = new_pr_to_v;
	   }
	  in (v, max_pr, new_pq)
      | [] -> failwith "remove_max_var_pq: list should not be empty"


(* we assert that var is not in pq before adding *)
    let add_var_pq pr var pq = 
      let new_v_to_pr = 
	assert (not (VMap.mem var pq.v_to_pr));
	VMap.add var pr pq.v_to_pr
      in
      let new_pr_to_v = 
	try 
	  let old_v_list = IntMap.find pr pq.pr_to_v in 
	  IntMap.add pr (var::old_v_list) pq.pr_to_v 
	with 
	  Not_found ->  IntMap.add pr ([var]) pq.pr_to_v 
      in
      let new_pq = 
	{
	 v_to_pr = new_v_to_pr;
	 pr_to_v = new_pr_to_v;
       }
      in
      new_pq
      
(* TODO: apply_f_pq apply function to priorities   *)
	      
(*       let max_var = PQ_Var.max_elt pq in  *)
(*       let rest_of_pq = PQ_Var.remove max_var pq in *)
(*       (max_var, rest_of_pq) *)

(*     let add_priority_var_queue priority var  pq =  *)
(*       PQ_Var.add (priority,var) pq *)

(* (\* increments priority of a variable; if the variable is not in the queue then then it is added with 0 priority *\) *)
(*     let inc_priority var pq =  *)
(*       try  *)
(* 	let  *)



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
	 smp_watch : watch_el VMap.t; (* all non-unit clauses clauses where lit occurs *)
(*	 trail : var list;   *)
	 smp_conflict_clause : clause param;
	 smp_unit_prop_queue : lit list; (* propagation queue *)
	 smp_new_units : clause list; (* units that have not been processed, can be inconsistent *)
	 smp_var_queue : var_priority_queue; (* not decided yet *)	
       }

(*----- init_sate --------*)
	  
    let init_smp_state = 
      {
       smp_clauses = CSet.empty;
       smp_model = VMap.empty;  
       smp_watch = VMap.empty; 
       smp_conflict_clause = Undef;
       smp_unit_prop_queue = [];
       smp_var_queue = var_priority_queue_init; 
     }


(*---------- adding/removing clauses----*)

(* smp_modif_watch can be used for adding/removing clauses from smp_watch by using for f: CSet.add/CSet.remove *)

    let smp_modif_watch f smp_init_watch c = 
      let modif_lit_watch c smp_watch l = 
	let (pol,var) = VarLit.lit_to_var l in
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
	let new_watch = VMap.add var new_wt_el smp_watch in     
	new_watch
      in
      let lits = clause_get_lits c in 
      let new_smp_watch = List.fold_left (modif_lit_watch c) smp_init_watch lits  in 
      new_smp_watch
	

(*---*)	 
    let smp_add_clause_to_watch smp_watch c = 
      smp_modif_watch CSet.add smp_watch c

(*---*)
    let smp_remove_clause_from_watch smp_watch c = 
      smp_modif_watch CSet.remove smp_watch c
	
   
(*--------------*)
    exception Empty_clause
    exception Conflict of var_model_val * clause * smp_dpll_state

(* as the result of adding a clause we can have a conflict clause *)

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
	  raise Empty_clause (* can only happen with the empty clause derived at the top level *)
	|[unit_lit] -> 
	    begin
	      (* check with the model *)
	      match (check_model smp_state.smp_model unit_lit) with 
	      | M_False (var_model_val) -> 
		  let conflict_clause = (get_implying c) in
		  dbg D_conflict (lazy (clause_to_string conflict_clause));
		  let new_state = 
		    {
		     smp_state with 
		     smp_conflict_clause = Def(conflict_clause)
		   }
		      (* raise (Conflict (var_model_val, c, smp_state)) *)
		  in
		  new_state

	      | M_True (var_model_val) -> 

       (* already there *)
		  smp_state (* TODO: check what to do we added implied but M_true is decided *)
		    
	      | M_Undef -> 
		  let (pol,var) = VarLit.lit_to_var unit_lit in 
		  let var_model_val = 
		    {
		     var = var;
		     var_val = pol;
		     var_impl_type = Unit_clause(c);
		   }	  
		  in
		  let new_model = add_to_model smp_state.smp_model var var_model_val in
		  let new_prop_queue = unit_lit::smp_state.smp_unit_prop_queue in 
		(* new state *)
		  {
		   smp_state with 
		   smp_model = new_model;
		   smp_unit_prop_queue = new_prop_queue;
		 }
	    end
	|_non_unit ->
	    let new_smp_clauses =  CSet.add c smp_state.smp_clauses in
	    let new_smp_watch =  smp_add_clause_to_watch smp_state.smp_watch c in 
	    {
		 smp_state with 
	     smp_clauses = new_smp_clauses; 
	     smp_watch = new_smp_watch;
	   }
	end

	  
	  
    let smp_remove_clause smp_state c = 
      if (CSet.mem c smp_state.smp_clauses)
      then 
	let new_smp_clauses =  CSet.remove c smp_state.smp_clauses in
	let new_smp_watch =  smp_remove_clause_from_watch smp_state.smp_watch c in 
	{
	 smp_state with 
	 smp_clauses = new_smp_clauses; 
	 smp_watch = new_smp_watch;
       }
      else
	smp_state

(*-- init clist --*)
    let init_smp_state_clist clist = 
      List.fold_left smp_add_clause init_smp_state clist



(*-- out --*)
    let smp_out_clauses smp_state =
      let f c = out_str (clause_to_string c) in
      CSet.iter f (smp_state.smp_clauses)

(*-- debug --*)
    let test_smp_state () = 
      let all_clauses = dimacs_stdin () in     
      let smp_state = init_smp_state_clist all_clauses in
      out_str ("smp_state unit clauses: \n ");
      out_str ((list_to_string VarLit.lit_to_string smp_state.smp_unit_prop_queue " 0\n")^" 0\n");
      out_str ("smp_state clauses: \n ");
      smp_out_clauses smp_state

(*-----------*)

    let smp_is_confl_state smp_state = 
      param_is_def smp_state.smp_conflict_clause

(*-- decide --*)

(* can raise Not_found if all vars are decided *)

    let smp_decide smp_dpll_state = 
      
      let is_undecided v = not (in_model smp_dpll_state.smp_model v) in
      
      let rec get_undecided_var var_queue = 
	let (var,var_priority,new_var_queue) = remove_max_var_pq var_queue in 
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
      let d_lit = VarLit.var_to_lit d_pol d_var in
      let d_var_model_val = 
	{
	 var = d_var;
	 var_val = d_pol;
	 var_impl_type =  Decided 
       }
      in
      let new_model = add_to_model smp_dpll_state.smp_model d_var d_var_model_val  in
      
      let new_unit_prop_queue = d_lit :: (smp_dpll_state.smp_unit_prop_queue) in
      let new_state = 
	{
	 smp_dpll_state with 
	 smp_model = new_model;     
	 smp_unit_prop_queue = new_unit_prop_queue;
	 smp_var_queue = new_var_queue;
       }
      in
      dbg D_decide (lazy ((VarLit.lit_to_string d_lit)^":p "^(string_of_int d_priority)));

      (d_var, d_pol, d_priority, new_state)

(*-----------*)
    let rec smp_unit_propagation smp_state lit =
(*      match smp_state.smp_unit_prop_queue with 
      | lit::tl -> 
	  begin
	    let new_state = smp_unit_propagation { smp_state with smp_unit_prop_queue = tl} in
 *)
      let new_state = smp_state in (* to keep old code *)
    	    let (pol,var) = VarLit.lit_to_var lit in	
    	    let var_model_val = VMap.find var smp_state.smp_model in
    	    assert(pol = var_model_val.var_val);	
    	    
	    dbg D_up (lazy (VarLit.lit_to_string lit));
	    match new_state.smp_conflict_clause with 
	    | Def(conflict_clause) ->
		begin
		    match (var_model_val.var_impl_type) with 
		    | Unit_clause(uc) ->  
		 
			let new_conflict_clause = unit_resolve_conflict uc conflict_clause in	      
			dbg D_conflict (lazy (clause_to_string new_conflict_clause));
			let new_state =  
			  {
			   smp_state with 
			   smp_conflict_clause = Def(new_conflict_clause);
			   smp_unit_prop_queue = [];
			 }
			in
			new_state

		    |Decided ->
			let new_state =  
			  {
			   smp_state with 			   
			   smp_unit_prop_queue = [];
			 }
			in
			new_state
		end
	    | Undef ->

		let smp_watch = VMap.find var new_state.smp_watch in		
    		let (clauses_to_elim, clauses_to_resolve) =
    		  if pol
    		  then
    		    (smp_watch.wt_pos, smp_watch.wt_neg)
    		  else 
    		    (smp_watch.wt_neg, smp_watch.wt_pos)
    		in
		let resolve_fun c current_state =
		  if (smp_is_confl_state smp_state) 
		  then  
		    current_state
		  else
		    let new_cl = unit_resolve_model var_model_val c in

		    let new_state = smp_add_clause current_state new_cl in (* can raise Conflict *) 
		    new_state
		in		
		let smp_resolved_state = CSet.fold resolve_fun clauses_to_resolve new_state in
		
		let smp_state_removed_elim =  
		  if  (smp_is_confl_state smp_resolved_state) 
		  then
		    smp_resolved_state
		  else
		    CSet.fold (fun c state -> smp_remove_clause state c) clauses_to_elim smp_resolved_state in
		smp_state_removed_elim
(*		smp_unit_propagation smp_state_removed_elim *)
(*	  end *)
(*      | [] ->  smp_state *)


(* fill_priority  after first unit propagation *)	  

    let fill_priority smp_state = 
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

(*-------------*)
    exception Satisfiable of smp_dpll_state
	
    let smp_dpll_rec smp_state = 
      
      match smp_state.prop_queue 

    let smp_dpll smp_state = 
      
      let rec prop_rec smp_state = 
	let prop_state = smp_unit_propagation decide_state in
	smp_decide prop_state
      and
	  decide_rec smp_state = 
	let (d_var, d_pol, d_priority, decide_state) = smp_decide smp_state in
	let prop_state = prop_rec decide_state in
	
	
(* assume that unit prop already has been applied before smp_dpll_rec *)
	let rec smp_dpll_rec smp_state = 
	  try
	    let (d_var, d_pol, d_priority, decide_state) = smp_decide smp_state in
	    let prop_state = smp_unit_propagation decide_state in
	    
	    match prop_state.smp_conflict_clause with 
	    | Def conflict_clause -> 
		let impl_pol = not d_pol in
		let impl_lit = VarLit.var_to_lit impl_pol d_var in
		let new_uc = clause_create [impl_lit] (P_URes (conflict_clause)) in 
		let new_state = smp_add_clause decide_state new_uc in 
		smp_dpll_rec new_state	      
		  
	    | Undef -> smp_dpll_rec prop_state
		  
	  with
	    Not_found -> 
	      raise (Satisfiable (smp_state))
	in      
	let up_state = smp_unit_propagation smp_state in 
	let new_state = fill_priority up_state in
	if (smp_is_confl_state new_state) 
	then 
	  raise Unsatisfiable 
	else	
	  smp_dpll_rec new_state

(*-------------*)



    let smp_start_dpll () =
      let all_clauses = dimacs_stdin () in     
      let smp_state = init_smp_state_clist all_clauses in
      out_str ("smp_state unit clauses: \n ");
      out_str ((list_to_string VarLit.lit_to_string smp_state.smp_unit_prop_queue " 0\n")^" 0\n");
      out_str ("smp_state clauses: \n ");
      smp_out_clauses smp_state;
      smp_dpll smp_state
      
(*
    let rec analyse_conflict var_model_val conflict_clause smp_state  =  
      if (get_lits conflict_clause) = []
      then 
	raise Unsatisfiable
      else
  
      match var_model_val.var_impl_type with 
      |Decided -> 
	  let var = var_model_val.var in 
	  let pol = var_model_val.var_pol in
	  let impl_pol = not pol in
	  let impl_lit = VarLit.var_to_lit impl_pol var in
	  let impl_var_model_val = 
	    {
	     var = var;
	     var_val = impl_pol;
	     var_impl_type = Unit_clause (get_implied uc) 
	   }
	  in
	  let new_model = add_to_model smp_dpll_state.smp_model var d_var_model_val  in		
(*		  let new_unit_prop_queue = uc :: (smp_dpll_state.smp_unit_prop_queue) in *)
	  let new_state = 
	    {
	     smp_dpll_state with 
	     smp_model = new_model;     
	     smp_unit_prop_queue = new_unit_prop_queue;		   
	   }
	  in
	  smp_unit_propagation smp_state
	    
	      |Unit_clause side_clause ->
		  let new_conflict_clause = 
		    
*)
(*   
   | Conflict (var_model_val, _clause, _smp_dpll_state) 
	-> 
*)
(*
	let (units, non_units) = List.partition is_unit_clause resolved_list in
	let add_unit 
*)
	
(*-----------------BELOW is NOT USED -------*)
    

(*-------- dpll_state not finished---------*)

(* dpll_state invariants: *)
(*  1. all vars = (vars in model) U var_queue = vars in two_watch_list *)
(*  2. vars in trail = vars in model *)
(*  3. lits are added to model before to unit_prop_queue *)
    type dpll_state = 
	{
	 all_clauses : clause list; 
	 model : model;             (* current partial model *)
	 watch : watch_el VMap.t;
	 (* trail : var list;   *)
	 unit_prop_queue : lit list; (* propagation queue *)
	 var_queue : var_priority_queue; (* not decided yet *)	
       }

(*----- dpll return -----*)

(*     type dpll_return =  *)

(* 	Model of model *)
(*         (\* conlfict clause, new var priorities, learnt clauses *\) *)
(*       | Conflict of clause  * var_priority_queue * (clause list)   *)


(*     let rec unit_propagate dpll_state =  *)
(*       match dpll_state.unit_prop_queue with  *)
(*       | [] -> dpll_state *)
(*       | lit::tl  ->  *)
(* 	  let (pol,var) = VarLit.lit_to_var in  *)
(* 	  assert (VMap.mem var dpll_state.two_watch_list); *)
(* 	  let two_watch = VMap.find var dpll_state.two_watch_list in 	  *)
(* 	  let new_watch lit clause =  *)
	    
	    
	    
	    
(* (\* decide: returns new dpll state  can raise Not_found if var_queue is empty *\) *)

	    
(*     let rec dpll dpll_state =  *)
(*       if dpll_state.unit_prop_queue != []  *)
(*       then   *)
	

(*     let decide dpll_state =  *)
(*       let  *)

(*     let rec unit_propagate dpll *)
(*

    let st_add_clause st cl = 
      let process_lit lit = 
	let (pol,v) = VarLit.lit_to_var lit in 
	

    let create_state clause_list = 
      
  *)     

  end
    
module DPLL_VInt = DPLLMake(IntVarLit)

(* let _ = DPLL_VInt.test_smp_state () *)

let _ = DPLL_VInt.smp_start_dpll () 
