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

let pure_lit_flag = true

(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_preprocess
  | D_trace
  | D_add_clause
  | D_remove_clause
  | D_decide 
  | D_up 
  | D_ur
  | D_br
  | D_upq
  | D_rm_wt_var
  | D_conflict 
  | D_pl

let dbg_gr_to_str = function 
  | D_preprocess -> "preprocess"	
  | D_trace -> "trace"
  | D_add_clause ->  "add"
  | D_remove_clause -> "rm"
  | D_decide -> "decide"
  | D_up -> "up" (* unit propagation *)
  | D_ur -> "ur" (* unit resolution *)
  | D_br -> "br" (* binary resolution *)
  | D_upq -> "upq" (* unit prop. queue *)
  | D_rm_wt_var -> "rm_wt_var"
  | D_conflict -> "conflict"
  | D_pl -> "pl" (* pure literal *)

let dbg_groups =
  [
(*   D_preprocess;*)
   D_trace; 
   D_add_clause;
   D_remove_clause;
   D_decide;
   D_up;
   D_ur;
   D_br;
(*   D_upq;*)
   D_rm_wt_var;
   D_conflict;
   D_pl
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
(* exception Satisfiable *)


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

module LKey (VarLit:VarLit) =  
  struct  
    type t = VarLit.l
    let compare l1 l2 = Pervasives.compare (VarLit.get_lit_id l1) (VarLit.get_lit_id l2)
  end

module LMap_Make(VarLit:VarLit) = Map.Make(LKey (VarLit))
module LSet_Make(VarLit:VarLit) = Set.Make(LKey (VarLit))


module DPLLMake(VarLit:VarLit) = 
  struct 
    type var = VarLit.v
    type lit = VarLit.l

    module VMap = VMap_Make(VarLit) 
    module VSet = VSet_Make(VarLit) 

    module LMap = LMap_Make(VarLit) 
    module LSet = LSet_Make(VarLit) 

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
      | P_URes of clause  (* implying clause *)



    and

(*------ model -------*)
	  var_impl_type = 
	Decided (* of int*) (* decision level *)
(* | UP_Implied of clause *)
      | Implied of clause (* implied by clause and previous assignments *)
	    
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
		  (first_char_str = "c") || (first_char_str = "p")
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
      let lit = VarLit.var_to_lit var_model_val.var_val var_model_val.var in 
      let compl_mod_lit = VarLit.compl_lit lit in
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
		 
	 in 
	 let result = clause_create new_lits new_parents in 
	 dbg D_ur (lazy ((clause_to_string result)^" <- "^(VarLit.lit_to_string lit)^" : "^(clause_to_string c)));
	 result  
	)

    let in_clause lit clause = 
      List.exists (lit_eq lit) (clause_get_lits clause)

(* resolve: lit from main_clause *)

    let resolve lit main_clause side_clause =             
      let compl_lit = VarLit.compl_lit lit in
      let main_lits = (clause_get_lits main_clause) in
      let side_lits = (clause_get_lits side_clause) in
      assert (in_clause lit main_clause);
      assert (in_clause compl_lit side_clause);
      let (_,new_main_part) = List.partition (lit_eq lit) main_lits in 
      let (_,new_side_part) = List.partition (lit_eq compl_lit) side_lits in 
      let new_parent =  P_BRes (lit, main_clause, side_clause) in 
      let result = clause_create (new_main_part@new_side_part) new_parent in 
      dbg D_br (lazy ((clause_to_string result)^" <- "
		      ^"l: "^(VarLit.lit_to_string lit)^" :m: "
		      ^(clause_to_string main_clause)^" :s: "
		      ^(clause_to_string side_clause)));
      result

(* get the clause that is implied by S and is implying c modulo current model *)
    let get_implying c = 
      match c.parents with 
      |P_Input | P_BRes _ -> c
      |P_URes implying -> implying


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


    exception Satisfiable of smp_dpll_state
    exception Unsatisfiable of clause

(*----- init_sate --------*)
	
    let init_smp_state = 
      {
       smp_clauses = CSet.empty;
       smp_model = VMap.empty;  
       smp_watch = VMap.empty; 
       smp_up_queue = LMap.empty;
       smp_var_queue = var_priority_queue_init; 
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
	   dbg D_upq (lazy ("new_better_impl: "^(VarLit.lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
	   let new_up_queue = LMap.add lit impl_clause smp_up_queue in 
	   {
	    smp_state with 
	    smp_up_queue = new_up_queue
	  }
	  )
	else
	  (
	   dbg D_upq (lazy ("old_better_impl: "^(VarLit.lit_to_string lit)^" : "^(clause_to_string old_impl)));  
	   smp_state
	  )
      with 
	Not_found -> 
	  (
	   let new_up_queue = LMap.add lit impl_clause smp_up_queue in 
	   dbg D_upq (lazy ("new:"^(VarLit.lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
	   {
	    smp_state with 
	    smp_up_queue = new_up_queue
	  }
	  )

    exception UPQ_Empty

    let smp_remove_max_up_queue smp_state = 
      try
	let (lit, impl_clause) =  LMap.max_binding smp_state.smp_up_queue in
	dbg D_upq (lazy ("rm: "^(VarLit.lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
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
	out_str ((VarLit.lit_to_string lit)^" <- "^(clause_to_string impl_clause));
      in     
      out_str ("------ up queue -------");
      LMap.iter f smp_state.smp_up_queue;
      out_str ("------ end up queue ---")



(*---------- adding/removing clauses----*)

	

(* smp_modif_watch can be used for adding/removing clauses from smp_watch by using for f: CSet.add/CSet.remove *)

(* TODO pure literals are collected, note that pure here is wrt to clauses of length >=2 *)

    let smp_modif_watch f up_queue smp_init_watch c = 
      let modif_lit_watch c (smp_watch, pure_lit_cset) l = 
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
	
	let new_watch = 
	  if ((new_wt_el.wt_pos = CSet.empty) && (new_wt_el.wt_neg = CSet.empty))
	  then 
	    (dbg D_rm_wt_var (lazy ((VarLit.var_to_string var)));  
	     VMap.remove var smp_watch)
	  else 	   
	    (VMap.add var new_wt_el smp_watch)
	in  
	let new_pure_lit_cset = 
	  if pure_lit_flag 
	  then 
	    let pos_lit = VarLit.var_to_lit true var in 
 	    let neg_lit = VarLit.var_to_lit false var in 
	    if (new_wt_el.wt_pos = CSet.empty) && (not (in_up_queue up_queue pos_lit))
	    then
	      (
	       dbg D_pl (lazy (VarLit.lit_to_string neg_lit));  
	       CSet.union new_wt_el.wt_neg pure_lit_cset)
	    else
	      if (new_wt_el.wt_neg = CSet.empty) && (not (in_up_queue up_queue neg_lit))
	      then
		(dbg D_pl (lazy (VarLit.lit_to_string pos_lit));  
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
	out_str ((VarLit.lit_to_string lit)^" 0\n");
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
		raise (Satisfiable (smp_dpll_state))		  
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
	let d_lit = VarLit.var_to_lit d_pol d_var in


	let new_state = 
	  {
	   smp_dpll_state with 
	   smp_var_queue = new_var_queue;
	 }
	in
	dbg D_decide (lazy ((VarLit.lit_to_string d_lit)^":p "^(string_of_int d_priority)));
	
	(d_var, d_pol, d_priority, new_state)
	  
    	    
(*-----------*)

    let smp_unit_propagate smp_state lit =

      let (pol,var) = VarLit.lit_to_var lit in	
      let var_model_val = VMap.find var smp_state.smp_model in

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

	dbg D_up (lazy ((VarLit.lit_to_string lit)^" <- "^(clause_to_string impl_clause)));
	
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
	    let (pol,var) = VarLit.lit_to_var lit in 
	    let var_model_val = 
	      {
	       var = var;
	       var_val = pol; 
	       var_impl_type = Implied (impl_clause) 
	     }
	    in

	    dbg D_up (lazy ("ext model: "^(VarLit.lit_to_string lit)));

	    let new_model = VMap.add var var_model_val before_model_ext_state.smp_model in
	    
	    let model_ext_state = {before_model_ext_state with smp_model = new_model} in

	    let prop_state = smp_unit_propagate model_ext_state lit in
	    
	    let confl_clause = smp_dpll_rec prop_state in 
	    let compl_lit = VarLit.compl_lit lit in 		

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
	    let lit = VarLit.var_to_lit d_pol d_var in
	    let var_model_val = 
	      {
	       var = d_var;
	       var_val = d_pol;
	       var_impl_type = Decided;
	     }	  
	    in
	    let ext_model_state = { decide_state with 
				    smp_model = add_to_model decide_state.smp_model d_var var_model_val} in 
	    let prop_state = smp_unit_propagate ext_model_state lit in 
	    let confl_clause = smp_dpll_rec prop_state in
	    
	    let compl_lit = VarLit.compl_lit lit in 
	    (* TODO: optionally also add the conflict clause to the clause set *)
	    
	    if (in_clause compl_lit confl_clause) 
	    then 
	      let impl_state = smp_add_up_queue decide_state compl_lit confl_clause in 
	      smp_dpll_rec impl_state 		  
	    else
	      confl_clause	   
	  end	    

(*-------------*)

    let out_model smp_state = 
      out_str "--------- Model ---------";
      let f var var_model_val = 
	let lit = VarLit.var_to_lit var_model_val.var_val var_model_val.var in
	out_str (VarLit.lit_to_string lit)
      in
      VMap.iter f smp_state.smp_model

(*-------------*)
    let smp_start_smp_dpll () =
      let all_clauses = dimacs_stdin () in     
      let smp_state = init_smp_state_clist all_clauses in
(*
  out_str ("smp_state unit clauses: \n ");
  out_up_clauses smp_state;
  out_str ("smp_state clauses: \n ");
 *)
      smp_out_clauses smp_state;
      let new_smp_state = fill_priority smp_state in
      out_str (pref_str^"Solving...");
      try
	ignore (smp_dpll_rec new_smp_state)
      with
      | Satisfiable (smp_state) -> 
	  (out_str "SATISFIABLE\n";
	   out_model smp_state;
	  )
      |Unsatisfiable c -> 
	  out_str "UNSATISFIABLE"

	    
  end

module DPLL_VInt = DPLLMake(IntVarLit)

let _ = DPLL_VInt.smp_start_smp_dpll () 

(* let _ = DPLL_VInt.test_smp_state () *)

(*----------JUNK----------------------*)

(*
    let smp_is_confl_state smp_state = 
      param_is_def smp_state.smp_conflict_clause
*)
(* *)
(*
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
*)


(*------- OLD -------*)
(*
  let smp_dpll_old smp_state = 
  
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
 *)


(*-----------------BELOW is NOT USED -------*)
	    

(*-------- dpll_state not finished---------*)
(*
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



  end
*)

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
