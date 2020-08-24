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
  | D_trail
  | D_reset
  | D_implied
  | D_cancel_until 
  | D_lemma 

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
  | D_trail -> "trail"
  | D_reset -> "reset"
  | D_implied -> "implied"
  | D_cancel_until -> "cancel_until"
  | D_lemma -> "lemma"

let dbg_groups =
  [
   D_preprocess;

(*   D_trace; *)
(*   D_add_clause; *)
(*   D_remove_clause; *)
   D_decide;
(*   D_ext_state; *)
   D_up;
   D_ur; 
   D_br;
(*   D_upq; *)
(*   D_tw; *)
   D_rm_wt_var;
   D_conflict;
   D_pl;
   D_trail;
   D_reset;
   D_implied;
   D_cancel_until;
   D_lemma
 ]

let module_name = "dpll_imp"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


    

(*	  
  module TWC_K =
  struct 
  type t = tw_clauses
  let compare (c1,_) (c2,_) = CKey.compare c1 c2
  end

  module TWC_S = Set.Make(TWC_K)
  module TWC_M = Map.Make(TWC_K)
 *)
type tw_clauses = lit CMap.t 

type tw_el = 
    {
     tw_var : var; 
     mutable tw_pos : tw_clauses;  (* tw: map from clauses to the other watched literal *)
     mutable tw_neg : tw_clauses;
   }

type stats = 
    {
     mutable num_input_clauses : int;
     mutable num_decisions : int;
     mutable num_propagations : int;
     mutable num_conflicts : int;
   }
      
let init_stats () = 
  {
   num_input_clauses = 0;
   num_decisions = 0;
   num_propagations = 0;
   num_conflicts = 0;
 }

(* out stats *)
    
let val_dist = 40

let stat_int_to_str name stats_val = 
  (space_padding_str val_dist ((tptp_safe_str name)^":"))
  ^(string_of_int stats_val)

(*	  
(* truncates to 3 digits after .*)
  let stat_float_to_str s = 
  (space_padding_str val_dist ((tptp_safe_str s.float_entry_name)^":"))
  ^(string_of_float (truncate_n 3 s.float_value))
 *)	  

let get_stats_str stats =
  String.concat "\n"
    ["------------ Statistics ------------";
     (stat_int_to_str "num_input_clauses" stats.num_input_clauses);
     (stat_int_to_str "num_decisions" stats.num_decisions);
     (stat_int_to_str "num_propagations" stats.num_propagations);
     (stat_int_to_str "num_conflicts" stats.num_conflicts);
     "------------------------------------\n";
   ]		      
    
let out_stats stats = out_str (get_stats_str stats)

type var_phase_count = 
    {
     vp_pos : int;
     vp_neg : int;
   }

(*------ dpll_state invariants: ------*)

(*  0. clauses constians all non-unit clauses; all_clauses = smp_clauses U smp_up_queue *)

(*  1. all vars = (vars in model) U var_queue = vars in two_watch_list *)
(*  2. vars in var_queue can be in model and should be checked separetely *)
(*  3. lits are added to model before to unit_prop_queue *)


type dpll_state = 
    {
     mutable input_clauses : clause list;

     mutable all_clauses : CSet.t; 
     mutable model : model;             (* current partial model *)
     mutable watch : tw_el VMap.t;   (* all non-unit clauses clauses where lit occurs *)
     mutable trail : var_model_val list; 
     mutable up_queue : clause LMap.t; (* propagation queue: lit -> implication clause *)
     mutable var_queue : var_priority_queue; (* not decided yet *)	
     mutable dlevel : int;
     mutable var_score_map : var_score_map;
     mutable reset_conflict_bound : int;
     mutable stats : stats;
     mutable phase_saving : bool VMap.t;
     mutable phase_count_map : var_phase_count VMap.t; (* max trail distance reached with this phase *)
   } 

(*----- init_sate --------*)
      
let init_dpll_state () = 
  {
   input_clauses = [];
   all_clauses = CSet.empty;
   model = create_model ();  

   trail = [];
   watch = VMap.empty; 
   up_queue = LMap.empty; (*TODO: change to just lit set *)
   var_queue = create_var_priority_queue (); 
   dlevel = 0;
   var_score_map = create_var_score_map ();
   reset_conflict_bound = 0;
   stats = init_stats ();

   
   phase_saving = VMap.empty;
   phase_count_map = VMap.empty;
 }


let	var_phase_incr var_val var incr phase_count_map =
  try 
    let vp_count = VMap.find var phase_count_map in 
    let new_vp_count = 
      if var_val 
      then 
	{vp_count with vp_pos = vp_count.vp_pos + incr}
      else
	{vp_count with vp_neg = vp_count.vp_neg + incr}
    in
    VMap.add var new_vp_count phase_count_map
  with 
    Not_found -> 
      let new_vp_count = 
	if var_val 
	then 
	  {vp_pos = incr; vp_neg = 0}
	else
	  {vp_pos = 0; vp_neg = incr}
      in
      VMap.add var new_vp_count phase_count_map


(*-------- up_queue --------*)
	
let add_up_queue state lit impl_clause = 
  let better_impl_clause c1 c2 = (* true c1 is better impl. clause than c2*)
    (List.length (clause_get_lits c1)) < (List.length (clause_get_lits c2))  (* TODO exp. with decision level *)
  in
  
  let up_queue = state.up_queue in
  try
    let old_impl = LMap.find lit up_queue in 
    if (better_impl_clause impl_clause old_impl) 
    then
      (
       dbg D_upq (lazy ("new_better_impl: "^(lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
       let new_up_queue = LMap.add lit impl_clause up_queue in 
       state.up_queue <- new_up_queue
      )
    else
      (
       dbg D_upq (lazy ("old_better_impl: "^(lit_to_string lit)^" : "^(clause_to_string old_impl)));  	
      )
  with 
    Not_found -> 
      (
       let new_up_queue = LMap.add lit impl_clause up_queue in 
       dbg D_upq (lazy ("new:"^(lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
       state.up_queue <- new_up_queue
      )


(*--------------------------*)
exception UPQ_Empty


let remove_max_up_queue state = 
  try
    let (lit, impl_clause) =  LMap.max_binding state.up_queue in
    dbg D_upq (lazy ("max: "^(lit_to_string lit)^" : "^(clause_to_string impl_clause)));  
    state.up_queue <- LMap.remove lit state.up_queue;
    (lit,impl_clause)
  with 
    Not_found -> raise UPQ_Empty


let in_up_queue up_queue lit = 
  LMap.mem lit up_queue

let remove_up_queue state lit = 
  state.up_queue <- LMap.remove lit state.up_queue 

(*----------*)
let out_up_queue state =       
  let f lit impl_clause = 
    out_str ((lit_to_string lit)^" <- "^(clause_to_string impl_clause));
  in     
  out_str ("------ up queue -------");
  LMap.iter f state.up_queue;
  out_str ("------ end up queue ---")


(*---------- adding/removing clauses ----*)
    
    
(*----------  DPLL two watch invariants: --------*)
(* 1. --t--f/t/u  if true lit is watch and the other watch is on a later or equal dlevel then the other watch can have any value *)
(* 2. ffft if true lit is in the current level and all others are false (this lit is obtained by UP) then  *)
(*    the other watch should be lit the highest dlevel (or trail level). *)
(* 3. if first watch is undef then a) try to find the other undef, otherwise  UP is applicable followed by 2. *)
(* 4. conflict two watches should be at the highest d level possible. *)
(* 5. first watch should be either true or undef otherwise either 4. or 2. is applicable. *)


let find_watch_lit_list model lit_list =
  (* TODO change to better choices *)
  let cmp l1 l2 = 
    (*let (_pol1,v1) = lit_to_var l1 in
      let (_pol2,v2) = lit_to_var l2 in
      let var_model_val_1 = VMap.find v1 model in 
      let var_model_val_2 = VMap.find v2 model in 
     *)
    match ((check_model model l1), (check_model model l2)) with 
    |(M_True _, M_False _)  
    |(M_True _, M_Undef) 
    |(M_Undef, M_False _) -> 1
    |(M_True val_1, M_True val_2) ->  -(Pervasives.compare val_1.var_dlevel val_2.var_dlevel) (* get lowest dl*)
    |(M_False val_1, M_False val_2) -> (Pervasives.compare val_1.var_dlevel val_2.var_dlevel) (* get highest dl*)
    |(M_Undef, M_Undef) -> 0      
    |_-> -1 
  in
  assert (lit_list != []);

  let watch_lit = list_find_max_element cmp lit_list in
  watch_lit 

type watch_res = 
  |W_Normal of lit * lit 
  |W_Conflict
  |W_Implied of lit * lit (* first lit is implied and second is at the same dlevel *)

let find_watch_clause model c = 
  let lits = clause_get_lits c in
  let w1 = find_watch_lit_list model lits in 
  let new_list = List.filter (fun x -> not (x==w1)) lits in 
  let w2 = find_watch_lit_list model new_list in
  match ((check_model model w1), (check_model model w2))with 
  |(M_True _, _)  
  |(M_Undef, M_Undef) -> W_Normal (w1,w2)
  |(M_False _, _) -> W_Conflict
  |(M_Undef, M_False _) -> W_Implied (w1,w2) 
  |(M_Undef,M_True _) -> failwith "find_watch_clause: should not happen"

	
let add_watch dpll_state other_w l c =       
  let (pol,var) = lit_to_var l in
  let watch = dpll_state.watch in
  let tw_el =
    try  
      VMap.find var watch 
    with 
      Not_found -> 
	{
	 tw_var = var;
	 tw_pos = CMap.empty;
	 tw_neg = CMap.empty;
       }
  in 
  (
   if pol 
   then 
     (
      dbg D_tw (lazy ("c: "^(clause_to_string c)
		      ^" pos: "^(lit_to_string l)
		      ^(" o: ")^(lit_to_string other_w)));
      
      tw_el.tw_pos <- CMap.add c other_w tw_el.tw_pos
     )
   else
     (
      dbg D_tw (lazy ("c: "^(clause_to_string c)
		      ^" neg: "^(lit_to_string l)
		      ^(" o: ")^(lit_to_string other_w)));

      tw_el.tw_neg <- CMap.add c other_w tw_el.tw_neg
     )	 
  );
  dpll_state.watch <- VMap.add var tw_el watch


let remove_watch dpll_state l c = 
  dbg D_tw (lazy ("rm c: "^(clause_to_string c)^" l: "^(lit_to_string l)));

  let (pol,var) = lit_to_var l in
  let watch = dpll_state.watch in
  try
    let tw_el =
      VMap.find var watch 
    in
    (
     if pol 
     then 
       (
	tw_el.tw_pos <- CMap.remove c tw_el.tw_pos
       )
     else
       (
	tw_el.tw_neg <- CMap.remove c tw_el.tw_neg
       )
    );
    if (tw_el.tw_pos = CMap.empty && tw_el.tw_neg = CMap.empty)
    then
      (
       dpll_state.watch <- VMap.remove var watch 
      )
    else 
      ()
  with Not_found -> ()
      
      

(*-----------------------------*)
(*
  let add_clause_to_watch up_queue smp_watch c = 
  let (new_smp_watch, _plcs) = smp_modif_watch CSet.add up_queue smp_watch c in
  new_smp_watch
 *)	


let extend_state_var state var var_model_val = 
  dbg D_ext_state (lazy (var_model_val_to_string var_model_val));

(* add to model *)
  state.model <- add_to_model state.model var var_model_val;
  
(* add to trail *)
  state.trail <- var_model_val::state.trail;

  state.var_queue <- remove_var_pq state.var_queue var;
  dbg D_trail (lazy ("add:"^(var_model_val_to_string var_model_val)));

(* save phase *)
  state.phase_saving <-  VMap.add var_model_val.var var_model_val.var_val state.phase_saving;

  state.phase_count_map <- var_phase_incr var_model_val.var_val var_model_val.var 1 state.phase_count_map;
  
  state.phase_saving <- VMap.add var_model_val.var var_model_val.var_val state.phase_saving;

(* if implied add to up queue *)
  (match var_model_val.var_impl_type with 
  |Implied c -> (add_up_queue state (var_to_lit  var_model_val.var_val var_model_val.var) c)
  |_->()
  )

    
    
(*--------------*)
exception Conflict of clause

let find_add_watch_pair state c =       
  match (find_watch_clause state.model c) with 
  |W_Normal (w1,w2) -> 
      dbg D_tw (lazy ("add normal: "^(lit_to_string w1)^" : "^(lit_to_string w2)));

      add_watch state w1 w2 c;
      add_watch state w2 w1 c
	
  |W_Implied (w1,w2) ->  
(*      dbg D_tw (lazy ("add implied: "^(lit_to_string w1)^" : "^(lit_to_string w2))); *)
      dbg D_implied (lazy ((lit_to_string w1)^" <- "^(clause_to_string c)));
      add_watch state w1 w2 c;
      add_watch state w2 w1 c;   
      let (pol,var) = lit_to_var w1 in
      let var_model_val = 
	{
	 var = var;
	 var_val = pol;
	 var_impl_type = Implied (c);
	 var_dlevel = state.dlevel;
       } 
      in
      extend_state_var state var var_model_val
(*	  (add_up_queue state w1 c)*)

  |W_Conflict -> 
(*      dbg D_tw (lazy ("add conflict: "^(clause_to_string c))); *)
      dbg D_conflict (lazy (clause_to_string c));
      raise (Conflict (c))


let remove_watch_pair state (w1,w2) c = 
  dbg D_tw (lazy ("remove: "^(lit_to_string w1)^", "^(lit_to_string w2)));
  remove_watch state w1 c;
  remove_watch state w2 c
    

(*--------------*)
    
let add_clause state c = 
(*
  if  (CSet.mem c state.all_clauses)
  then 
  ()
  else      
 *)
  begin

    
    let lits = clause_get_lits c in       
    match lits with
    |[] ->
	raise (Unsatisfiable (c)) (* can only happen with the empty clause derived at the top level *)
	  
    |[lit] -> 
	(
	 dbg D_add_clause (lazy ("unit: "^(clause_to_string c)));  
	 let (pol,var) = lit_to_var lit in
	 match (check_model state.model lit) with  (* change to keep unit literal rather than implied by non-unit *)
	 | M_True _ -> ()
	 | M_False _ -> raise (Conflict c)
	 | M_Undef -> 
	     let var_model_val = 
	       {
		var = var;
		var_val = pol;
		var_impl_type = Implied (c);
		var_dlevel = 0; (* unt clauses are of level 0 *)
	      } 
	     in		   
	     extend_state_var state var var_model_val;
	     state.all_clauses <- CSet.add c state.all_clauses;	       
	)
	  
    |_non_unit ->
	(
	 dbg D_add_clause (lazy (clause_to_string c));  
	 find_add_watch_pair state c;    (* can raise Conflict *)
	 state.all_clauses <- CSet.add c state.all_clauses;
	)
  end

(* TODO: extend with counters to avoid cardinal *)
let get_tw_el_size pol tw_el = 
  if pol 
  then 
    CMap.cardinal tw_el.tw_pos
  else 
    CMap.cardinal tw_el.tw_neg
      
(*-----------------------------*)
(* later: incr decision level; add to trail *)
let decide state =       
  let is_undecided v = 
    not (in_model state.model v) (* && (VMap.mem v state.watch) *) (* TODO: fixme *)
  in	
  let rec get_undecided_var var_queue = 
    let (var,var_priority,new_var_queue) = 
      try
	remove_max_var_pq var_queue 
      with 
	Not_found ->
	  raise (Satisfiable (state.model))	
    in 
    if (is_undecided var)
    then
      (var, var_priority, new_var_queue)
    else
      get_undecided_var new_var_queue
  in

  let (d_var,d_priority,new_var_queue) = get_undecided_var state.var_queue in
  
(* decide polatiry based on a heirustic *)
  let get_d_pol state var = (*false in *)

(*   *)
(*
  try 
  let phase_count = VMap.find var state.phase_count_map in 
  phase_count.vp_pos > phase_count.vp_neg 
  with
  Not_found ->
 *)
    begin
      
(* try phase *)
      try 
	VMap.find var state.phase_saving 
      with 
	Not_found -> 
	  
	  (* as a heiristic get polarity which will make true more clauses *)
	  let watch = VMap.find var state.watch in
	  let pos_w_size = get_tw_el_size true watch in
	  let neg_w_size = get_tw_el_size false watch in
	  if pos_w_size >= neg_w_size 
	  then
	    true 
	  else 
	    false 

    end	  
  in  
  let d_pol = get_d_pol state d_var in
  let d_lit = var_to_lit d_pol d_var in
  state.var_queue <- new_var_queue;
  
  state.dlevel <- state.dlevel +1;
  
(*  dbg D_decide (lazy ((lit_to_string d_lit)^" p: "^(string_of_int d_priority)^" d: "^(string_of_int state.dlevel))); *)
  
  dbg D_decide (lazy ("l: "^(lit_to_string d_lit)^" dlevel: "^(string_of_int state.dlevel)));
  state.stats.num_decisions <-  state.stats.num_decisions + 1;

  (d_var, d_pol, d_priority)    
    


(* ------------------------------ *)
(* --- can raise Conflict (c) --- *)
(* --- can extend up queue ------ *)


let unit_propagate state lit =

  dbg D_up (lazy (lit_to_string lit));

  state.stats.num_propagations <- state.stats.num_propagations +1;

  let (pol,var) = lit_to_var lit in	
  (*let var_model_val = VMap.find var state.smp_model in*)

  try 
    let watch = VMap.find var state.watch in		
    
    let to_reassign_watch =
      if pol
      then
    	(
	 watch.tw_neg 
	)
      else 
	(
    	 watch.tw_pos
	)
    in
    let compl_lit = compl_lit lit in 
    let reassign c other_watch = 
      match (check_model state.model other_watch) with 
      |M_True (_) -> ()
      |M_False (_) | M_Undef ->
	  (
	   remove_watch_pair state (compl_lit,other_watch) c;
	   find_add_watch_pair state c 	     
	  )
    in 
    CMap.iter reassign to_reassign_watch

  with 
    Not_found -> 
      (
       dbg D_up (lazy ("watch not found: "^(var_to_string var)));
      ) (* not watched *)


(*--------------*)

type lid = lit * var_impl_type * int
      
let get_lid state lit = 
  let (_pol,var) = lit_to_var lit in      
  assert (in_model state.model var);
  let var_model_val = find_model state.model var in 
  (lit, var_model_val.var_impl_type, var_model_val.var_dlevel)
    

let get_lid_lits state lit_list = 
  List.map (get_lid state) lit_list 


(* Decided < Implied  *)
let cmp_var_type t1 t2 = 
  match (t1, t2) with 
  |(Decided, Implied _) -> -1
  |(Implied _, Decided)  -> 1
  | _ ->  0 

let is_decided t =  (match t with Decided -> true | _-> false)
let is_implied t =  (match t with Implied _ -> true | _-> false)

(* when we sort in asceding order we would have: [(l_dec, max); (l'_impl,max);...;(l_dec_min,min);...;(l'_impl,min)] *)
let cmp_lid (l1,i1,d1) (l2,i2,d2) =       
  if (d1 = d2)
  then 
    cmp_var_type i1 i2 
  else
    -(Pervasives.compare d1 d2)
      
(* returns (lit, max_dlevel) *)
let get_max_dlevel dlevel_lit_list =           
  list_find_max_element cmp_lid dlevel_lit_list

let sort_lid_lit_list lid_list =      
  List.sort cmp_lid lid_list

    (*-------------*)
let rec cancel_until state dlevel = 
  dbg D_cancel_until (lazy ("dlevel: "^(string_of_int dlevel)^" current dlevel: "^(string_of_int state.dlevel)));
  match state.trail with 
  | var_model_val :: tl -> 	 
      state.dlevel <- var_model_val.var_dlevel;	    
      dbg D_trace (lazy ("new state dlevel: "^(string_of_int state.dlevel)));
      if state.dlevel = dlevel 
      then (dbg D_trace (lazy ("cancel_until finished")))
      else 
	begin
	  let lit = var_to_lit var_model_val.var_val var_model_val.var in
	  dbg D_trail (lazy ("rm: l: "^(lit_to_string lit)));
	  let var = var_model_val.var in
	  state.trail <- tl; (* remove from trail *)
	  state.model <- remove_model state.model var; 	 (* remove from model *)
	  remove_up_queue state lit; (* remove from up queue *)
	  let new_var_priority = 
	    try
	      get_var_score var state.var_score_map 
	    with 
	      Not_found -> 
		(
		 dbg D_trace (lazy ("get_var_score Not_found: v: "^(var_to_string var) ));

		 let score = 1 in 
		 let new_score_map = incr_var_score var score state.var_score_map in 
		 state.var_score_map <- new_score_map;
		 score
		)
	  in 
          (* TODO try max watch ? to look at score map *)
	  (if (mem_pq state.var_queue var) 
	  then
	    state.var_queue <- remove_var_pq state.var_queue var
	  );	
          state.var_queue <- add_var_pq new_var_priority var state.var_queue;    (* add to var queue *)		
	  cancel_until state dlevel
	end 
  |[] -> (state.dlevel <- 0;
          dbg D_cancel_until (lazy ("current dlevel: "^(string_of_int state.dlevel)))
         )


(*
  let rec add_parents state c = 
  let parents = 
  match c.parents with 
  P_Input -> []
  | P_BRes (_l, c1, c2) ->  [c1;c2]
  | P_URes _-> [(get_implying c)] (* implying clause *)
  | P_HRes hparents ->  hparents (* hyper resolution *) 
  in
  List.iter (add_clause state) parents;
  List.iter (add_parents state) parents
 *)

(* uil-- unique implication literal *)
(* returns new conflict such that a compl. of a previous decision literal is implied *)

let rec analyse_conflict_uil state c =    
  dbg D_conflict (lazy ("analyse_uil: "^(clause_to_string c)));

  let lit_list = clause_get_lits c in 
  let dlevel_lit_list = sort_lid_lit_list (get_lid_lits state lit_list) in

  match dlevel_lit_list with 
  |(l1, i1, d1)::(l2, i2, d2)::tl -> 

      if (d1 = d2)
      then 
	(
	 assert (is_implied i2);
	 
	 let (pol,var) = lit_to_var l2 in    
	 assert (in_model state.model var);
	 let var_model_val = find_model state.model var in 
	 let new_conflict = resolve_model var_model_val c in

	 state.var_score_map <- incr_var_score var 1 state.var_score_map;
	 analyse_conflict_uil state new_conflict
	)
      else
	(
	 assert (d1 > d2);
	 cancel_until state d2;

(* change score map *)
(*
  let lit_list = clause_get_lits c in 
  let var_score_fun score_map lit = 	
  let (_pol,var) = lit_to_var lit in 
  incr_var_score var 1 score_map 
  in
  let new_var_score_map = List.fold_left var_score_fun state.var_score_map lit_list in 
  state.var_score_map <- new_var_score_map;

 *)
(* very bad 
   let add_parents_flag = true in

   if add_parents_flag then add_parents state c;
 *)
         dbg D_lemma (lazy (clause_to_string c));
	 add_clause state c
	)

  |[(l, i, d)] -> (* c is unit clause *)
      begin
	cancel_until state 0; 
	try
          dbg D_lemma (lazy (clause_to_string c));
	  add_clause state c 
	with 
	  Conflict d ->

            assert (c==d);
	    dbg D_conflict (lazy ("analyse_conflic_uil unit c: "
			       ^(clause_to_string c)));
	    let (pol,var) = lit_to_var l in    
	    assert (in_model state.model var);
	    let var_model_val = find_model state.model var in 
	    let new_conflict = unit_resolve_model var_model_val c in
	    assert ((clause_get_lits new_conflict)=[]); (* empty clause *)
	    raise (Unsatisfiable (new_conflict))
      end
  |[] -> (* c is empty clause *) 	
      raise (Unsatisfiable (c))
	

(* analyse until all lits in the conflict are decided *)



let analyse_conflict_dec state c =

  dbg D_trace (lazy ("analyse_conflict_dec: "^(clause_to_string c)));

  let conflict = hyper_resolve_until_decided state.model c in 

  dbg D_trace (lazy ("analyse_conflict_dec: decided conflict: "^(clause_to_string conflict)));
  
  let lit_list = clause_get_lits conflict in 

(* change score map *)
  let var_score_fun score_map lit = 	
    let (_pol,var) = lit_to_var lit in 
    incr_var_score var 1 score_map 
  in
  let new_var_score_map = List.fold_left var_score_fun state.var_score_map lit_list in 
  state.var_score_map <- new_var_score_map;

  let dlevel_lit_list = sort_lid_lit_list (get_lid_lits state lit_list) in
  match dlevel_lit_list with 
  |(l1, i1, d1)::(l2, i2, d2)::tl -> 
      assert (d1 > d2); 
      assert (is_decided i1);
      assert (is_decided i2);
      cancel_until state d2;
      add_clause state conflict
  |[(l, i, d)] -> (* co is unit clause *)
      begin
	cancel_until state 0; 
	try
	  add_clause state conflict 
	with 
	  Conflict d ->
	    dbg D_trace 
	      (lazy ("analyse_conflic_dec unit c: "^
		     (clause_to_string conflict)^" Conflict d:"^(clause_to_string d)));
	    let (pol,var) = lit_to_var l in    
	    assert (in_model state.model var);
	    let var_model_val = find_model state.model var in 
	    let new_conflict = unit_resolve_model var_model_val conflict in
	    assert ((clause_get_lits new_conflict)=[]); (* empty clause *)
	    raise (Unsatisfiable (new_conflict))
      end
  |[] -> (* c is empty clause *) 	
      raise (Unsatisfiable (conflict))

(*-------------------------*)

let analyse_conflict state c  = 
  state.stats.num_conflicts <- state.stats.num_conflicts + 1;
(*--- UIL version----*)
  analyse_conflict_uil state c 

(*
  ............ OLD .............

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
 *)	


(*----- fill_priority after first unit propagation -----*)	  

let init_fill_priority state = 
  let f var tw_el =
    let max_size = 
      list_find_max_element compare 
	[(CMap.cardinal tw_el.tw_pos);(CMap.cardinal tw_el.tw_neg)]
    in
(*	state.var_score_map <- incr_var_score var max_size state.var_score_map; *)
    state.var_queue <- add_var_pq max_size var state.var_queue
  in
  VMap.iter f state.watch 

let score_fill_priority_queue score_map state = 
  let f var _tw = 
    let score =
      try
	get_var_score var state.var_score_map 
      with 
	Not_found -> 
	  (
	   dbg D_trace (lazy ("get_var_score Not_found: v: "^(var_to_string var) ));
	   let score = 1 in 
	   let new_score_map = incr_var_score var score state.var_score_map in 
	   state.var_score_map <- new_score_map;
	   score
	  )
    in
    state.var_queue <- add_var_pq score var state.var_queue
  in
  VMap.iter f state.watch 

(*-- init clist --*)
let add_clauses_dpll_state state clist = 
  try 
    let f c = 
      if (not (is_tautology c))
      then
	(add_clause state c)
      else
	()
    in
    List.iter f clist
  with 
  | Conflict (c) ->  (* to level conflict *)
      analyse_conflict state c (* always returns Unsatisfieble c with  empty clause *)

(*-------- Reset -----------*)

exception Reset of dpll_state

let check_reset old_state = 

  if (old_state.stats.num_conflicts > old_state.reset_conflict_bound) 
  then 
    begin
      let state =  init_dpll_state () in  

      state.stats <- old_state.stats;

      state.reset_conflict_bound <- 
(*old_state.stats.num_conflicts + (List.length old_state.input_clauses);*) 
	2 * (old_state.reset_conflict_bound +1);  (* (CSet.cardinal old_state.all_clauses);*)

      state.phase_count_map <- old_state.phase_count_map; 

(*	  state.phase_saving <- old_state.phase_saving; *) (* phase reset to empty *)

(* reset score to phase count *) (* worse *)
(*
  let f v vp_count = 
  let new_score = vp_count.vp_pos + vp_count.vp_neg in 	     
  state.var_score_map <- VMap.add v new_score state.var_score_map
  in
  VMap.iter f state.phase_count_map;
 *)

(*
  state.var_score_map <- old_state.var_score_map; (* keep score map *) (* should it be scaled ? /10 ? *)
 *)	 
(*
  let f v old_score = 
  let new_score = old_score/10 in 	     
  state.var_score_map <- VMap.add v new_score state.var_score_map
  in
  VMap.iter f old_state.var_score_map;
 *)
      let f old_score = old_score/10 in
      state.var_score_map <- unpdate_all_vars_score f state.var_score_map;

      let keep_clause c = 
	(
	 match (get_parents c) with 
	 |P_Input -> true
	 |_->  (List.length (clause_get_lits c)) < 15
	) 
      in 
      let new_input_clauses = CSet.elements (CSet.filter keep_clause old_state.all_clauses) in 

      add_clauses_dpll_state state new_input_clauses;

      state.input_clauses <- old_state.input_clauses; 

(*	  add_clauses_dpll_state state old_state.input_clauses; *)
(*	  state.input_clauses <- old_state.input_clauses; *)

      score_fill_priority_queue state.var_score_map state;

(* TODO move iter to prop_env *)
(*
   dbg_env D_reset
   (fun () -> 
   out_str "\n---------Reset New Priorities:------- \n";
   let f pr _ = 
   out_str (string_of_int  pr)
   in 
   IntMap.iter f state.var_queue.pr_to_v;	 
   let g v pr = 
   out_str ("v: "^(var_to_string v)^" p: "^(string_of_int  pr));
   in 
   VMap.iter g state.var_queue.v_to_pr;
   out_str "\n--------- end Priorities:------- \n";
   );
 *)
      out_str "\n\n-------- Reset --------\n\n";
      out_stats state.stats;
      raise (Reset (state))
    end

(*---------In progress----------*)
      
let rec dpll state = 
  try
    check_reset state; 
    begin
      try (* unit propagation *)
	while true 
	do
	  
	  let (lit, impl_clause) =  remove_max_up_queue state in 
	  
	  dbg D_up (lazy ((lit_to_string lit)^" <- "^(clause_to_string impl_clause)));
	  
	  assert (is_true_model state.model lit);
	  unit_propagate state lit 
	    
	done	   
      with
      |UPQ_Empty ->  (* all propagated *)
	  begin (*assume all lit are propagated *)	 	    
	    let (d_var, d_pol, d_priority) = decide state in (* can raise Satisfiable *)
(*	    let lit = var_to_lit d_pol d_var in*)
	    let var_model_val = 
	      {
	       var = d_var;
	       var_val = d_pol;
	       var_impl_type = Decided;
	       var_dlevel = state.dlevel; (* changed by decide *)
	     }	  
	    in
	    extend_state_var state d_var var_model_val;
	    let lit = var_to_lit d_pol d_var in
	    unit_propagate state lit; 
	    dpll state
	  end
    end
  with
  |Conflict c ->
      (
       analyse_conflict state c; 
       add_clause state c;
       dpll state
      ) 	    
	
  | Reset res_state -> dpll res_state
	



(*-------------*)
let dpll_imp_run_stdin () =
  let state =  init_dpll_state () in  
  try
    begin

      let input_clauses = List.sort clause_cmp_length (dimacs_stdin ()) in	  
      
      dbg_env D_preprocess 
        (fun () -> 
         ( out_str "\n";
          out_str "----------- input clauses ------------\n";
          out_str (clause_list_to_string input_clauses);
          out_str "--------------------------------------\n";
          )
        );

      state.stats.num_input_clauses <- List.length input_clauses;
      
      state.reset_conflict_bound <-  state.stats.num_input_clauses; 

      state.input_clauses <- input_clauses;
      add_clauses_dpll_state state input_clauses;
      
      init_fill_priority state;
(*
  out_str ("smp_state unit clauses: \n ");
  out_up_clauses smp_state;
  out_str ("smp_state clauses: \n ");
 *)
(*      out_clauses smp_state; *)
      
      out_str (pref_str^"Solving...");
      
      ignore(dpll state);
    end
  with 
    Satisfiable (model) -> 
      (
       out_str "\n";
       out_str "SATISFIABLE\n";
       out_stats state.stats;
       out_model model;  (* commented for gorilla *)
      )
  |Unsatisfiable c -> 
      (
       out_str "\n";
       out_str "UNSATISFIABLE\n";
       out_stats state.stats;
      )

  | Termination_Signal -> 
      out_str ("\n\n User Terminated\n\n");
      out_stats state.stats;
      exit 1;
  | x ->
      (
       out_stats state.stats;
       if dbg_flag then
	 Format.eprintf "Unexpected error after main.Backtrace:@\n%s@\n@." (Printexc.get_backtrace ());	    
       raise x
      )
	



let _ = dpll_imp_run_stdin ()
