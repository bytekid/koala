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
open Instantiation_env


(*----- debug modifiable part-----*)

let dbg_flag = false

(*-------- switching off all redundancies-----*)
let dbg_inst_no_redund = false

let _ = if dbg_inst_no_redund then (out_warning " dbg_inst_no_redund \n\n ")

type dbg_gr = 
  |D_inst
  |D_inst_tmp
  |D_res
  |D_bmc1_merge_next
  |D_unflat
  |D_dom_inst

let dbg_gr_to_str = function 
  | D_bmc1_merge_next -> "bmc1_merge_next_func"
  | D_res -> "res"
  | D_inst_tmp -> "inst_tmp"
  | D_inst -> "inst"
  | D_unflat -> "unflat"
  | D_dom_inst -> "dom_inst"

let dbg_groups =
  [
(*
   D_bmc1_merge_next;
   D_res;
   D_inst;
*)
(*   D_inst_tmp;*)
(*   D_unflat; *)
(*   D_dom_inst *)
  D_inst;
  D_inst_tmp;

 ]
    
let module_name = "inference_rules"

(*----- debug fixed part --------*)


(*----- debug fixed part --------*)
    
let () = dbg_flag_msg dbg_flag module_name
    
let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy
    
let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)

    
(*
  type  statistics = 
  {num_of_dismatch_blockings : int;
  num_of_non_proper_inst    : int }
 *)

(*
  let num_of_dismatch_blockings = ref 0 
  let num_of_non_proper_inst = ref 0
  let num_of_duplicates = ref 0
 *)


(*----------------Subset Subs. used in subsumption resolution ----------*)

(* we assume that to_subs_clause has defined length *)
(* and by_clause does not, but all lits a are in    *)

let rec strict_subset_subsume_lits by_lits to_lits = 
  match by_lits with 
  |h::tl -> 
      if  (List.exists (function l -> h == l) to_lits) 
      then strict_subset_subsume_lits tl to_lits
      else false
  |[] -> true 

let strict_subset_subsume by_clause to_clause = 
  let by_lits = Clause.get_literals by_clause in
  if (List.length by_lits) < (Clause.length to_clause)
  then 
    (let to_lits = Clause.get_literals to_clause in
    strict_subset_subsume_lits by_lits to_lits)
  else
    false

exception Main_subsumed_by of clause

(* resolution, factoring can raise  Unif.Unification_failed *)
(* resolution can raise Main_subsumed_by*)

(* literals l1 l2 are in c1 and c2 *)
let resolution c1 l1 c_list2 l2 (* term_db_ref *) = 
  let compl_l1 = add_compl_lit l1 in
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  let new_litlist1 = 
    Clause.find_all (fun lit -> not(l1 == lit)) c1 
  in 
  let f rest c2 = 
(*    check_disc_time_limit (); *)
    let new_litlist2 = 
      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 

    dbg D_res ( lazy ("-----------------------------"));
    dbg D_res ( lazy ("main: "^(Clause.to_string c1)));
    dbg D_res ( lazy ("main sel: "^(Term.to_string l1)));
    dbg D_res ( lazy ("side: "^(Clause.to_string c2)));
    dbg D_res ( lazy ("side sel: "^(Term.to_string l2)));
    let tstp_source = Clause.tstp_source_resolution [c1;c2] [l1;l2] in  
    let conclusion = 
      create_clause tstp_source 
	(normalise_blitlist_list 
	   mgu [(1,new_litlist1);(2,new_litlist2)]) in
    Clause.assign_ps_when_born_concl ~prem1:[c1] ~prem2:[c2] ~c:conclusion;

    dbg D_res ( lazy ("conl: "^(Clause.to_string conclusion)));
    dbg D_res ( lazy ("-----------------------------"));

    (*   let min_conj_dist = Clause.get_min_conjecture_distance [c1;c2] in
	 Clause.assign_conjecture_distance (min_conj_dist+1) conclusion; 
     *) 
    (if !current_options.res_forward_subs_resolution 
    then
      if (strict_subset_subsume conclusion c1)
      then 
	(
         dbg D_res ( lazy ("main subsumed by concl"));
(*	 clause_register_subsumed_by ~by:conclusion c1; *)
	 raise (Main_subsumed_by conclusion))
      else ()
    else ()      
    );
(*
    (if !current_options.res_backward_subs_resolution
    then
      if (strict_subset_subsume conclusion c2)
      then 
	(
(*	 clause_register_subsumed_by ~by:conclusion c2; *)
	)
      else ()
    else ()
    );      
*)
    conclusion::rest  in 
  List.fold_left f [] c_list2     


(* the result of subs_resolution is the list of resolvents subsuming 
   one of the side premises; subsumed side premises are assigned Clause.is_dead *)

let subs_resolution c1 l1 c_list2 l2 (* term_db_ref *) = 
  let compl_l1 = add_compl_lit l1 in
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  let new_litlist1 = 
    Clause.find_all (fun lit -> not(l1 == lit)) c1 
  in 
  let f rest c2 = 
    let new_litlist2 = 
      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 
    
    let tstp_source = Clause.tstp_source_resolution [c1;c2] [l1;l2] in  
    let conclusion = 
      create_clause tstp_source 
	(normalise_blitlist_list 
	   mgu [(1,new_litlist1);(2,new_litlist2)]) in
    
    Clause.assign_ps_when_born_concl ~prem1:[c1] ~prem2:[c2] ~c:conclusion;		
    
    (* let min_conj_dist = Clause.get_min_conjecture_distance [c1;c2] in
       Clause.assign_conjecture_distance (min_conj_dist+1) conclusion;*)
    (if !current_options.res_forward_subs_resolution  
    then
      if (strict_subset_subsume conclusion c1)
      then 
  	(
(*	 clause_register_subsumed_by ~by:conclusion c1; *)
	 raise (Main_subsumed_by conclusion)
	)
      else ()
    else ()      
    );
    let subsuming_clauses = 
      if !current_options.res_forward_subs_resolution
      then
	if (strict_subset_subsume conclusion c2)
	then 
	  (
(*           clause_register_subsumed_by ~by:conclusion c2; *)
	   [conclusion])
	else []
      else []
    in      
    subsuming_clauses@rest  in 
  List.fold_left f [] c_list2     




(* factors and removes all  repeated l1's in the clause *)
let factoring c l1 l2 (* term_db_ref *) =
  let tstp_source = Clause.tstp_source_factoring c [l1;l2] in
  if l1==l2 then 
    let new_litlist = 
      l1::(Clause.find_all (fun lit -> not(l1 == lit)) c) in			
    let conclusion = 
      create_clause tstp_source new_litlist in
    Clause.assign_ps_when_born_concl ~prem1:[c] ~prem2:[] ~c:conclusion;
    (* simplified *)
(*    clause_register_subsumed_by ~by:conclusion c; *)
    conclusion
  else    
    let mgu =  Unif.unify_bterms (1,l1) (1,l2) in
    let new_litlist = 
      Clause.find_all (fun lit -> not(l1 == lit)) c
    in
    let conclusion = 
      create_clause tstp_source (Clause.normalise_b_litlist term_db_ref mgu (1,new_litlist)	) in
    Clause.assign_ps_when_born_concl ~prem1:[c] ~prem2:[] ~c:conclusion;
    conclusion


(*-------------------- tautology delition--------------------*)
	
(*
let rec coml_in_list lit_list =
  match lit_list with
  | l:: tl ->
      let exists = List.exists (Term.is_complementary l) tl in
      if exists then exists
      else coml_in_list tl
  |[] -> false
*)


let compl_in_list lit_list =
  let (neg_lits, pos_lits) = List.partition (Term.is_neg_lit) lit_list in 
  let pos_lit_set = Term.term_list_to_set pos_lits in 
  let f neg_lit = 
    let atom = Term.get_atom neg_lit in 
    TSet.mem atom pos_lit_set
  in 
  List.exists f neg_lits

let is_tautology clause =
  let lit_list = Clause.get_literals clause in
  if (compl_in_list lit_list) 
  then
    (
(*     Clause.assign_replaced_by (Def(Clause.RB_tautology_elim)) clause; *)
     true
    )
  else 
    false
	  

(* can not use eq_tautology elim with axiomtic equality ! only  in preprocessing before eq axioms are added *)
let is_eq_tautology clause = 

  let lit_list = Clause.get_literals clause in 
  let f lit = 
    match (term_eq_view_type_term lit) with    (* matches only when lit is positive *)
    |Def(Eq_type_term (_, t, s)) -> t == s
    |Undef -> false
  in
  let is_eq_tautology = List.exists f lit_list in 
  if is_eq_tautology
  then
      (
(*       Clause.assign_replaced_by (Def(Clause.RB_tautology_elim)) clause; *)
       true
      )
  else 
    false


  
(*-----equality resolution simplification---------*)


(* One should be careful since in general x!=t \/ C [x] => C[t] *)
(* is not a vaild simplification since eq is not built in and therefore *)
(* congurence axioms x!=y \/ ~P(x) \/ P(y) would be simplified into tautologies! *)

(* we restrict to a simple case when *)
(* t!=t \/ C => C*)

let is_trivial_diseq_lit lit =  
  if (Term.is_neg_lit lit) 
  then
    let atom = Term.get_atom lit in  
    match (term_eq_view_type_term atom) with 
    | Def(Eq_type_term(_eq_type_term, t,s)) -> 
	t == s
    | Undef -> false
  else 
    false

(* if not simplified the clause remains the same and not otherwise *)		
let equality_resolution_simp c = 
  if (Clause.has_eq_lit c)
  then
    let lits = get_lits c in
    let new_lits = 
      List.find_all (fun l -> (not (is_trivial_diseq_lit l))) lits in 
    if ((List.length lits) = (List.length new_lits))
    then c 
    else 
      (
       let tstp_source = Clause.TSTP_inference_record (Clause.Eq_res_simp, [c]) in	
       let new_clause = create_clause tstp_source new_lits in 
(*       clause_register_subsumed_by ~by: new_clause c; *)
       Clause.assign_ps_when_born_concl ~prem1:[c] ~prem2:[] ~c:new_clause;		
       new_clause
      )
  else 
    (c)
      
      


(*-----------------------------------------------------------------*)
(*-- unflatting: x!=t\/ C[x,y] -> C[t,s] where x not in t ---------*)
(*-- 1) collect diequalities {x_i!=t_i}; unify {x_1 = t_1;..;x_n=t_n} and apply mgu to the remainder of the clause *)
(*--- if 1) fails due non-unification then collect disequality of vaiables and unify them and apply one substitution --*)
(*--- the ramaining disequalitites are applied one by one *)
(*-----------------------------------------------------------------*)

    
let unflatten_clause clause = 
  if not (Clause.has_eq_lit clause) 
  then clause
  else
    begin
  let lit_list = Clause.get_lits clause in 
  let clause_chaged = ref false in 
  (* get_subst_t_s checks whether one of s,t is a var, makes occur check and returns the pair Some((v,t)); otherwse None *)
  let get_subst_t_s t s =
    if  (Term.is_var t) && (not (Term.is_subterm t s))
    then 
      Some((t,s))
    else
      (if (Term.is_var s) && (not (Term.is_subterm s t))
      then
	Some((s,t))
      else
	None
       )
  in
  let is_var_eq atom = 
    match (Term.decompose_eq_atom atom) with 
    |[_etype;t;s] -> (Term.is_var t) && (Term.is_var s)
    | _ -> false
  in
  let is_var_deq lit =  
    (Term.is_neg_lit lit) && (is_var_eq  (Term.get_atom lit))
  in
 (* we order so disequality between var X!=Y comes first *)
 (* order can have effect consider*)
 (* cnf(a1,axiom, (p(f(X,Y)) | g(X,Z) != Y | h(X) != Y | X != Y | Y != Z)). *)
 (* 1. unflatten  Y -> g(X,Z) *)
 (* cnf(a1,axiom, (p(f(X,Y)) | h(X) != g(X,Y) | X != g(X,Z) | g(X,Z) != Z)).*)
 (* 2. unflatten vars first *)
  (* cnf(a1,axiom, (p(f(Y,Y)) | g(Y,Y) != Y | h(Y) != Y)). *)
  
  let ordered_clause_lits = 
    let cmp_lit l1 l2 = cmp_bool (not (is_var_deq l1)) (not (is_var_deq l2)) in 
    List.sort cmp_lit lit_list 
  in
  let rec f processed_lits rest_lits = 
    match rest_lits with 
    | lit::tl_rest ->  
	begin
	  if (Term.is_neg_lit lit) 
	  then 
	    let atom = Term.get_atom lit in     
	    match (Term.decompose_eq_atom atom) with 
	    |[_etype;t;s] -> 
		if (t == s)
		then 
		  f processed_lits tl_rest
		else
		  (
		   match (get_subst_t_s t s) with
		   | Some(v,r)  -> 
		       let subst_var_lit lit = (* add_term_db (Term.replace v r lit) *)
			 let res = add_term_db (Term.replace v r lit) in
(*			 out_str ("subst: "^(Term.to_string v)^"->"^(Term.to_string r)^" into "
				  ^(Term.to_string lit)^" res: "^(Term.to_string res)^"\n");			 
*)
			 res
		       in
		       let new_processed_lits = List.map subst_var_lit processed_lits in
		       let new_rest_lits =  List.map subst_var_lit tl_rest in
		       incr_int_stat 1 prep_unflattend;
		       clause_chaged:= true;		       
		       f new_processed_lits new_rest_lits
		   | None ->
		       let new_processed = lit::processed_lits in
		       f new_processed tl_rest
		  )
(*out_str ("some: ("^(Term.to_string t)^";"^(Term.to_string s)^")\n");*)
		       	
	    |_-> (* not diseq *)
		let new_processed = lit::processed_lits in
		f new_processed tl_rest
	  else (* not neg *)
	    let new_processed = lit::processed_lits in
	    f new_processed tl_rest
	end
    | [] -> processed_lits
  in
  let new_lits = f []  ordered_clause_lits in
  if !clause_chaged 
  then    
    let tstp_source = Clause.tstp_source_unflattening clause in  
    let unflat_clause = create_clause tstp_source new_lits in
    dbg D_unflat (lazy ("old: "^(Clause.to_string clause)));
    dbg D_unflat (lazy ("new: "^(Clause.to_string unflat_clause)));
(*    Clause.assign_replaced_by (Def(Clause.RB_unflat unflat_clause)) clause; *)
    Clause.inherit_conjecture clause unflat_clause;
    unflat_clause
  else
    clause
    end

let unflatten clause_list =  
(*  out_str (" before unflatten: \n"^(Clause.clause_list_to_string clause_list)^"\n\n");*)
  let unflatten_clause_list = List.map unflatten_clause clause_list in
(*  out_str (" after unflatten: \n"^(Clause.clause_list_to_string unflatten_clause_list)^"\n\n");*)
  unflatten_clause_list


(* could be more efficient but messier

(* literals l1 l2 are already CUT  from  c1 and c2 *)
   
   let resolution  c1 l1 c2 l2 term_db_ref = 
   let compl_l1 = add_compl_lit l1 in
   let mgu = Unif.unify_bterms (1,l1) (2,l2) in
   Clause.normalise_bclause_list  
   term_db_ref mgu [(1,c1);(2,c2)]

(* literals l1 l2 are already CUT from  c *)

   let factoring c l1 l2 term_db_ref =
   let mgu =  Unif.unify_bterms (1,l1) (1,l2) in
   Clause.normalise_bclause (1,c) mgu term_db_ref

 *)

(*--- bmc1 next merge -------*)

(* 
 can appear during preprocessing such as pred_elim 
 (functionality) If we have ~Next(i, x,y1) \/ ~Next(j,x,y2) \/ C(x,y1,y2) then we merge y1 and y2:  ~Next(i, x,y1) \/ ~Next(j, x,y1) \/ C(x,y1,y1) and if i = j then with  ~Next(i, x,y1) \/ C(x,y1,y1)
 for safety can also use (one-to-one) but mifgt be a problem for liveness/deadlock so don't include yet
 If we have ~Next(i,x1,y) \/ ~Next(j,x2,y) \/ C(x1,x2,y) then replace it by  ~Next(i,x1,y) \/ ~Next(j,x1,y) \/ C(x1,x1,y)
 (more generaly for safety can eliminate long cycles)
*)

(* can raise Eliminated *)

let get_next_vars lit = 
    if (Term.is_neg_lit lit)
    then
      let atom = Term.get_atom lit in 
      match atom with 
      |Term.Fun (symb,args,_) -> 
	  if (symb == Symbol.symb_ver_next_state) 
	  then 
	    let arg_list = Term.arg_to_list args in
	    match arg_list with 
	    |[_tr_i; (Term.Var(x,_) as x_t);(Term.Var(y,_) as y_t)] -> Some ((x, x_t, y, y_t)) (* Next(tr_i,x,y) *)
	    |_-> None 
	  else None
      |_ -> None
    else 
      None 

exception Remove_Lit

(* can raise Eliminated *)

(* merge functinality based on functionality restriction which should be OK for saftey/liveness/deadlock *)
(* for saftey we can add also the inverse one-one, or more generally no cycles *)


let bmc1_merge_next_func clause =   
  let fwd_map_ref = ref (Subst.create ())  in
  let merge_map_ref = ref (Subst.create ()) in
  let f lit = 
    match (get_next_vars lit) with 
    |Some((x, x_t, y, y_t)) -> 
	begin
	  try 
	    let y1_t = Subst.find x !fwd_map_ref in 	      
	    if (y1_t == y_t) (* assume terms are shared *) 
	    then  () (* this is the same literal as before and can be removed  later *)
	    else
	      (
	       if (not (Subst.mem y !merge_map_ref))
	       then
		 merge_map_ref := Subst.add y y1_t !merge_map_ref (* map new to old *)
	       else ()
	      )
	  with 
	    Not_found -> 
	      (
	       fwd_map_ref:= Subst.add x y_t !fwd_map_ref;
	      )
	end
    |None -> ()
  in
  if (Clause.has_next_state clause)
  then
    (
     let lits = Clause.get_lits clause in
     List.iter f lits;
     if (not (Subst.is_empty !merge_map_ref))
     then
       let new_lits = List.map (Subst.apply_subst_term term_db_ref !merge_map_ref) lits in
       let tstp_source = Clause.tstp_source_bmc1_merge_next clause in
       let new_clause = create_clause tstp_source new_lits in
       dbg D_bmc1_merge_next 
	 (lazy ((Clause.to_string clause)^" => "^(Clause.to_string new_clause)));
       Statistics.incr_int_stat 1 bmc1_merge_next_func;
       new_clause
     else
       clause
    )
  else
    clause

 

(*
let bmc1_merge_next_func clause =   
  let fwd_map_ref = ref TMap.empty   (* map: tr_i -> Subst  (x-> y)  in *)
  let merge_map_ref = ref TMap.empty (* (Subst.create ()) in *)
  let f lit = 
    match (get_next_vars lit) with 
    |Some((x, x_t, y, y_t)) -> 
	begin
	  try 
	    let x_subst = TMap.find tr_i !fwd_map_ref in (* first N(tr_i,x,y) creates x_subst: x->y *)
	    try 
	      let y1_t = Subst.find x !fwd_map_ref in 	      
	      if (y1_t == y_t) (* assume terms are shared *) 
	      then  () (* this is the same literal as before and can be removed  later *)
	      else
		(
		 if (not (Subst.mem y !merge_map_ref)) 
		 then
		   merge_map_ref := Subst.add y y1_t !merge_map_ref (* map new to old *)
		 else
		 ()
		)
	    with 
	      Not_found -> 
		(
		 fwd_map_ref:= Subst.add x y_t !fwd_map_ref;
		)
	  with 
	    Not_found -> (* tr_i *)
	      ...
	end
    |None -> ()
  in
  if (Clause.has_next_state clause)
  then
    (
     let lits = Clause.get_lits clause in
     List.iter f lits;
     if (not (Subst.is_empty !merge_map_ref))
     then
       let new_lits = List.map (Subst.apply_subst_term term_db_ref !merge_map_ref) lits in
       let tstp_source = Clause.tstp_source_bmc1_merge_next clause in
       let new_clause = create_clause tstp_source new_lits in
       dbg D_bmc1_merge_next 
	 (lazy ((Clause.to_string clause)^" => "^(Clause.to_string new_clause)));
       Statistics.incr_int_stat 1 bmc1_merge_next_func;
       new_clause
     else
       clause
    )
  else
    clause
*)

(*
let bmc1_next_merge cl = 

  (* for new ~Next(x,y) then add fwd_map x-> y and bwd_map y->x *)
 (* we are doing it iteratively first collect collapsing merging vars then rewrite and repeate *)

  let fwd_map_ref = ref VMap.empty in
  let bwd_map_ref = ref VMap.empty in   
  let merging_map_ref = ref VMap.empty
  let f rest_lits lit = 
    match (get_next_vars lit) with 
    |Some((x,y)) -> 
	if (x == y) (* we have ~Next(x,x) \/ C which we can allways assume true: can be a problem in future ? *)
	then raise Eliminated 
	else
	  begin
	    try 
	      let y1 = VMap.find x !fwd_map_ref in 	      
		if (y1 == y) 
		then   
		  ()  (* this is the same literal as before and can be removed         *)
		else   (* this left arg already occured and we need to collaps y1 and y *)
		  ( 
		    collapsing_map_ref := VMap.add y y1 !collapsing_map_ref; (* map new to old *)
		    try 
		      let x1 = VMap.find y !bwd_map_ref in
		    (* since we always add x,y and y, x simultaniously we can assume that if there is x in b*) 
		      collapsing_map_ref := VMap.add x x1 !collapsing_map_ref; (* map new to old *)	      
		    with 
		      Not_found -> 
 			bwd_map_ref:= VMap.add y x !bwd_map_ref;			
		   )
	    with 
	      Not_found -> 
		(fwd_map_ref:= VMap.add x y !fwd_map_ref;
		 lit::rest_lits
		)

	      VMap.add x y 
	  end
	fwd_map_ref:= VMap.add x y !fwd_map_ref;

    |None -> rest_lits
 
	      with Remove_Lit -> 		
(* add *)
(*
	if (Clause.has_next_state clause)
	then
	else clause
 *)	    
*)

(*--------------------------Instantiation-------------------------*)

(*----------VERSION WITHOUT DISM VEC INDEX ---------*)
(*--new version: constr checked on normalized substitutions****)


(*

  let is_not_redundant_inst_norm subst_norm clause =
(*   out_str_debug 
     ("---------Constr Check-------\n");    *)
  if (not !current_options.inst_dismatching) 
  then true
  else
  begin
  try
  let dismatching = Clause.get_dismatching clause in
(*    out_str_debug 
      ("Inst Clause: "^(Clause.to_string clause)
      ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
      ^"Subs_to_check: "^(Subst.to_string subst_norm)^"\n"); *)
  if (Dismatching.check_constr_norm_list subst_norm dismatching)
  (*(Dismatching.check_constr_feature_list subst_norm dismatching)*)
  then
  ( (*out_str_debug "Constr. is Satisfied \n";*)
(* we don't need to add all subt_norm but only vars that occurred in mgu *)
  let new_constr = Dismatching.create_constr_norm subst_norm in
  Clause.assign_dismatching 
  (Dismatching.add_constr dismatching new_constr) clause;
  (*(Dismatching.add_constr_feature_list dismatching new_constr);*)
  true)
  else
  ((*out_str_debug "Constr. is NOT Satisfied \n";*)
  incr_int_stat 1 inst_num_of_dismatching_blockings;
  false) 
  with Clause.Dismatching_undef -> 
  (let new_dismatching =
  (Dismatching.create_constr_list ()) in
  (* let new_dismatching =
     (Dismatching.create_constr_feature_list ()) in*)
  let new_constr = Dismatching.create_constr_norm subst_norm in
  Clause.assign_dismatching 
  (Dismatching.add_constr new_dismatching new_constr) clause;
  (* (Dismatching.add_constr_feature_list new_dismatching new_constr);   
     Clause.assign_dismatching new_dismatching clause;*)
  (*out_str_debug "Constr. is empty\n";*)
  true)
  end
(*out_str_debug "Constr. is empty";*)  
(*  else false*)


 *)



(*
  let is_not_redundant_dism constr clause =
(*   out_str_debug 
     ("---------Constr Check-------\n");    *)
  if (not !current_options.inst_dismatching) 
  then true
  else
  begin
  try
  let constr_set = Clause.get_dismatching clause in
(*    out_str_debug 
      ("Inst Clause: "^(Clause.to_string clause)
      ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
      ^"Subs_to_check: "^(Subst.to_string subst_norm)^"\n"); *)
  if (Dismatching.check_constr_set constr_set constr)
  (*(Dismatching.check_constr_feature_list subst_norm dismatching)*)
  then
  (*out_str_debug "Constr. is Satisfied \n";*)
(* we don't need to add all subt_norm but only vars that occurred in mgu *)
  true 
  else 
  (incr_int_stat 1 inst_num_of_dismatching_blockings;
  false)
  with 
  Clause.Dismatching_undef -> 
  true
  end


  let add_dism_constr constr clause = 
  begin
  let constr_set =
  try
  Clause.get_dismatching clause 
  with 
  Clause.Dismatching_undef -> 
  (Dismatching.create_constr_set ())
  in
  Clause.assign_dismatching 
  (Dismatching.add_constr constr_set constr) clause
  end
  
 *)

(*
  let is_not_redundant_inst_norm subst_norm clause =
  if (not !current_options.inst_dismatching) && (not !current_options.sat_out_model)
  then true
  else
  let constr = Dismatching.create_constr subst_norm in
  if (is_not_redundant_dism constr clause) 
  then 
  (add_dism_constr constr clause;
  true 
  )
  else 
  false
  
 *)
      

let get_dismatching_create clause_param = 
  try 
    get_inst_dismatching clause_param
  with 
    Dismatching_undef -> 
      (
      let init_dismatching = Dismatching.create_constr_set () in 
      inst_assign_dismatching init_dismatching clause_param;
      init_dismatching
      )


let add_to_dism_constr subst_norm clause_param = 
  let old_constr_set = get_dismatching_create clause_param in
  let new_constr_set = Dismatching.add_constr old_constr_set subst_norm in
  inst_assign_dismatching new_constr_set clause_param



let is_not_redundant_inst_norm subst_norm clause_param =
  let start_time = Unix.gettimeofday () in
  let res =
(* if not !current_options.sat_out_model=Model_None then we need to create dismatching constriants     *)
(* for the model representation, they are checked only when !current_options.inst_dismatching is true *)
    if (not !current_options.inst_dismatching) && (!current_options.sat_out_model=Model_None)
    then true
    else
      begin     
	let old_constr_set = get_dismatching_create clause_param in
	if (!current_options.inst_dismatching) 
	then      
	  try 
	    let new_constr_set = Dismatching.check_and_add old_constr_set subst_norm in
	    inst_assign_dismatching new_constr_set clause_param;
	    true
	  with
	    Dismatching.Constr_Not_Sat ->
	      (incr_int_stat 1 inst_num_of_dismatching_blockings;
	       false)
	else (* !current_options.sat_out_model=true and !current_options.inst_dismatching = false *)
	  (* We need to add constriant for model representation, but do not check it *)
	  let new_constr_set = Dismatching.add_constr old_constr_set subst_norm in
	  inst_assign_dismatching new_constr_set clause_param;
	  true
      end
  in
  let end_time   = Unix.gettimeofday () in 
  let run_time = (end_time -. start_time) in
  add_float_stat run_time Statistics.inst_dismatching_checking_time;
  res
    

let dismatching_string clause_param =   
  try 
    "["^(Dismatching.to_string_constr_set (get_inst_dismatching clause_param))^"]"
  with
    Dismatching_undef -> "[]"


exception Main_concl_redundant

(* assume that we already added clause to db *)

let assign_param_clause parent parents_side clause = 
(*  Clause.assign_when_born ((Clause.when_born parent)+1) clause;*)

(* only assign to clauses not which are not in passive! *)
  Clause.assign_ps_when_born_concl ~prem1:[parent] ~prem2:parents_side ~c:clause (*; *)

(*  inst_assign_activity ((Clause.inst_get_activity parent)+1) parent; *)
(*
  (if (!current_options.inst_orphan_elimination) 
  then
    (add_inst_child parent ~child:clause;)
  else ())
*)
(*;	*)
(*
  (if 
    val_of_override !current_options.bmc1_unsat_core_children &&
    Clause.in_unsat_core parent 
  then
    (Clause.assign_in_unsat_core true clause;)
  )
*)
    (* Clause.assign_conjecture_distance conj_dist clause;*)
    (* Clause.assign_instantiation_history clause parent parents_side *)
    (* Clause.assign_tstp_source_instantiation clause parent parents_side *)
    

let select_a_side_clause c_list = 
  list_find_min_element 
    (fun c1 c2 ->
      Pervasives.compare (Clause.get_conjecture_distance c1) (Clause.get_conjecture_distance c2)
    )	 
    c_list
    
(*---------------------------------------------------------------------------*)  
(*------instantiation first check duplicates then dismatching constraints----*)


exception Inst_main_only_proper of clause

let instantiation_norm_dc ~is_redundant_fun (c1,c1_param) l1 c_c_param_list2 l2  =
(* if mgu is proper of c1 and the conclusion is redundant then all inference *)
(* is redundant; similar *)
(* if mgu is proper of list2 and *)
(*  all instanses of list2 are redundant then the ineference is redundant  *)
(* we assign  list2_concl_redundant is false if at least one concl in list2  *)
(* is not redundant  *)
(* we can not *)
(* put conl of c1 in to ClauseAssignDB immediately, but only at the end  *)
  let compl_l1 = add_compl_lit l1 in
  let (c_list2,c_param_list2) = List.split c_c_param_list2 in
  let list2_concl_redundant = ref (true && (not dbg_inst_no_redund)) in

  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in

  if (not ((SubstBound.is_proper_instantiator mgu 1) || (SubstBound.is_proper_instantiator mgu 2)))
  then(
    dbg D_inst_tmp (lazy ("main clause:"^(Clause.to_string c1)));
    dbg D_inst_tmp (lazy ("sel lit: "^(Term.to_string l1)));
    dbg D_inst_tmp (lazy ("dism: "^(dismatching_string c1_param)));
    
    dbg D_inst_tmp (lazy ("side sel lit: "^(Term.to_string l2) ));
   );

  
  assert ((SubstBound.is_proper_instantiator mgu 1) || (SubstBound.is_proper_instantiator mgu 2));

  dbg D_inst (lazy ("main clause:"^(Clause.to_string c1)));
  dbg D_inst (lazy ("sel lit: "^(Term.to_string l1)));
  dbg D_inst (lazy ("dism: "^(dismatching_string c1_param)));
  
  dbg D_inst (lazy ("side sel lit: "^(Term.to_string l2) ));
  

  let main_old_dismatching_c1 = get_dismatching_create c1_param  in

  try    
    let conc1 = 
      if (SubstBound.is_proper_instantiator mgu 1) || (dbg_inst_no_redund)
      then  
	let (inst_lits,subst_norm) = 
	  (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 (get_lits c1))
	in
	let tstp_source = Clause.tstp_source_instantiation c1 [(select_a_side_clause c_list2)]  in 
	let inst_clause = create_clause tstp_source inst_lits in
(*	if (context_mem context inst_clause) *)
	if (is_redundant_fun inst_clause) && (not dbg_inst_no_redund) 
	then 
          (
(* adding dism. constraint is essential for correct model representation!*)
	   add_to_dism_constr subst_norm c1_param;   
           incr_int_stat 1 inst_num_of_duplicates;
           dbg D_inst (lazy (" main concl is redundant or in: "^(Clause.to_string inst_clause)));
(*          out_str_debug ("Clause is already In DB: "
            ^(Clause.to_string inst_clause)^"\n");*)
           raise Main_concl_redundant)
	else
	  if (is_not_redundant_inst_norm subst_norm c1_param) ||  (dbg_inst_no_redund)
          then 
            if !current_options.inst_restr_to_given
            then 
              (
               dbg D_inst (lazy (" keeping only main concl: "^(Clause.to_string inst_clause)));
               raise (Inst_main_only_proper inst_clause)
              )
            else
              Some ((inst_clause, subst_norm))
	  else 
	    (
             dbg D_inst (lazy (" main concl is redundant: dismatching unsat: "^(Clause.to_string inst_clause)));
             raise Main_concl_redundant)
      else
	(
	 incr_int_stat 1 inst_num_of_non_proper_insts;
         dbg D_inst (lazy ("non-proper main inst"));
	 None)
    in    
    let conc2 =
(* if l1 is in inst_in_unif_index then all instantiations with the side clauses *)
(* are already beeing made since all inference between active are made        *)
      let is_proper_mgu_2 = (SubstBound.is_proper_instantiator mgu 2) in
      if (is_proper_mgu_2) || (dbg_inst_no_redund)
      then
	let f rest (clause, clause_param) =
          dbg D_inst (lazy ("side clause:"^(Clause.to_string clause)));
          dbg D_inst (lazy ("sel lit: "^(Term.to_string l2) ));
          dbg D_inst (lazy ("dism: "^(dismatching_string clause_param)));

	  let (inst_lits,subst_norm) = 
	    Clause.apply_bsubst_norm_subst term_db_ref mgu 2 (get_lits clause) 
	  in
	  let tstp_source = Clause.tstp_source_instantiation clause [c1] in 
	  let inst_clause = create_clause tstp_source inst_lits in	
	  if (is_redundant_fun inst_clause) && (not dbg_inst_no_redund) 
	  then 
	    (
             dbg D_inst (lazy (" side concl is redundant or in: "^(Clause.to_string inst_clause)));
(* adding dism. constraint is essential for correct model representation!*)
	     add_to_dism_constr subst_norm clause_param;   
	     incr_int_stat 1 inst_num_of_duplicates;
	     rest)
	  else
	    if (is_not_redundant_inst_norm subst_norm clause_param) || (dbg_inst_no_redund)
(*(is_not_redundant_feature subst_norm clause)*)
	    then 
	      (list2_concl_redundant := false;

(*	       let added_clause = context_add context inst_clause in *)
	       let added_clause = inst_clause in 

(* TODO: 2016 check !!!*)
	       assign_param_clause clause [c1] added_clause;
	       
	       added_clause::rest)
	    else 
	      (
               dbg D_inst (lazy (" side concl is redundant: dismatching unsat: "^(Clause.to_string inst_clause)));
	       rest)	  
	in
	List.fold_left f [] c_c_param_list2 
      else
	(         
         dbg D_inst (lazy (" side non-proper mgu "));
         list2_concl_redundant := false; (*KK *)
         incr_int_stat 1 inst_num_of_non_proper_insts;
         []
        )
    in 

(* dbg*)
(*
    let concl_list = 
      match conc1 with 
      | Some ((dbg_conc1_cl,_)) ->
          dbg_conc1_cl::conc2 
      |None -> conc2
*)
(* end dbg *)


    let concl_list = 
      if  (!list2_concl_redundant) 
      then
	(
	 (*  out_str "Side Conclusions are all redundant !\n "; *)
         dbg D_inst (lazy ("inf is redundant: all side concl are reudundant"));
         dbg D_inst (lazy ("tmp dism: "^(dismatching_string c1_param)));
	 inst_assign_dismatching main_old_dismatching_c1 c1_param; 
         dbg D_inst (lazy ("assigned old dism: "^(dismatching_string c1_param)));
         []
        )
      else 
	(match conc1 with 
	|Some ((conc1_cl, conc1_subst_norm)) ->
            (* note that here conc1_subst_norm is always proper *)
	    (

	     if (is_redundant_fun conc1_cl)  && (not dbg_inst_no_redund)  (*KK'16: should not happen ? *)
             then
              (
(* adding dism. constraint is essential for correct model representation!*)

	       add_to_dism_constr conc1_subst_norm c1_param;   
	       incr_int_stat 1 inst_num_of_duplicates;
               conc2)
             else   
              ( 
           (* let added_conc1 = (context_add context conc1_cl) in *)
                let added_conc1 = conc1_cl in 

(* TODO: 2016 check !!!*)
	      assign_param_clause c1 c_list2 added_conc1; 
       	      added_conc1::conc2
            )
            ) 
              (* in this case conc1 is empty*)
	|None -> conc2
	)

    in
    (*  out_str
	("\n Conclusions:\n"^(Clause.clause_list_to_string concl_list)^"\n"
	^"------------------------------------------------\n");
     *)
    concl_list
  with 
    Main_concl_redundant -> 
      (dbg D_inst (lazy (" main concl is redundant"));      
       []
      )
  | Inst_main_only_proper inst_main_clause -> [inst_main_clause]


(*-------------------------------------------------------------------*)
(* instantiation first check dismatching constraints then duplicates *)

let instantiation_norm_cd context (c1,c1_param) l1 c_c_param_list2 l2 =
  let compl_l1 = add_compl_lit l1 in
  let (c_list2,c_param_list2) = List.split c_c_param_list2 in
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
(*debug*)
  (*out_str_debug ("Main Clause:"^(Clause.to_string c1)^"\n"
    ^"Constr: "^(dismatching_string c1)^"\n" 
    ^"Sel Lit: "^(Term.to_string l1)^"\n");  *)
(*  let conjecture_distance_c1 = (Clause.get_conjecture_distance c1) in*)
  (* let min_conj_dist = Clause.get_min_conjecture_distance (c1::c_list2) in*)
  try 
    let conc1 = 
      if (SubstBound.is_proper_instantiator mgu 1) 
      then  
	let (inst_lits,subst_norm) = 
	  (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 (get_lits c1))
	in
	let tstp_source = Clause.tstp_source_instantiation c1 [(select_a_side_clause c_list2)]  in 
	let inst_clause = create_clause tstp_source inst_lits in
	if (is_not_redundant_inst_norm subst_norm c1_param)
	then 
	  if (context_mem context inst_clause)
	  then 
	    (
	     incr_int_stat 1 inst_num_of_duplicates;
	     (*out_str_debug ("Clause is already In DB: "
	       ^(Clause.to_string inst_clause)^"\n");*)
	     raise Main_concl_redundant)
	  else
	    let added_clause = context_add context inst_clause in
	    (* let new_conj_dist = min_conj_dist +1 in*)
            (*((min_conj_dist_list2 + conjecture_distance_c1) lsr 2)+1*) 
	    assign_param_clause c1 c_list2  added_clause;	    
	    [added_clause]	 
	else 
	  (
	   raise Main_concl_redundant)
      else
	(
	 incr_int_stat 1 inst_num_of_non_proper_insts;
	 (*out_str_debug ("Non-proper Inst Main\n");*)
	 [])
    in    
    let conc2 =
      if (SubstBound.is_proper_instantiator mgu 2) then    
	let f rest (clause,clause_param) =
(*debug*)
	  (*out_str_debug  ("Side Clause:"^(Clause.to_string clause)^"\n"
	    ^"Constr: "^(dismatching_string clause)^"\n" 
	    ^"Sel Lit: "^(Term.to_string l2)^"\n"); *)
	  let (inst_lits,subst_norm) = 
	    Clause.apply_bsubst_norm_subst term_db_ref mgu 2 (get_lits clause) 
	  in
	  let tstp_source = Clause.tstp_source_instantiation clause [c1] in 
	  let inst_clause = create_clause tstp_source inst_lits in	
	  if (is_not_redundant_inst_norm subst_norm clause_param)
	  then 
	    if (context_mem context inst_clause)
	    then (
	      incr_int_stat 1 inst_num_of_duplicates;
	      (* out_str_debug ("Clause is already In DB: "
		 ^(Clause.to_string inst_clause)^"\n");*)
	      rest)
	    else
	      let added_clause = context_add context inst_clause in
	      (* let new_conj_dist = (Clause.get_min_conjecture_distance [clause;c1])+1 in *)
	      assign_param_clause clause [c1] added_clause;
	      added_clause::rest	
	  else 
	    (
	     rest)	  
	in
	List.fold_left f [] c_c_param_list2
      else
	(
	 incr_int_stat 1 inst_num_of_non_proper_insts;
	 (*out_str_debug ("Non-proper Inst Side\n");*)
	 [])
    in 
    let concl_list = conc1@conc2 in
    (*out_str_debug 
      ("\n Conclusions:\n"^(Clause.clause_list_to_string concl_list)^"\n"
      ^"------------------------------------------------\n");*)
    concl_list
  with 
    Main_concl_redundant -> 
(*      out_str_debug 
	(" ---------Main_concl_redundant ----------\n");*)
      []	      
	


let instantiation_norm = 
  instantiation_norm_dc
(* instantiation first check dismatching constraints then duplicates *)
(* instantiation_norm_cd *)


(*------------- domain instantiation used in QBF/ also try finite domains ------------*)

type inst_domain_result = 
  | Main_dom_inst of clause list (* main is redunandant in the presence of these clauses *)
  | Side_dom_inst of clause list (* side is redunandant in the presence of these clauses *)

(* generates a list of bsubst_i which is obtained by instantiating bv -> d_i for d_i \in (type_to_dom v) *)
let dom_ext_bsubst type_to_domain bv bsub = 
  let (b,v) = bv in 
  let dom_set = 
    try 
      SMap.find (Var.get_bv_type bv) type_to_domain
    with 
      Not_found -> failwith ("inference_rules:dom_ext_bsub: type of bv: "^(Symbol.to_string (Var.get_bv_type bv))^"  should be in type_to_domain")
  in  
  let f d rest = 
    let new_bsubst = SubstBound.add bv (b,d) bsub in 
    (new_bsubst::rest)
  in
  TSet.fold f dom_set []

(* can raise Unif.unification_failed *)
(* do not need dismatching as instantiated clauses will be eliminated *)
let inst_clause bound bsubst clause = 
  let (inst_lits,subst_norm) = 
    Clause.apply_bsubst_norm_subst term_db_ref bsubst bound (get_lits clause)
  in
  let tstp_source = Clause.tstp_source_instantiation clause []  in 
  let inst_clause = create_clause tstp_source inst_lits in
  dbg D_dom_inst (lazy (Clause.to_string clause));
  dbg D_dom_inst (lazy (Clause.to_string inst_clause));
  inst_clause

(* instantiatiate clause by all substs *)
let inst_substs_clause bound bsubsts clause = 
  List.map (fun bsubst -> inst_clause bound bsubst clause) bsubsts 
  
(* instantiatiate all clauses by all subst *)  
let inst_substs_clauses bound bsubsts clauses = 
  List.fold_left 
    (fun rest cl -> 
      let inst_cls = inst_substs_clause bound bsubsts cl in 
      inst_cls@rest)
    [] 
    clauses 

(* instantiation chain which is domain complete -- so original clause can be eliminated and fully cover the substitution *)
(* we assume bsubst is 1)  right var reduced 2) separated based on a) proper part and b) bound *)
(* inst_chain can be simulated by a sequence of the single instantiations by instantiation_domain_single *)
let get_inst_chain type_to_domain bsubst = 
  let rec f bsubst_accum inst_chain remainder_bsubst = 
    try
      let (bv, bt) = SubstBound.choose remainder_bsubst in
      let new_inst_chain = (dom_ext_bsubst type_to_domain bv bsubst_accum)@inst_chain in
      let new_remainder_bsubst = SubstBound.remove bv remainder_bsubst in
      let new_bsubst_accum = SubstBound.add bv bt bsubst_accum in
      f new_bsubst_accum new_inst_chain new_remainder_bsubst
    with
      Not_found -> inst_chain
  in 
  let inst_chain = f SubstBound.empty [] bsubst in
  inst_chain

(*
type dom_inst_param = 
    Dom_inst_single | 
    Dom_inst_chain
*)
  
let instantiation_domain_single dom_inst_param type_to_domain (c1,(c1_param:inst_cp)) l1 (c_c_param_list2:((clause * inst_cp) list)) l2 =
  let compl_l1 = add_compl_lit l1 in

(*  let list2_concl_redundant = ref (true && (not dbg_inst_no_redund)) in *)

  let mgu = SubstBound.right_vnorm_bsubst (Unif.unify_bterms (1,compl_l1) (2,l2)) in
  let (mgu_proper, _mgu_non_proper) = SubstBound.split_proper_inst mgu in 
  assert (not (SubstBound.is_empty mgu_proper));

  let (mgu_main_proper, mgu_side_proper) =  SubstBound.split_left_bound mgu_proper 1 in 

  let get_dom_inst_bsubsts bsubst = 
    assert (not (SubstBound.is_empty bsubst));
    match dom_inst_param with 
    | QBF_dom_inst_single -> 
        let (bv, _bt) = SubstBound.choose bsubst in    
        let dom_bsubst_list = dom_ext_bsubst type_to_domain bv (SubstBound.create ()) in
        dom_bsubst_list
          
    |QBF_dom_inst_chain ->
        let dom_bsubst_list = get_inst_chain type_to_domain bsubst in
        dom_bsubst_list

    |QBF_dom_inst_none -> failwith "instantiation_domain_single: dom_inst_param should not be QBF_dom_inst_none here"
  in
  if (not (SubstBound.is_empty mgu_main_proper)) 
  then 
    let dom_bsubst_list = get_dom_inst_bsubsts mgu_main_proper in
    let dom_instances = inst_substs_clause 1 dom_bsubst_list c1 in
    Main_dom_inst (dom_instances)
  else
    (    
     let dom_bsubst_list = get_dom_inst_bsubsts mgu_side_proper in
     let (c_list2, c_param_list2) = List.split c_c_param_list2 in  
     let dom_instances = inst_substs_clauses 2 dom_bsubst_list c_list2 in 
     Side_dom_inst (dom_instances)
        )
      
(*-----------------domain pre-instantiation-------*)

let split_type_to_domain type_to_dom = (* list of maps type -> dom_el *)
  let f dom_type dom_set f_rest = 
    let g dom_el g_rest = 
      let new_map = SMap.add dom_type dom_el SMap.empty in 
      new_map::g_rest 
    in
    TSet.fold g dom_set f_rest 
  in
  SMap.fold f type_to_dom []

  
let dom_pre_inst type_to_domain clause =
  if (Clause.is_ground clause) 
  then 
    [clause]
  else
    let lits = Clause.get_lits clause in 
    let type_dom_ground_maps = split_type_to_domain type_to_domain in
    let f rest_clauses type_dom_map  = 
      let inst_lits = List.map (Subst.grounding term_db_ref type_dom_map) lits in
      let tstp_source = Clause.tstp_source_instantiation clause []  in 
      let inst_clause = create_clause tstp_source inst_lits in
      inst_clause::rest_clauses
    in
    List.fold_left f [] type_dom_ground_maps

(* right reduce the b_mgu *)


(* applies domain splitting *)
(*
let apply_dom_splitting_single type_to_domain bsubst bound clause = 
  assert (SubstBound.is_proper_instantiator bsubst 1)
*)

(*
exception Dom_inst_main of (clause list)
exception Dom_inst_side of (clause list)


let instantiation_domain ~is_redundant_fun type_to_domain (c1,c1_param) l1 c_c_param_list2 l2 =
  let compl_l1 = add_compl_lit l1 in
  let (c_list2,c_param_list2) = List.split c_c_param_list2 in
(*  let list2_concl_redundant = ref (true && (not dbg_inst_no_redund)) in *)

  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  
*)
(*---------------------- end domain split ----------*)

(*-------- Resolution with dismatching on unit clauses  -----------*)
(*-------  only for hyper resolution with Horn clauses  -----------*)

let resolution_dismatch  
    dismatch_flag forward_subs_resolution_flag  backward_subs_resolution_flag 
    (c1,c1_param) l1 c_c_param_list2 l2 = 
  let compl_l1 = add_compl_lit l1 in
(*  let (c_list2, c_param_list2) = List.split c_c_param_list2 in*)
(* out_str_debug ("Main Clause:"^(Clause.to_string c1)^"\n"
   ^"Constr: "^(dismatching_string c1)^"\n" 
   ^"Sel Lit: "^(Term.to_string l1)^"\n");  *)

  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in   
  let (inst_lits,subst_norm) = 
    (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 (get_lits c1))
  in
  
  if (not dismatch_flag) || 
  ((Clause.length c1) <= 1) ||
  (is_not_redundant_inst_norm subst_norm c1_param) 
  then    
    begin
      let new_litlist1 = 
	Clause.find_all (fun lit -> not(l1 == lit)) c1 
      in
      let f rest (c2,c2_param) = 
(*	out_str_debug ("Side Clause:"^(Clause.to_string c2)^"\n"
  ^"Constr: "^(dismatching_string c2)^"\n" 
  ^"Sel Lit: "^(Term.to_string l2)^"\n");  
 *)
	let (inst_lits2,subst_norm2) = 
	  (Clause.apply_bsubst_norm_subst term_db_ref mgu 2 (get_lits c2))
	in  
	if (not dismatch_flag) || (Clause.length c2) <=1 ||
	(is_not_redundant_inst_norm subst_norm2 c2_param) 
	then
	  begin
	    let new_litlist2 = 
	      Clause.find_all (fun lit -> not(l2 == lit)) c2 in 
	    let tstp_source = Clause.tstp_source_resolution [c1;c2] [l1;l2] in
	    let conclusion = 
	      create_clause tstp_source 
		(Clause.normalise_blitlist_list 
		   term_db_ref mgu [(1,new_litlist1);(2,new_litlist2)])
	    in
	    (if forward_subs_resolution_flag 
	    then
	      if (strict_subset_subsume conclusion c1)
	      then 
		(
                  (* clause_register_subsumed_by ~by:conclusion c1;*)		 
		  raise (Main_subsumed_by conclusion))
	      else ()
	    else ()      
	    );
	    (if backward_subs_resolution_flag 
	    then
	      if (strict_subset_subsume conclusion c2)
	      then 
		(
                (* clause_register_subsumed_by ~by:conclusion c2 *)
                )
	      else ()
	    else ());      
	    (* Clause.assign_resolution_history conclusion [c1;c2] [l1;l2]; *)
	    Clause.assign_ps_when_born_concl ~prem1:[c1] ~prem2:[c2] ~c:conclusion;
	    conclusion::rest
	  end  
	else (* dismatch flag and c2 is redundant *)
	  (
	   (*  out_str "Dismatch unsat for Side Clause\n";*)
	   rest)	
      in 
      List.fold_left f [] c_c_param_list2 
    end    
  else (* dismatch flag and c1 is redundant *)
    (
     (* out_str "Dismatch unsat for Main Clause\n";*)
     [])




(*------------------Commented--------------------------*)
(*


(*------------- Instantiation ------------------*)

(* Works but slow....*)
(*
(*--------------Feature Index Version--------------------*)
  let is_not_redundant_feature subst_norm clause =
(*   out_str_debug 
     ("---------Constr Check-------\n");    *)
  if (not !current_options.inst_dismatching) 
  then true
  else
  begin
  try
  let dismatching = Clause.get_dismatching clause in
(*    out_str_debug 
      ("Inst Clause: "^(Clause.to_string clause)
      ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
      ^"Subs_to_check: "^(Subst.to_string subst_norm)^"\n"); *)
  if (Dismatching.check_constr_feature_list subst_norm dismatching)
  (*(Dismatching.check_constr_feature_list subst_norm dismatching)*)
  then
  ( (*out_str_debug "Constr. is Satisfied \n";*)
(* we don't need to add all subt_norm but only vars that occurred in mgu *)
  let new_constr =  Dismatching.create_constr_norm subst_norm in
  Dismatching.add_constr_feature_list dismatching new_constr;
  (*    Clause.assign_dismatching 
	( ) clause;*)
  (*(Dismatching.add_constr_feature_list dismatching new_constr);*)
  true)
  else
  ((*out_str_debug "Constr. is NOT Satisfied \n";*)
  incr_int_stat 1 inst_num_of_dismatching_blockings;
  false) 
  with Clause.Dismatching_undef -> 
  (let new_dismatching =
  (Dismatching.create_constr_feature_list ()) in
  (* let new_dismatching =
     (Dismatching.create_constr_feature_list ()) in*)
  let new_constr = Dismatching.create_constr_norm subst_norm in
  Dismatching.add_constr_feature_list new_dismatching new_constr; 
  Clause.assign_dismatching new_dismatching clause;
  (* (Dismatching.add_constr_feature_list new_dismatching new_constr);   
     Clause.assign_dismatching new_dismatching clause;*)
  (*out_str_debug "Constr. is empty\n";*)
  true)
  end
 *)


(****************old version, not correct*********)
(*
  let is_not_redundant_inst bound bsubst clause = 
(*  if (SubstBound.is_proper_instantiator bsubst bound)     *)
(*  then proper inst checked first because applies to many clauses with the same lit*)
(*  out_str_debug  "\n-------Constr Check-------\n";*)
  try
  let dismatching = Clause.get_dismatching clause in
  out_str_debug (
  "Inst Clause: "^(Clause.to_string clause)
  ^"  Bound: "^(string_of_int bound)^"\n"      
  ^"Constraint: "^"["^(Dismatching.constr_list_to_string dismatching)^"]"^"\n"
  ^"Subs_to_check: "^(SubstBound.to_string bsubst)^"\n"); 
  if (Dismatching.check_constr_list bound bsubst dismatching)
  then
  (out_str_debug "Constr. is Satisfied \n";
  true)
  else 
  (out_str_debug "Constr. is NOT Satisfied \n";
  false) 
  with Clause.Dismatching_undef -> 
  (*out_str_debug "Constr. is empty";*) true 
(*  else false*)

(* instantiates adding dismatching constr to the parent--clause *)
  let instantiate_clause term_db_ref bound bsubst clause =
  let concl_clause = Clause.apply_bsubst term_db_ref bsubst (bound,clause) in
  let new_constr = Dismatching.create_constr term_db_ref bound  bsubst in
  try    
  let dismatching = Clause.get_dismatching clause in
  Clause.assign_dismatching (Dismatching.add_constr dismatching new_constr) clause;
  concl_clause
  with 
  Clause.Dismatching_undef -> 
  let empty_dism = Dismatching.create_constr_list () in
  let new_dism = Dismatching.add_constr empty_dism new_constr in
  Clause.assign_dismatching new_dism clause;
  concl_clause

(* {num_of_dismatch_blockings = ref 0;*)
(*     num_of_non_proper_inst = ref 0}*)

  let instantiation term_db_ref c1 l1 compl_l1 c_list2 l2 =
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
  let conc1 = 
  if (SubstBound.is_proper_instantiator mgu 1) 
  then  
  if (is_not_redundant_inst 1 mgu c1)
  then 
  [(instantiate_clause term_db_ref 1 mgu c1)]
  else 
  (
  [])
  else
  (
  incr_int_stat 1 inst_num_of_non_proper_insts;
  [])
  in    
  let conc2 =
  if (SubstBound.is_proper_instantiator mgu 2) then    
  let f rest clause = 
  if (is_not_redundant_inst 2 mgu clause)
  then 
  (instantiate_clause term_db_ref 2 mgu clause)::rest
  else 
  (
  rest)
  in
  List.fold_left f [] c_list2
  else
  (
  incr_int_stat 1 inst_num_of_non_proper_insts;
  [])
  in conc1@conc2

 *)
(*******************old version end*************)



(*
(************** Eq Axioms Special treatment ******************)
(* yet doesnot work..... see fof_eq_reduced_19May_bugs_all.txt for ex.*)
(* instantiation first check duplicates then dismatching constraints*)
  let instantiation_norm_dc dismatch_switch term_db_ref clause_db_ref c1 l1 compl_l1 c_list2 l2 =
  let mgu = Unif.unify_bterms (1,compl_l1) (2,l2) in
(*debug*)
(*  out_str_debug ("Main Clause:"^(Clause.to_string c1)^"\n"
    ^"Constr: "^(dismatching_string c1)^"\n" 
    ^"Sel Lit: "^(Term.to_string l1)^"\n"
    ^"Conj Dist: "^(string_of_int (Clause.get_conjecture_distance c1))^"\n"); *)
  let conjecture_distance_c1 = (Clause.get_conjecture_distance c1) in    
  let min_conj_dist = Clause.get_min_conjecture_distance (c1::c_list2) in
  let c1_is_eq = Clause.get_bool_param Clause.eq_axiom c1 in
  let c1_is_input_under_eq = Clause.get_bool_param Clause.input_under_eq c1 in
  let c_list2_has_eq = 
  (List.exists (Clause.get_bool_param Clause.eq_axiom) c_list2) in
  let c_list2_has_input_under_eq = 
  (List.exists (Clause.get_bool_param Clause.input_under_eq) c_list2) in
  let c_list2_all_eq_ax = 
  (List.for_all (Clause.get_bool_param Clause.eq_axiom) c_list2) in

  (* inference is not needed for eq_ax with input_under_eq = false *) 
  try    
  let conc1 = 
  if ((c1_is_eq & (not c_list2_has_input_under_eq)) 
  || ((not c1_is_input_under_eq ) & (c_list2_all_eq_ax)))
  then raise Main_concl_redundant
  else
  if (SubstBound.is_proper_instantiator mgu 1) 
  then  
  let (inst_clause,subst_norm) = 
  (Clause.apply_bsubst_norm_subst term_db_ref mgu 1 c1)
  in
  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
  then 
  (
  incr_int_stat 1 inst_num_of_duplicates;

(*	   out_str_debug ("Clause is already In DB: "
  ^(Clause.to_string inst_clause)^"\n");*)
(*debug*) 
  let cl_in_db = ClauseAssignDB.find inst_clause !clause_db_ref in
  (if (((not (Clause.get_bool_param Clause.input_under_eq cl_in_db))
  & c1_is_input_under_eq)
  || 
  ((not (Clause.get_bool_param Clause.eq_axiom cl_in_db))
  & c1_is_eq)) 
  then 
  out_str "\n Inf_Rules: Cluase in DB weaker than not added!\n"
  else());
(*end debug*)
  raise Main_concl_redundant)
  else
  if  (is_not_redundant_inst_norm subst_norm c1)
  then 
  let added_clause = 
  (ClauseAssignDB.add_ref inst_clause clause_db_ref) in
  let new_conj_dist = min_conj_dist +1
  (*((min_conj_dist_list2 + conjecture_distance_c1) lsr 2)+1*) in
  assign_param_clause c1 new_conj_dist  added_clause;
  (if (c1_is_eq || (c1_is_input_under_eq & c_list2_has_eq))
  then 
  (Clause.set_bool_param true Clause.input_under_eq added_clause;
  Clause.inherit_bool_param Clause.eq_axiom c1 added_clause)    
  else  ()); (* by default added_clause has false param*)		
  [added_clause]
  else 
  (
  raise Main_concl_redundant)
  else
  (
  incr_int_stat 1 inst_num_of_non_proper_insts;

(*       out_str_debug ("Non-proper Inst Main\n");*)
  [])
  in    
  let conc2 =
  if ((not (Term.get_fun_bool_param Term.inst_in_unif_index l1))& 
  (SubstBound.is_proper_instantiator mgu 2)) then    
  let f rest clause =
(*debug*)
(*	out_str_debug  ("Side Clause:"^(Clause.to_string clause)^"\n"
  ^"Constr: "^(dismatching_string clause)^"\n" 
  ^"Sel Lit: "^(Term.to_string l2)^"\n");*)
  let clause_is_eq =  (Clause.get_bool_param Clause.eq_axiom clause) in
  if (clause_is_eq & (not c1_is_input_under_eq)) 
  then rest 
  else
  let (inst_clause,subst_norm) = 
  Clause.apply_bsubst_norm_subst term_db_ref mgu 2 clause 
  in
  if (ClauseAssignDB.mem inst_clause !clause_db_ref)
  then (
  incr_int_stat 1 inst_num_of_duplicates;
(*	      out_str_debug ("Clause is already In DB: "
  ^(Clause.to_string inst_clause)^"\n");*)
(*debug*)
  let cl_in_db = ClauseAssignDB.find inst_clause !clause_db_ref in
  (if (((not (Clause.get_bool_param Clause.input_under_eq cl_in_db))
  &
  (Clause.get_bool_param Clause.input_under_eq clause))
  || 
  ((not (Clause.get_bool_param Clause.eq_axiom cl_in_db))
  & (Clause.get_bool_param Clause.eq_axiom clause )))
  then 
  out_str "\n Inf_Rules: Cluase in DB weaker than not added!\n"
  else());
(*end debug*)
  rest)
  else
  if  (is_not_redundant_inst_norm subst_norm clause)
  then 
  (let added_clause = 
  ClauseAssignDB.add_ref inst_clause clause_db_ref in
  (* let new_conj_dist = 
     ( ((Clause.get_conjecture_distance clause) + 
     conjecture_distance_c1) lsr 2)+1 in*)
  let new_conj_dist = (Clause.get_min_conjecture_distance [clause;c1])+1 in
  assign_param_clause clause new_conj_dist added_clause;
  (if 
  (
  (clause_is_eq (*&
		  (c1_is_eq || c1_is_input_under_eq)*))
  ||
  ((Clause.get_bool_param Clause.input_under_eq clause) &
  c1_is_eq))
  then 
  (Clause.set_bool_param true Clause.input_under_eq added_clause;
  Clause.inherit_bool_param Clause.eq_axiom clause added_clause)    
  else  ());
  added_clause::rest)
  else 
  (

(*	     out_str_debug ("Dismatching \n");*)
  rest)	  
  in
  List.fold_left f [] c_list2
  else
  (
  incr_int_stat 1 inst_num_of_non_proper_insts;
(* debug*)   
  (*  (if (Term.get_fun_bool_param Term.inst_in_unif_index l1) 
      then 	 
      out_str ("Side is In Unif Index: "^(Term.to_string l1)^"\n")
      else
      out_str_debug ("Non-proper Inst Side\n")
      );*)
  [])
  in 
  let concl_list = conc1@conc2 in
(*   out_str_debug 
     ("\n Conclusions:\n"^(Clause.clause_list_to_string concl_list)^"\n"
     ^"------------------------------------------------\n");*)
  concl_list
  with 
  Main_concl_redundant -> 
(*      out_str_debug 
	(" ---------Main_concl_redundant ----------\n");*)
  []	      


(*------------- End Eq Axioms Special treatment comment----------------*)
 *)



 *)


(*------------------End Commented--------------------------*)
