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
let proof = false

(*max number of symbol groups used in feature vector*)
let max_num_of_symb_groups = 5

(* number of sym groups can be changed if number of symbols 
  is less than max_num_of_symb_groups *)
let actual_num_of_symb_groups_ref = ref max_num_of_symb_groups

type clause = Clause.clause
type lit = Term.literal

exception Unsatisfiable
exception Satisfiable
exception DontKnow
exception Eliminated
exception Picked_clause_is_dead
exception Passive_Empty

(*let selection_fun = Selection.kbo_sel_max *)
let selection_fun  = Selection.literal_neg_selection_max

let symbol_db_ref  = Parsed_input_to_db.symbol_db_ref

let neg_symb       = Symbol.symb_neg

let term_db_ref    = Parsed_input_to_db.term_db_ref
let init_clause_list_ref = Parsed_input_to_db.clause_list_ref
let clause_db_ref = ref (ClauseAssignDB.create_name "Discount_Clauses_DB")

(* susbetsubsumption index*)
let ss_index_ref = ref (SubsetSubsume.create ())


(*********statistics*********)
let num_of_forward_subset_subsumed  = ref 0
let num_of_backward_subset_subsumed = ref 0
let num_of_forward_subsumed = ref 0 
let num_of_backward_subsumed = ref 0 
let num_of_tautology_del = ref 0
let num_of_discount_iter = ref 0
let num_in_passive       = ref 0     
let out_statistics () = 
  out_str 
    ("num_of_forward_subset_subsumed: "
     ^(string_of_int !num_of_forward_subset_subsumed)^"\n"
     ^"num_of_backward_subset_subsumed: "
     ^(string_of_int !num_of_backward_subset_subsumed)^"\n" 
     ^"num_of_forward_subsumed: "
     ^(string_of_int !num_of_forward_subsumed)^"\n"
     ^"num_of_backward_subsumed: "
     ^(string_of_int !num_of_backward_subsumed)^"\n"
     ^"num_of_tautology_del: "
     ^(string_of_int !num_of_tautology_del)^"\n"
     ^"num_of_clauses_in_db: "
     ^(string_of_int (ClauseAssignDB.size !clause_db_ref))^"\n"
     ^"num_in_passive: "
     ^(string_of_int !num_in_passive)^"\n"
     ^"num_of_discount_iterations: "
     ^(string_of_int !num_of_discount_iter)^"\n")


module SizeQueueElem = 
  struct
    type t = clause
    let compare c1 c2 = 
      let cmp = compare (Clause.num_of_symb c1) (Clause.num_of_symb c2) in 
      if cmp = 0 then 
       Clause.compare c1 c2
      else -cmp 	  
  end

module SizeQueue = Heap.Functional (SizeQueueElem) 
let size_queue_ref = ref (SizeQueue.empty)

module AgeQueueElem = 
  struct
    type t = clause
    let compare c1 c2 = 
      let cmp = compare (Clause.when_born c1) (Clause.when_born c2) in 
      if cmp = 0 then 
	Clause.compare c1 c2
      else -cmp 	  
  end

module AgeQueue = Heap.Functional (AgeQueueElem) 
let age_queue_ref = ref (AgeQueue.empty)

type passive_ratio = {mutable size : int; mutable age : int}

(* the algorithm picks from the queue 
   with non zero current_passive_ratio.parameter; if all are 0 
   then it goes to the initial state i.e. 
   assigns passive_ratio to current_passive_ratio *)

let init_passive_ratio () = {size = 10; age = 5} (* param should be >= 0*)
let current_passive_ratio_ref =  ref (init_passive_ratio ())

let rec remove_from_passive () = 
  if 
    ((!size_queue_ref = SizeQueue.empty) ||
    (!age_queue_ref = AgeQueue.empty))
  then
(* since we add all clauses to all queues it is enough that one queue is empty*)
    raise Passive_Empty 
  else
    if (!(current_passive_ratio_ref).size > 0)     
    then 
      let clause =  SizeQueue.maximum !(size_queue_ref) in 
      size_queue_ref := SizeQueue.remove !(size_queue_ref);
      !(current_passive_ratio_ref).size <- !(current_passive_ratio_ref).size - 1;
      clause
  else 
      if (!(current_passive_ratio_ref).age > 0)
      then 
	let clause =  AgeQueue.maximum !(age_queue_ref) in 
	age_queue_ref := AgeQueue.remove !(age_queue_ref);
	!(current_passive_ratio_ref).age <- !(current_passive_ratio_ref).age - 1;
	clause
      else 
        (* we have (!(current_passive_ratio_ref).size = 0 *)
	(* and !(current_passive_ratio_ref).age = 0) *)
	(current_passive_ratio_ref := init_passive_ratio ();
	 remove_from_passive ())

        
(*debug*)
let stat_count_ref = ref 0 
   
let add_to_passive clause = 
  size_queue_ref := 
    SizeQueue.add clause !(size_queue_ref); 
  age_queue_ref := 
    AgeQueue.add clause !(age_queue_ref);
  num_in_passive:=!num_in_passive+1
(* debug *)
(*  ( if ((!num_in_passive - !stat_count_ref) > 10000) 
  then 
    (out_statistics (); 
     stat_count_ref:= !num_in_passive))
*)
  



(* can not make local db's since types are not all defined 
   like for unif_index 

   type all_dbs = 
   { 
    term_db_ref   : TermDB.termDB ref;
    clause_db_ref : ClauseAssignDB.clauseDB ref;
    ss_index_ref  : SubsetSubsume.index ref;
    passive_queue_ref : PassiveQueue.t ref
   (*  unif_index_ref : 
    unfortunatelly its type is defined only in the start_discount  *)
    }
*)
   


(* subsumption feature index see Schulz*)
module Feature = 
  struct  
    type t = int 
    let  compare = compare
  end

(*returns pair of (max size positive,max size neg) used to get a feature *)
let rec get_max_size_of_literal = function 
  |h::tl -> 
      let h_size = Term.get_num_of_symb h in
      let (max_pos_tl,max_neg_tl) = get_max_size_of_literal tl in
      ( match h with 
      | Term.Fun(sym,_,_) -> 
	  if sym == neg_symb 
	  then
	    if  h_size > max_neg_tl
	    then (max_pos_tl,h_size)
	    else (max_pos_tl,max_neg_tl) 
	  else 
	    if h_size > max_pos_tl 
	    then (h_size,max_neg_tl)
	    else (max_pos_tl,max_neg_tl) 
      |_-> failwith "discount get_max_size_of_literal"
       )
  |[] -> (0,0) 

let rec num_of_neg = function 
  |h::tl -> 
     ( match h with 
     | Term.Fun(sym,_,_) -> 
	  if  sym == neg_symb
	  then 1+(num_of_neg tl)
	  else (num_of_neg tl)
      |_-> failwith "discount num_of_neg"
      )
  |[]-> 0 

(*this should be done only once in the start_discount*)
let partition_symbols num_of_groups = 
  let current_group_ref = ref 0 in 
  let f s =  
    (if !current_group_ref >= num_of_groups
    then
      current_group_ref:= 0
    ); 
    (Symbol.assign_group s !current_group_ref;
     current_group_ref := !current_group_ref +1)in
  SymbolDB.iter f !symbol_db_ref

let get_sym_group_features num_of_groups clause= 
  let group_array = Array.make num_of_groups 0 in
  let f () sym = 
    let sym_group = Symbol.get_group sym in
   group_array.(sym_group) <- (group_array.(sym_group) +1) in
  Clause.fold_sym f () clause;
  Array.to_list group_array

let get_feature_list (clause:clause) = 
  let sym_group_feature_list = 
    get_sym_group_features !actual_num_of_symb_groups_ref clause in
  let feature1 = Clause.num_of_symb clause in
  let feature2 = Clause.length clause in
  let (feature3,feature4) = get_max_size_of_literal (Clause.get_literals clause) in
  let feature5 = num_of_neg  (Clause.get_literals clause) in
  (*out_str_debug 
    ("Clause: "^(Clause.to_string clause)
     ^"Feature list: ["
     ^(list_to_string string_of_int sym_group_feature_list ",")^"]\n");*)
  sym_group_feature_list@[feature1;feature2;feature3;feature4;feature5]
 
module SubsumptionIndexM = SubsumptionIndex.Make(Feature)
let subsumption_index_ref = ref (SubsumptionIndexM.create ())



module DTParam = 
  struct let num_of_symb = (SymbolDB.size !symbol_db_ref) end 
module DiscrTreeM = DiscrTree.Make(DTParam)  

(* all clauses with the same literal put together, 
   assoc list with == *)
type unif_index_elem = (lit*(clause list)) list
let (unif_index_ref : (unif_index_elem DiscrTreeM.index) ref ) 
    = ref (DiscrTreeM.create ())



let out_proof s = 
  if proof then out_str s
  else ()
    
let compl_lit literal = 
  match literal with 
  | Term.Fun(sym,args,_) -> 
      if sym ==neg_symb
      then List.hd (Term.arg_to_list args)  
      else Term.create_fun_term neg_symb [literal]
  |_-> failwith "term: compl_lit it is not a literal" 


(******** tautology delition********)	
let is_complementary l1 l2 =
  match l1 with 
  | Term.Fun(sym1,args1,_) -> 
      if  sym1 == neg_symb 
      then 
	if l2 == (List.hd (Term.arg_to_list args1))  
	then true 
	else false	    
      else (*l1 is positive*)
	(match l2 with 
	|Term.Fun(sym2,args2,_) -> 
	    if sym2 == neg_symb
	    then 
	      if l1 == (List.hd (Term.arg_to_list args2))  
	      then true 
	      else false	
	    else false
	|_ ->  failwith "term: is_compl it is not a literal" 
	)
  |_-> failwith "term: is_compl it is not a literal" 

let rec coml_in_list lit_list =
  match lit_list with 
  |l::tl ->   
      let exists = List.exists (is_complementary l) tl in
      if exists then exists
      else coml_in_list tl 
  |[] -> false
	
let is_tautology clause = 
  let lit_list = Clause.get_literals clause in
  coml_in_list lit_list


(*     add to ss_index   *)
let add_to_ss_index clause = 
  try 
    ss_index_ref := SubsetSubsume.add_clause clause !(ss_index_ref);    
    Clause.set_bool_param 
      true Clause.in_subset_subsumption_index clause;
  with
    _-> 
      failwith 
	"discount add_to_ss_index: should be checked on subsest subs before adding "
	
(************eliminates clause!*****************)

let eliminate_from_unif_index main_clause = 
  let selected_literals = selection_fun main_clause in
  (*out_str_debug 
    ("Trying to elim from Unif index:"
     ^(Clause.to_string main_clause)
     ^" Literals: "
     ^(Term.term_list_to_string selected_literals)^"\n");
  *)
  let elim_lit sel_lit =   
   
      let ind_elem = DiscrTreeM.find sel_lit !unif_index_ref
      (* failwith "discount:  eliminate_from_unif_index lit is in unif_index"     *)
      in
      ( match !ind_elem with 
      |Elem(old) ->
	  ( (* old = [[L1,[C_1,..,Cn]],[L2,[C'_1,..,C'n']],..]  
	       old_clause_list = [C_1,..,Cn] corr to sel_lit*)
	    try 
	      let old_clause_list  = List.assq sel_lit old in 
        (*  out_str_debug 
	    ("Elem From Unif index old_cl_list:"
	       ^(Clause.clause_list_to_string old_clause_list)^"\n"); *)   
	      let old_with_removed = List.remove_assq sel_lit old in
	      
(*remove main_clause*)     
	      let new_clause_list = 
		List.find_all (fun cl -> not(cl == main_clause)) old_clause_list in
	      (* out_str_debug 
		 ("Elem From Unif index new_cl_list:"
		 ^(Clause.clause_list_to_string new_clause_list)^"\n"); *)
              if new_clause_list = [] 
	      then 
 		if  old_with_removed = []
		then
		  (DiscrTreeM.remove_term_path sel_lit unif_index_ref
                     (*; out_str_debug 
		       ("Elim unif Removed term path"
		       ^(Term.to_string sel_lit)^"\n")*))
		else 
		  (ind_elem := Elem(old_with_removed)
                      (*; out_str_debug 
			("Elim unif: Old_with_removed")*))
	      else 	    
		(ind_elem := 
		  Elem((sel_lit,new_clause_list)::old_with_removed)
             (*;out_str_debug 
		 ("Elim unif: Old_with_removed")*) )		
	  with 
	      Not_found -> ()
	   )
      | Empty_Elem -> 
	  failwith "discount: eliminate_from_unif_index  \
	  unif index should not contain Empty_Elem"  
       ) in
  try
    List.iter elim_lit selected_literals;
  with
    Not_found -> ();  
  Clause.set_bool_param  
    false Clause.in_unif_index main_clause 

(* eliminates clause from all indexes 
   but not from ss_index and not from subsumtion index*)
    
let eliminate_clause clause = 
  Clause.set_bool_param 
    true Clause.is_dead clause;
  if (Clause.get_bool_param Clause.in_active clause) 
  then 
    (eliminate_from_unif_index clause;
     Clause.set_bool_param false Clause.in_active clause)
  else ()(*;*)   
  (*if (Clause.get_bool_param Clause.in_clause_db clause) 
  then  
    clause_db_ref:= ClauseAssignDB.remove clause !clause_db_ref
  else ()
*)

(***************simplify light******************)
let simplify_light_forward_new clause = 
  if (is_tautology clause) 
  then 
    ((*out_str_debug 
       ("Simplified tautology: "
	^(Clause.to_string clause));*)        
     num_of_tautology_del:= !num_of_tautology_del + 1;  
     raise Eliminated)
  else
    if (SubsetSubsume.is_subsumed clause  !(ss_index_ref)) 
    then
      ((* out_str_debug 
	 ("Simplified forward: "
	  ^(Clause.to_string clause)); *) 
       num_of_forward_subset_subsumed:= !num_of_forward_subset_subsumed + 1;
       raise Eliminated)
    else
      clause (* in futer clause can be modified *)
	

let simplify_light_backward_new main_clause = 
  try 
    let subsumed_clauses = SubsetSubsume.find_subsumed main_clause !ss_index_ref in
   (* out_str_debug (
    "Backward Subsumed: "
    ^(Clause.clause_list_to_string subsumed_clauses)
    ^"   By: "^(Clause.to_string main_clause));*)
      List.iter eliminate_clause subsumed_clauses;
    num_of_backward_subset_subsumed := 
      !num_of_forward_subset_subsumed + (List.length subsumed_clauses);
    ss_index_ref :=  SubsetSubsume.remove_subsumed main_clause !ss_index_ref     
  with 
    SubsetSubsume.No_subsumed -> ()
	
(*************add new clauses*******)    
let add_new_clause_to_passive picked_clause clause = 
  if (Clause.is_empty_clause clause) 
  then
    ((*out_proof 
      ("---------Proof-----------\n"
       ^(Clause.to_string_history clause));*)
     raise Unsatisfiable
    )
  else 
    if (not (Clause.get_bool_param Clause.is_dead clause))
    then     
      try 
	let main_clause = simplify_light_forward_new clause in
	simplify_light_backward_new main_clause;        
	let added_clause = 
	  ClauseAssignDB.add_ref main_clause clause_db_ref in 
	Clause.assign_when_born !num_of_discount_iter added_clause;
	add_to_passive added_clause;
(*	passive_queue_ref := 
	  PassiveQueue.add added_clause !(passive_queue_ref);        
	Clause.set_bool_param true Clause.in_passive added_clause;*)
	(* one might also add to full subsumption index*)  
	add_to_ss_index added_clause;
	if  (Clause.get_bool_param Clause.is_dead picked_clause)
	then raise Picked_clause_is_dead 
             (* we abort all further 
		inferences with the picked clause,
                later we can add to eliminate also all other conclusions
		with this clause but not this one!, 
		also in general after backward subsumption we can eliminate 
                all children of the subsumed clause provided that we add 
                the clause which subsumes to the clause set*)
	else ()
      with 
	Eliminated -> ()
    else ()  



(************all factorings*********)
let rec all_factorings'  main_clause sel_lit rest_sel_lits = 
  match rest_sel_lits with
  | l::tl ->
      (try 
	let conclusion = 
	  Inference_rules.factoring main_clause sel_lit l term_db_ref in
	add_new_clause_to_passive main_clause conclusion;
	(*out_str_debug ("\n Factoring: "^(Clause.to_string main_clause)
		       ^" conclusion: "^(Clause.to_string conclusion));*)
	all_factorings'  main_clause sel_lit tl
      with Unif.Unification_failed  -> ()
      )
  |[] -> ()      

	
let rec all_factorings  main_clause selected_literals =
  match  selected_literals with 
  |l::tl ->  
      all_factorings'  main_clause l tl;
      all_factorings  main_clause tl
  |[] -> ()

	
(*******all resolutions********)

let  all_resolutions  main_clause selected_literals = 
  let for_all_sel_lit sel_lit =    
    let compl_sel_lit = compl_lit sel_lit in
    let unif_candidates = 
      DiscrTreeM.unif_candidates !unif_index_ref compl_sel_lit in
    let for_all_candidates (lit,clause_list) =       
      (try 
	(* out_str_debug ("res_try: "^(Clause.to_string main_clause)
		       ^(Clause.clause_list_to_string clause_list)); *)
	let conclusion_list = 
	  Inference_rules.resolution 
	    main_clause sel_lit compl_sel_lit clause_list lit term_db_ref in	
	(* out_str_debug 
	  ("resolution: "^(Clause.to_string main_clause)
	    ^"["^(Clause.clause_list_to_string clause_list)^"]"   
	    ^"conclusion: "
	   ^"["^(Clause.clause_list_to_string conclusion_list)^"]");*)
	List.iter (add_new_clause_to_passive main_clause) conclusion_list    
      with Unif.Unification_failed  -> ()       
      ) in	
    List.iter for_all_candidates unif_candidates in  
  List.iter for_all_sel_lit selected_literals
      
      
(* add to unif index *)
      
let add_to_unif_index main_clause selected_literals = 
  let add_lit sel_lit = 	 
    let ind_elem = DiscrTreeM.add_term_path sel_lit unif_index_ref in
    (match !ind_elem with 
    |Elem(old) -> 
	(try
	  let old_clause_list =  List.assq sel_lit old in 
	  let old_with_removed = List.remove_assq sel_lit old in
	  ind_elem := 
	    Elem((sel_lit,(main_clause::old_clause_list))::old_with_removed)
	with Not_found ->  ind_elem := Elem((sel_lit,[main_clause])::old)
	)	     
    |Empty_Elem   -> 	 
	ind_elem := Elem([(sel_lit,[main_clause])])
    )     
  in 
  List.iter add_lit selected_literals;
  Clause.set_bool_param true Clause.in_unif_index main_clause
    

(* add_to_subsumption_index *)
(*add later !!!*)
let add_to_subsumption_index feature_list main_clause =
  SubsumptionIndexM.add_clause feature_list main_clause subsumption_index_ref

let simplify_forward_heavy_old feature_list main_clause = 
(* do not need light simplifications since light backward *)
  match  
    (SubsumptionIndexM.is_subsumed 
       feature_list  main_clause subsumption_index_ref)
  with
  |Some(_) ->
      (num_of_forward_subsumed:= !num_of_forward_subsumed + 1; 
       raise Picked_clause_is_dead )
  |None -> main_clause 
	

let simplify_backward_heavy feature_list main_clause = 
  let b_subsumed_list = 
    (SubsumptionIndexM.find_subsumed 
       feature_list main_clause subsumption_index_ref) in
  if b_subsumed_list != [] 
  then
    (List.iter eliminate_clause b_subsumed_list;
     num_of_backward_subsumed:= 
       !num_of_backward_subsumed + (List.length b_subsumed_list)) 
  else ()

(*******discount loop***********)
    
let rec discount_loop () =
  while true do  
    num_of_discount_iter := !num_of_discount_iter + 1;  
    try  
     (* let clause =  PassiveQueue.maximum !(passive_queue_ref) in 
      passive_queue_ref := PassiveQueue.remove !(passive_queue_ref);*)
      let clause = remove_from_passive () in
      (*out_str_debug ("removed form passive"^(Clause.to_string clause));*)
      if ((Clause.get_bool_param Clause.is_dead clause) ||
      (Clause.get_bool_param Clause.in_active clause))
      then ()      
      else 
	(try
	  let feature_list = (get_feature_list clause) in
	  let picked_clause = simplify_forward_heavy_old feature_list clause in
	(* Clause.set_bool_param false Clause.in_passive picked_clause; *)	
          simplify_backward_heavy feature_list picked_clause; 
	  let selected_literals = selection_fun picked_clause in
	  (*out_str_debug (" picked_clause: "^(Clause.to_string  picked_clause)
			 ^"selected lit: "
			 ^(Term.term_list_to_string selected_literals));  *)
          
	  all_factorings   picked_clause selected_literals;          
	  all_resolutions  picked_clause selected_literals;
	  add_to_unif_index  picked_clause  selected_literals;
	  Clause.set_bool_param true Clause.in_active  picked_clause;       
(* alternatively one can add all newly generated to subsumption also  *)
	  add_to_subsumption_index feature_list picked_clause;
(*	  out_str_debug 
	    ("\n In Active: "^(Clause.to_string picked_clause)) *)
	    (* else () *)
	with 
	|Eliminated -> () 
	|Picked_clause_is_dead -> ()
               (*out_str_debug "\n Picked_clause_is_dead \n"*)
	)
    with 
      Passive_Empty -> raise Satisfiable
  done
    
    
let start_discount () = 
  let num_of_symb = SymbolDB.size !symbol_db_ref in
  (if  num_of_symb < !actual_num_of_symb_groups_ref
  then actual_num_of_symb_groups_ref := num_of_symb);  
  partition_symbols !actual_num_of_symb_groups_ref;
    let add_clause clause = 
      add_new_clause_to_passive clause clause
    in
    List.iter add_clause !init_clause_list_ref;
    (* ClauseAssignDB.iter add_caluse !init_clause_db_ref; *)
   (* out_str_debug "initial clauses are added to passive \n";*)
    try  discount_loop () with
    |Unsatisfiable -> 
	out_str "PROVED\n";
	out_statistics ()	  	
    |Satisfiable   -> 
	out_str "SATISFIABLE\n";  
	out_statistics ()


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
  (if  num_of_symb < !actual_num_of_symb_groups_ref
  then actual_num_of_symb_groups_ref := num_of_symb);  
  partition_symbols !actual_num_of_symb_groups_ref;
  let add_clause clause = 
    out_str_debug ("Adding init cl to passive: "^(Clause.to_string clause)^"\n");
    add_new_clause_to_passive clause clause;
    SubsumptionIndexM.add_clause  
      (get_feature_list clause) clause subsumption_index_ref
  in
  List.iter add_clause !init_clause_list_ref;
    out_str_debug "initial clauses are added to passive and subsumtion index\n";
   ClauseAssignDB.iter 
      (fun c ->out_str_debug ("Clause in db: "^(Clause.to_string c)^"\n"))
    !clause_db_ref ; 
  iter_all_pairs_of_clauses try_subsumption 
 (* uncomment for index subsumption
 let try_forward_subs clause = 
    ( match 
      (SubsumptionIndexM.is_subsumed 
	 (get_feature_list clause) clause subsumption_index_ref) 
    with 
    |Some((subsumer,subst)) -> 
	out_str_debug 
	  ("Clause"^(Clause.to_string clause)^" is subsumed by "
	   ^(Clause.to_string subsumer)^"\n")
    |None -> 
  	out_str_debug 
	  ("Clause"^(Clause.to_string clause)^" can not be subsumed \n")
     ) in
  ClauseAssignDB.iter try_forward_subs !clause_db_ref
*)

    
    
    
    
    
