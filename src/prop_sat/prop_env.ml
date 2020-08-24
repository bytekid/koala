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

(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_ur
  | D_br
  | D_prep

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_ur -> "ur" (* unit resolution *)
  | D_br -> "br" (* binary resolution *)
  | D_prep -> "prep"

let dbg_groups =
  [
(*   D_trace;  *)
   D_ur;
   D_br;
   D_prep
 ]

let module_name = "prop_env"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


(*----- uncomment for backtrace in debug mode --------*)
(*
let _ = Printexc.record_backtrace dbg_flag
*)

(*------ signals -------*)

let set_sys_signals () =
  let signal_handler signal =
    if (signal = Sys.sigint || signal = Sys.sigterm || signal = Sys.sigquit)
    then raise Termination_Signal
  in
  Sys.set_signal Sys.sigint (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigterm (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigquit (Sys.Signal_handle signal_handler)
  
let _ = set_sys_signals ()



(*------------------------------------x*)
  
let lit_var_comapre l1 l2 = 
  let (p1,v1) = lit_to_var l1 in 
  let (p2,v2) = lit_to_var l2 in 
  let vid1 = (get_var_id v1) in
  let vid2 = (get_var_id v2) in
  if vid1 = vid2  
  then 
    Pervasives.compare p1 p2
  else 
    Pervasives.compare vid1 vid2

(*
let lit_equal l1 l2 = ((get_lit_id l1) = (get_lit_id l2))
let lit_eq = lit_equal 
*)  

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
  | P_HRes of clause list (* hyper resolution *) 
  | Q_Res of clause

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
     var_dlevel : int; (* not used in func impl. *)
   }	  


let clause_get_lits c = c.lit_list

let clause_cmp_length c1 c2 = 
  Pervasives.compare (List.length (clause_get_lits c1))  (List.length (clause_get_lits c2)) 

let clause_to_string c = (list_to_string lit_to_string c.lit_list " ")^(" "^(string_of_int 0))
									  
let clause_list_to_string c_list = list_to_string clause_to_string c_list "\n"

let out_clause_list c_list = List.iter (fun c -> (out_str (clause_to_string c))) c_list

let get_parents clause = clause.parents
    
(*---- var_model_val -----*)

module VMV_Key = 
  struct 
    type t = var_model_val 
    let compare vmv1 vmv2 = var_compare vmv1.var vmv2.var
  end

module VMV_Map = Map.Make(VMV_Key) 
module VMV_Set = Set.Make(VMV_Key) 

(*--------*)
type model = var_model_val VMap.t (* TODO: change to array of htbl *)

type model_res = 
  |M_False of var_model_val 
  |M_True of var_model_val
  |M_Undef 
      
let create_model () = VMap.empty

let in_model model var  = 
  VMap.mem var model

let find_model model var = 
  VMap.find var model 
    
let mem_model model var = 
  VMap.mem var model 

let remove_model model var = 
  VMap.remove var model

(* assert that var is not in the model *)
let add_to_model model var var_model_val =      
  assert (not (VMap.mem var model)); 
  VMap.add var var_model_val model
    
let check_model model lit = 
  let (pol,var) = lit_to_var lit in 
  try 
    let var_model_val = VMap.find var model in 
    if (pol = var_model_val.var_val) 
    then 
      M_True(var_model_val)
    else
      M_False (var_model_val)
  with 
    Not_found -> M_Undef

let is_true_model model lit = 
  match (check_model model lit) with 
  |M_True _ -> true
  |_ -> false

let var_impl_type_to_string var_impl_type = 
  match var_impl_type with 
  |Implied c -> "i: "^(clause_to_string c)
  |Decided -> "d"

let var_model_val_to_string var_model_val = 
  let lit = var_to_lit var_model_val.var_val var_model_val.var in
  (
   " l: "^(lit_to_string lit)^
   " dlevel: "^(string_of_int  var_model_val.var_dlevel)^
   " ltype: "^(var_impl_type_to_string var_model_val.var_impl_type)
  )

(*-------------*)
let out_model model = 
  out_str "--------- Model ---------";
  let f var var_model_val = 
    let lit = var_to_lit var_model_val.var_val var_model_val.var in
    out_str (lit_to_string lit)
  in
  VMap.iter f model

(*--------*)
let clause_create lit_list parents =       
  let sorted_list = list_remove_duplicates_ordered_non_ptr (List.sort lit_var_comapre lit_list) in 
  {
   lit_list = sorted_list;
   parents = parents
 }



let rec taut_lits lit_list = 
  match lit_list with 
  | l1::l2::tl -> 
      if (is_compl l1 l2) 
      then true 
      else taut_lits (l2::tl)

  | _-> false


let is_tautology c = 
  taut_lits (clause_get_lits c)


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
	

let is_empty_clause c =  (clause_get_lits c) = []
  

(*----------------*)
	
exception Satisfiable of model
exception Unsatisfiable of clause


(*------- parsing -------*)    
    
(* returns list of clauses *)

let parse_str_list_to_int str_list = 
  try
    List.map int_of_string str_list 
  with 
    Failure _ -> 
      (out_str 
         ("\n\n"
          ^"parsing error: not a legal string:\n"
          ^"\""^(String.concat " " str_list)^"\"\n\n"
         );
       failwith ("Parsing error"); 
      )

let parse_str_list_to_int_0 str_list = 
  let int_list_with_0 = parse_str_list_to_int str_list in
  match (list_remove_last int_list_with_0) with 
  |Some (zero, int_list) -> 
      if (zero != 0)
      then 
        (out_str
           ("\n\n"
            ^"parsing error: string is not ending with 0:"
            ^"\""^(String.concat " " str_list)^"\"\n\n"
           );
         failwith ("Parsing error"); 
        )
      else
        int_list (* remove last element *)	  
  |None -> failwith "empty lines should be removed"

           
(* vars lists are used  in qbf *)  
let var_str_list_to_var_list_0 var_str_list = 
  let int_list = parse_str_list_to_int_0 var_str_list in 
  List.map make_var int_list

let lit_str_list_to_lit_list_0 lit_str_list = 
  let int_list = parse_str_list_to_int_0 lit_str_list in 
  List.map make_lit int_list


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
	let str_list = Str.split (Str.regexp "[ \t]+") line in	  
        if (str_list = [])
        then 
          parse acc
        else
	  let lit_list = lit_str_list_to_lit_list_0 str_list in 
	  let clause = clause_create lit_list P_Input in
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
  let lit = var_to_lit var_model_val.var_val var_model_val.var in 
  let compl_mod_lit = compl_lit lit in
  let c_lits = (clause_get_lits c) in
  let new_lits = List.filter (fun l -> not (lit_equal compl_mod_lit l)) c_lits  in

  if (List.length c_lits) = (List.length new_lits)
  then
    c
  else
    (
     let new_parents = 
       match c.parents with 
       | P_Input  | P_BRes _ | P_HRes _ | Q_Res _ -> P_URes c 
       | P_URes _pc -> c.parents 	  		 
     in 
     let result = clause_create new_lits new_parents in 
     dbg D_ur (lazy ("binary resolution"^(clause_to_string result)^" <- "
                     ^":left premise: " ^(lit_to_string lit)^" 0"
                     ^" :right premise: "^(clause_to_string c)));
     result  
    )



let in_clause lit clause = 
  List.exists (lit_equal lit) (clause_get_lits clause)

(* resolve: lit from main_clause *)

let resolve lit main_clause side_clause =             
  let compl_lit = compl_lit lit in
  let main_lits = (clause_get_lits main_clause) in
  let side_lits = (clause_get_lits side_clause) in
  assert (in_clause lit main_clause);
  assert (in_clause compl_lit side_clause);
  let (_,new_main_part) = List.partition (lit_equal lit) main_lits in 
  let (_,new_side_part) = List.partition (lit_equal compl_lit) side_lits in 
  let new_parent =  P_BRes (lit, main_clause, side_clause) in 
  let result = clause_create (new_main_part@new_side_part) new_parent in 
  dbg D_br (lazy ((clause_to_string result)^" <- "
		  ^" :left premise: " (* main *)
		  ^(clause_to_string main_clause)
                  ^" :right premise: " (* side premise*)
		  ^(clause_to_string side_clause)
                  ^" upon l: "^(lit_to_string lit)));
  result

(* binary resolves clause impl literal in the model and c *)
let resolve_model var_model_val c = 
  match var_model_val.var_impl_type with 
  |Implied d -> 
      let lit = var_to_lit var_model_val.var_val var_model_val.var in 
      let dl = var_model_val.var_dlevel in (* for debug *)
      dbg D_trace (lazy ("resolve_model: l: "^(lit_to_string lit)^" d: "^(string_of_int dl)));
      resolve lit d c  

  | Decided -> failwith "resolve_model lit should not be decided"

(* get the clause that is implied by S and is implying c modulo current model *)
let get_implying c = 
  match c.parents with 
  |P_Input | P_BRes _ | P_HRes _ | Q_Res _ -> c
  |P_URes implying -> implying


(* vmv -- var_model_val *)
	
(* returns split: (impl_vmv_set, decided_set); lit_set =  (impl_vmv_set U decided_set) *)

let split_impl_decided model lit_set = 
  let f lit (impl_vmv_set, decided_set) = 
    let vmv =
      match (check_model model lit) with 
      |M_False vmv -> vmv
      |M_True vmv -> failwith "split_impl_decided: lit should be false"
      |M_Undef -> failwith "split_impl_decided: var should be defined"
    in
    match vmv.var_impl_type with 
    |Implied _ -> 
	((VMV_Set.add vmv impl_vmv_set), decided_set)
    |Decided  -> 
	(impl_vmv_set, (LSet.add lit decided_set))
  in
  LSet.fold f lit_set (VMV_Set.empty,LSet.empty)
    
(*----------------*)
let hyper_resolve_model_vmv model implied_vmv_set decided_set c = 

  (* assume c_lits = compl (implied_vmv_set) \cup decided_set *)
  let res vmv (impl_clauses, result_lit_set) = 
    match vmv.var_impl_type with 
    |Implied d -> 
	let lit = var_to_lit vmv.var_val vmv.var in
	let d_lits = clause_get_lits d in
	assert (in_clause lit d);
	let (_, rest_d_lits) = List.partition (lit_equal lit) d_lits in 
	let f rest_lits d_lit = LSet.add d_lit rest_lits in 
	let new_result_lit_set = List.fold_left f result_lit_set rest_d_lits in
	(d::impl_clauses, new_result_lit_set)
    |Decided -> failwith "hyper_resolve_model_vm"
  in
  let (impl_clauses, resolved_impl_lit_set) = VMV_Set.fold res implied_vmv_set ([],LSet.empty) in 
  let all_resolvent_lits = LSet.union resolved_impl_lit_set decided_set in 
  let parents = P_HRes (impl_clauses) in
  let resolvent = clause_create (LSet.elements all_resolvent_lits) parents in     

  let (new_impl_vmv_set, new_extra_decided_set) = split_impl_decided model resolved_impl_lit_set in
  let new_decided_set = LSet.union new_extra_decided_set decided_set in

  (* assume that (new_impl_vmv_set U new_decided_set) = resolvent_lits *)
  (new_impl_vmv_set, new_decided_set, resolvent)
    


let rec hyper_resolve_until_decided_lits model implied_vmv_set decided_set c  =
  if (VMV_Set.is_empty implied_vmv_set) 
  then  
    (implied_vmv_set, decided_set, c)
  else
    let (new_impl_vmv_set, new_decided_set, resolvent) = 
      hyper_resolve_model_vmv model implied_vmv_set decided_set c in
    hyper_resolve_until_decided_lits model new_impl_vmv_set new_decided_set resolvent 
      
      
let lit_list_to_set lit_list = 
  let f rest_set l = LSet.add l rest_set in 
  List.fold_left f LSet.empty lit_list
    

let hyper_resolve_until_decided model c =
  let (implied_vmv_set, decided_set) = split_impl_decided model (lit_list_to_set (clause_get_lits c)) in 
  let (_,_,resolvent) =  hyper_resolve_until_decided_lits model implied_vmv_set decided_set c in 
  resolvent
    
(*-------------*)
    
(*-------------*)


(* watch *)
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
  let compare pv1 pv2 = pair_compare_lex Pervasive.compare compare pv1 pv2
  end
  
  module PQ_Var = Set.Make(PV_Key) (* priority queue implemented as a set; TODO change into list of PQs *)
 *)
      
type var_priority_queue = 
    {
     v_to_pr : int VMap.t; (* var -> priority *)
     pr_to_v : (VSet.t) IntMap.t   (* set ordered with priority *)
   }

let create_var_priority_queue () = 
  {
   v_to_pr = VMap.empty;
   pr_to_v = IntMap.empty;
 }

let mem_pq pq var = VMap.mem var pq.v_to_pr

let remove_var_pq pq var = 
  try 
    let var_priority = VMap.find var pq.v_to_pr in 
    let new_v_to_pr = VMap.remove var pq.v_to_pr in 
    assert (IntMap.mem var_priority pq.pr_to_v);
    let pr_var_set = IntMap.find var_priority pq.pr_to_v in 
    let new_pr_var_set = VSet.remove var pr_var_set in       
    let new_pr_to_v = 
      if (VSet.is_empty new_pr_var_set) 
      then
	IntMap.remove var_priority pq.pr_to_v
      else
	IntMap.add var_priority new_pr_var_set pq.pr_to_v
    in
    {
     v_to_pr = new_v_to_pr;
     pr_to_v = new_pr_to_v;
   }
  with 
    Not_found -> 
      (
       dbg D_trace (lazy ("remove_var_pq: Not_found: v:"^(var_to_string var)));
       pq)
	
(* remove_max_pq_var returns (max_priority_var, rest_queue) *)
(* raises Not_found if the queue is empty *)

let remove_max_var_pq pq =
  let (max_pr,max_pr_var_set) = IntMap.max_binding pq.pr_to_v in (* can raise Not_found *)      	
  dbg D_trace (lazy ("remove_max_var_pq: max_p: "^(string_of_int max_pr)));     
  assert (not (VSet.is_empty max_pr_var_set));
  let max_var = VSet.min_elt max_pr_var_set in (* pick min var in the set *)
  let new_pq = remove_var_pq pq max_var in 
  (max_var, max_pr, new_pq)
    

    

(* we assert that var is not in pq before adding *)
let add_var_pq pr var pq = 
  dbg D_trace (lazy ("add_var_pq: v: "^(var_to_string var)^(" p: ")^(string_of_int pr)));
  let new_v_to_pr = 
    assert (not (VMap.mem var pq.v_to_pr));
    VMap.add var pr pq.v_to_pr
  in
  let new_pr_to_v = 
    try 
      let old_v_set = IntMap.find pr pq.pr_to_v in 
      IntMap.add pr (VSet.add var old_v_set) pq.pr_to_v 
    with 
      Not_found ->  IntMap.add pr (VSet.singleton var) pq.pr_to_v 
  in
  let new_pq = 
    {
     v_to_pr = new_v_to_pr;
     pr_to_v = new_pr_to_v;
   }
  in
  new_pq

(*--------------------*)
type var_score_map = int VMap.t
      
let create_var_score_map () = VMap.empty

let get_var_score var var_score_map = 
  VMap.find var var_score_map
    

let incr_var_score var incr var_score_map = 
  try 
    let current_score = VMap.find var var_score_map in 
    let new_score = current_score + incr in 
    dbg D_trace (lazy ("incr_var_score: v: "^(var_to_string var)^" s: "^(string_of_int new_score)));
    VMap.add var new_score var_score_map
  with 
    Not_found -> 
      VMap.add var incr var_score_map

let update_var_score f var var_score_map = 
  try 
    let current_score = VMap.find var var_score_map in 
    let new_score = f current_score in 
    VMap.add var new_score var_score_map
  with 
    Not_found -> 
      failwith "var_score: Not_found"
        
let unpdate_all_vars_score f var_score_map = 
  let g var score new_map = 
    VMap.add var (f score) new_map
  in 
  VMap.fold g var_score_map VMap.empty 

let assign_var_score var score var_score_map = 
  VMap.add var score var_score_map

(*--------------------*)
    

(* TODO: apply_f_pq apply function to priorities   *)