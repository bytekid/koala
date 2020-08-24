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
open Logic_interface
open Resolution_env

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_trace
  | D_adaptive

let dbg_gr_to_str = function
  | D_trace -> "trace"
  | D_adaptive -> "adaptive"

let dbg_groups =
  [
    D_trace; 
   D_adaptive;
 ]

let module_name = "resolution_sel"


(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

let filter_min_unif_cands unif_index lits = 
  let side_measure_opt = !current_options.res_lit_sel_side in        
  match side_measure_opt with 
  |CM_none ->  lits
  | _ ->  
      begin              
        let cl_measure = Clause.cl_measure_to_fun side_measure_opt in 
        let min_side_lits = 
          ClauseUnifIndex.filter_lits_min_unif_cand unif_index cl_measure lits 
        in
        min_side_lits
      end

(*------------------------*)

(* spltting literals must be smaller than any other; otherwise incomplete (sat in place of unsat) *)

let is_pol_lit ~pol l = (Term.get_sign_lit l) = pol

let is_pol_no_split ~pol l = 
  (is_pol_lit ~pol l) && (not (Term.is_split_lit l))

let filter_pol_lits ~pol lits = 
  List.find_all (is_pol_lit ~pol) lits

let filter_no_split_lits lits = 
  List.find_all (fun l -> (not (Term.is_split_lit l))) lits

let filter_pol_no_split ~pol lits = 
  List.find_all (is_pol_no_split ~pol) lits

(*-----OLD-----*)

let is_neg_no_split l = 
  (Term.is_neg_lit l) && (not (Term.is_split_lit l))

let filter_neg_lits lits = 
  List.find_all Term.is_neg_lit lits

let filter_no_split_lits lits = 
  List.find_all (fun l -> (not (Term.is_split_lit l))) lits

let filter_neg_no_split lits = 
  List.find_all is_neg_no_split lits

(*-----EOLD-----*)

(*-----------------*)
(* filter out literals from whose compliment is in propositional assumptions; we assume that the result is not empty  *)
let get_lits_no_assumptions clause =   
  let lits = Clause.get_lits clause in 
  if (Prop_solver_exchange.is_empty_assumptions ()) 
  then 
    lits
  else
    (
     let res = 
       List.find_all 
         (fun l -> 
           let compl_l = (add_compl_lit l) in
           not (Prop_solver_exchange.mem_assumptions compl_l) || (Prop_solver_exchange.mem_soft_assumptions compl_l))
         lits in 
     (* we allow compl to belong to soft assumptions *)
     assert (res != []);
     res
    )

let get_relevant_lits clause = 
  get_lits_no_assumptions clause

(*----------------------*)
let get_ordering () = 
  match !current_options.res_ordering with 
  | Res_ord_kbo -> Orderings.simple_kbo
  | Res_ord_kbo_pred -> Orderings.simple_kbo_pred

let get_max_kbo_lits lits = 
  let ordering = get_ordering () in
   list_get_max_elements_v ordering lits

(*
let get_max_kbo_lits_cl clause = 
  get_max_kbo_lits (get_relevant_lits clause)
*)

(*let kbo_sel_max clause = get_sel kbo_sel_max' clause see below*)

(* if max is false select min otherwise max wrt to num of symbols. *)
(* can raise Not_found if there are no pol lits *)
let literal_pol_selection' ~max ~pol unif_index lits = 
  let pol_lits = filter_pol_no_split ~pol lits in
  let min_unif_cands = filter_min_unif_cands unif_index pol_lits in  
  let cmp = if max then Term.cmp_num_symb else (fun x y -> - (Term.cmp_num_symb x y)) in
  let pol_literal = list_find_max_element cmp min_unif_cands in
  [pol_literal]
 
let literal_pol_selection_cl ~max ~pol unif_index cl =
  let lits = (get_relevant_lits cl) in
  try
    literal_pol_selection' ~max ~pol unif_index lits
  with 
    Not_found -> (* all lits are opposite pol *)
      get_max_kbo_lits lits

let literal_pol_selection ~max ~pol unif_index cl_param clause = 
  let sel_lits = literal_pol_selection_cl ~max ~pol unif_index clause in   
  res_assign_sel_lits cl_param sel_lits;
  sel_lits

(*------------------OLD----------------*)
(* TODO: refactor *)


(*--------- neg_max -------------*)
(* can raise Not_found if there are no neg lits *)

(*
let literal_neg_selection_max' unif_index lits = 
(*let lit_neg_sel_max_t clause =*)
  let neg_lits = filter_neg_no_split lits in
  let min_unif_cands = filter_min_unif_cands unif_index neg_lits in  
  let neg_literal = list_find_max_element Term.cmp_num_symb min_unif_cands in
  [neg_literal]
  

let literal_neg_selection_max_cl unif_index cl =
  let lits = (get_relevant_lits cl) in
  try
    literal_neg_selection_max' unif_index lits
  with 
    Not_found -> (* all lits are positive*)
      get_max_kbo_lits lits
	
let literal_neg_selection_max unif_index cl_param clause = 
  let sel_lits = literal_neg_selection_max_cl unif_index clause in   
  res_assign_sel_lits cl_param sel_lits;
  sel_lits
*)

(*
(*------ neg_min -----------*)
(* can raise Not_found if there are no neg lits *)
let literal_neg_selection_min' unif_index lits = 
  let neg_lits = filter_neg_no_split lits in
  let min_unif_cands = filter_min_unif_cands unif_index neg_lits in  
  let neg_literal  = list_find_max_element (fun x y -> - (Term.cmp_num_symb x y)) min_unif_cands in
  [neg_literal]


let literal_neg_selection_min_cl unif_index cl = 
  let lits = (get_relevant_lits cl) in
  try
    literal_neg_selection_min' unif_index lits 
  with
    Not_found -> (* all lits are positive*)
      get_max_kbo_lits lits
   
let literal_neg_selection_min unif_index cl_param clause = 
  let sel_lits = literal_neg_selection_min_cl unif_index clause in
  res_assign_sel_lits cl_param sel_lits;
  sel_lits
*)

(*------ neg_nrc -----------*)
(* tries to find neg literal with no positive occurrence of its pred symb in the clause and different from Split *)
(* otherwise max neg; otherwise max kbo *)
(* can raise Not_found if there are no neg lits *)
let literal_neg_selection_nrc' unif_index lits = 
  let neg_lits = filter_neg_no_split lits in
  let nrc_filtered = 
    let pos_symbs = 
      let f acc_pos_symbs lit = 
        if (Term.is_pos_lit lit) 
        then 
          let top_symb = Term.get_top_symb lit in
          SSet.add top_symb acc_pos_symbs
        else
          acc_pos_symbs
      in
      List.fold_left f SSet.empty lits
    in
    let f acc_nrc lit = 
      let top_symb = Term.get_top_symb (Term.get_atom lit) in
      if (SSet.mem top_symb pos_symbs) || (Symbol.get_property top_symb = Symbol.Split)
      then
        acc_nrc
      else
        (lit::acc_nrc)
    in
    List.fold_left f [] neg_lits
  in
  let nrc_lits = 
    if not (nrc_filtered = [])
    then 
      nrc_filtered
    else
      (
(*       raise Not_found *)
        neg_lits 
      )
  in
  let min_unif_cands = filter_min_unif_cands unif_index nrc_lits in  
  let neg_literal  = list_find_max_element (fun x y -> (Term.cmp_num_symb x y)) min_unif_cands in
  [neg_literal]


let literal_neg_selection_nrc_cl unif_index cl = 
  let lits = (get_relevant_lits cl) in
  try
    literal_neg_selection_nrc' unif_index lits 
  with
    Not_found -> (* all lits are positive*)
      get_max_kbo_lits lits
   
let literal_neg_selection_nrc unif_index cl_param clause = 
  let sel_lits = literal_neg_selection_nrc_cl unif_index clause in
  res_assign_sel_lits cl_param sel_lits;
  sel_lits

(* changing selection !*)


(* next_neg_sel moving to the next negative selection   *)
(* chnages the selection and returns the new sel lit *)
(* can raise  No_next_neg *)
(* assume no duplicates of lits in the clause *)
exception No_next_neg
let next_neg_sel cl_param clause = 
  dbg D_adaptive (lazy ("next_neg_sel: clause: "^(Clause.to_string clause)));
  let lits = (get_relevant_lits clause) in
  try 
    let current_sel = 
      (match (res_get_sel_lits cl_param) 
      with h::tl -> h
      |_->  failwith "Selection: next_neg_sel selection is not neg")
    in
    dbg D_adaptive (lazy ("next_neg_sel: current sel: "^(Term.to_string current_sel)));
    let tail_lits = list_skip current_sel lits in
    try 
      let next_sel = List.find is_neg_no_split tail_lits in
      res_assign_sel_lits cl_param [next_sel]; 
      dbg D_adaptive (lazy ("next_neg_sel: next sel: "^(Term.to_string next_sel)));
      [next_sel]
    with 
      Not_found -> 
        (
         dbg D_adaptive (lazy ("next_neg_sel: No_next_neg"));
        raise No_next_neg
        )
  with 
    Res_sel_lits_undef ->   
      try 
	let next_sel = List.find is_neg_no_split lits in
	res_assign_sel_lits cl_param [next_sel]; 
        dbg D_adaptive (lazy ("next_neg_sel: first sel: "^(Term.to_string next_sel)));
	[next_sel]
      with 
	Not_found -> 
          (dbg D_adaptive (lazy ("next_neg_sel: No_next_neg"));
          raise No_next_neg
	  ) 

(* sel max kbo but if there is pol in max then selects any such lit *)
let sel_kbo_max' ~pol unif_index lits =
  let kbo_sel_lits = get_max_kbo_lits lits in 
  try  
    literal_pol_selection' ~pol ~max:true unif_index kbo_sel_lits (* get neg sel from kbo pre selected *)
  with
    Not_found ->
      kbo_sel_lits
        

let sel_kbo_max unif_index cl_param clause =
  let sel_lits = sel_kbo_max' ~pol:false unif_index (get_relevant_lits clause) in (* select single negative if exists *)
  res_assign_sel_lits cl_param sel_lits;
  sel_lits

(*------------------------------------------------*)
let res_change_sel_final unif_index cl_param clause =
  dbg D_adaptive (lazy ("-----final sel------"));
  dbg D_adaptive (lazy ("final sel: clause: "^(Clause.to_string clause)));
  if (not (res_get_sel_final cl_param)) 
  then 
    begin
      res_set_sel_final true cl_param;   
      let all_lits = get_relevant_lits clause in
      let neg_lits = List.find_all is_neg_no_split all_lits in     
      if ((List.length neg_lits) > 0)
      then
        let final_sel = (* neg_sel_cand *)
          match !current_options.res_lit_sel with 
          |Res_adaptive_neg ->
              let neg_sel_cand = literal_pol_selection' ~pol:false ~max:true unif_index neg_lits in      
              neg_sel_cand
          |Res_adaptive_max ->
              let kbo_max_sel_cand = sel_kbo_max' ~pol:false unif_index all_lits in
              kbo_max_sel_cand
          |_->  (* Res_adaptive *)
              begin
                let side_measure_opt = !current_options.res_lit_sel_side in        
                match side_measure_opt with 
                |CM_none ->  
                    let sel_lits = sel_kbo_max unif_index cl_param clause in
                    dbg D_adaptive (lazy ("final sel: CM_none: kbo_max: "^(Term.term_list_to_string sel_lits) ));
                    sel_lits
                | _ ->  
                    let cl_measure = Clause.cl_measure_to_fun side_measure_opt in  
                    let neg_sel_cand = literal_pol_selection' ~pol:false ~max:true unif_index neg_lits in      
                    let kbo_max_sel_cand = sel_kbo_max' ~pol:false unif_index all_lits in
                    
                    let sel_the_same = 
                      match (neg_sel_cand, kbo_max_sel_cand) with 
                      |([neg_sel_lit], [kbo_max_lit]) -> neg_sel_lit == kbo_max_lit
                      |_-> false 
                    in
                    if sel_the_same 
                    then 
                      (
                       dbg D_adaptive (lazy ("final sel: neg_sel_lit == kbo_max_lit : "
                                             ^(Term.term_list_to_string neg_sel_cand)));
                       neg_sel_cand
                      )
                    else
                      begin
(* choose between neg_sel_cand and kbo_max_sel_cand *)
                          
                        let measure_neg_sel_cand = 
                          ClauseUnifIndex.get_measure_unif_cand_lits unif_index cl_measure neg_sel_cand in
                        
                        let measure_kbo_max_sel_cand = 
                          ClauseUnifIndex.get_measure_unif_cand_lits unif_index cl_measure kbo_max_sel_cand in
                        
                        dbg D_adaptive (lazy ("final sel neg: "^(Term.term_list_to_string neg_sel_cand)
                                              ^" measure_cand: "^(string_of_int measure_neg_sel_cand)));
                          
                        dbg D_adaptive (lazy ("final sel kbo_max: "^(Term.term_list_to_string kbo_max_sel_cand)
                                              ^" measure_cand: "^(string_of_int measure_kbo_max_sel_cand)));
                        if (measure_neg_sel_cand <= measure_kbo_max_sel_cand)
                        then 
                          (
                           dbg D_adaptive (lazy ("final sel: choose: neg_sel_cand"));
                           neg_sel_cand
                          )
                        else
                          (
                           dbg D_adaptive (lazy ("final sel: choose: kbo_max_sel_cand "));
                           kbo_max_sel_cand 
                          )
                      end  
              end   (* end Res_adaptive *)     
        in        
        res_assign_sel_lits cl_param final_sel;
        final_sel
      else (* no neg_no_split lits *)
        (         
                  let sel_lits = sel_kbo_max unif_index cl_param clause in
                  dbg D_adaptive (lazy ("final sel: kbo_max: no neg: "^(Term.term_list_to_string sel_lits) ));
                  sel_lits
                 )
    end
  else
    (
     try 
       res_get_sel_lits cl_param 
     with 
       Res_sel_lits_undef -> 
	 failwith "selection: res_change_sel_final"
    )   
      

(*change_sel changes selection to new and returns new selected literals *)
(*if  selection is already max then raises Max_sel  *)
(*also works when no sel is assigned*)

(* exception Final_sel *)
	  
let res_change_sel unif_index cl_param clause = 
  if (res_get_sel_final cl_param) 
  then 
   (failwith "res_change_sel: sel_final: can not change") (* should not happen *)
  else
    try 
      next_neg_sel cl_param clause
    with 
      No_next_neg -> 
        res_change_sel_final unif_index cl_param clause


let res_lit_sel_type_to_fun unif_index res_lit_sel_type = 
  match res_lit_sel_type with 
  |Res_adaptive | Res_adaptive_neg | Res_adaptive_max -> res_change_sel unif_index
  |Res_KBO_max     -> sel_kbo_max unif_index
  |Res_neg_sel_max -> literal_pol_selection ~max:true ~pol:false unif_index
  |Res_neg_sel_min -> literal_pol_selection ~max:false ~pol:false unif_index
  |Res_pos_sel_max -> literal_pol_selection ~max:true ~pol:true unif_index
  |Res_pos_sel_min -> literal_pol_selection ~max:false ~pol:true unif_index
  |Res_neg_sel_nrc -> literal_neg_selection_nrc unif_index


(* todo rework without passing unif_index *)
let res_lit_sel unif_index cl_param clause = 
  let sel_fun = res_lit_sel_type_to_fun unif_index !current_options.res_lit_sel in
  let sel_lits = sel_fun cl_param clause in
  res_assign_sel_lits cl_param sel_lits;
  sel_lits
  
