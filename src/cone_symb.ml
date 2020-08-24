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


open Logic_interface
open Lib

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  |D_add_clause

let dbg_gr_to_str = function 
  |D_add_clause -> "add_clause"
	
let dbg_groups =
  [
   D_add_clause;
 ]
    
let module_name = "cone_symb"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)


type full_rel = 
    {
     mutable symb_to_clauses : CSet.t SMap.t;
     mutable succ_rel : SSet.t SMap.t;     
   }

type cone = 
    {
     mutable cone_symb_depth_map : int SMap.t;
     
     mutable cone_full_rel : full_rel; 
     mutable cone_max_depth : int;
     mutable cone_id : int;
   (*  mutable cone_clauses : CSet.t;  *)
   }

let create_full_rel () = 
  {
   symb_to_clauses = SMap.empty;
   succ_rel = SMap.empty;
 }


let cone_id_counter = ref 0 

let get_symb_to_clauses full_rel = full_rel.symb_to_clauses

let get_cone_id cone = cone.cone_id
    
(*---------------------------------*)
let add_clause 
     full_rel ?(tolerance=0.) ?(symb_num_of_occ_map=SMap.empty)  ~is_relevant_symb ?(pred_symb_only=true) clause =
  
  dbg D_add_clause (lazy (Clause.to_string clause));
  let cl_all_relevant_symb_set = 
    if pred_symb_only 
    then 
      Clause.find_all_pred ~is_relevant_pred:(fun _sign symb -> is_relevant_symb symb) clause 
    else
      Clause.find_all_sym ~is_relevant_symb clause
  in

  let trigger_symb_set = 
    if (tolerance > 0.)
    then
      begin
	let min_num_of_occ = 
	  let f symb curr_min = 
	    try 
	    let symb_num_occ = SMap.find symb symb_num_of_occ_map in 
	    if symb_num_occ < curr_min 
	    then
	      symb_num_occ
	    else
	      curr_min
	    with 
	      Not_found -> curr_min
	  in
	  SSet.fold f cl_all_relevant_symb_set max_int
	in
	dbg D_add_clause (lazy ("min_num_occ: "
				       ^(string_of_int  min_num_of_occ)));
	if (min_num_of_occ = max_int)
	then 
	  cl_all_relevant_symb_set
	else
	  begin
	    let acceptable_num_occ = (int_of_float ((float_of_int min_num_of_occ) *. tolerance)) in
	    dbg D_add_clause (lazy ("accept_num_occ: "
				    ^(string_of_int acceptable_num_occ)));
	    let filtered_in_symbs = 
	      SSet.filter
		(fun symb -> 
		  try      
		    let symb_num_occ = SMap.find symb symb_num_of_occ_map in 
		    dbg D_add_clause (lazy ((Symbol.to_string symb)^" num_occ: "
					    ^(string_of_int symb_num_occ)));
		    symb_num_occ <= acceptable_num_occ
		  with 
		  Not_found -> 
		    dbg D_add_clause (lazy ((Symbol.to_string symb)^"symb not in the  symb_num_of_occ_map"));
		    true
		)
		cl_all_relevant_symb_set
	    in
	    dbg_env D_add_clause 
	      (fun () -> 
	      if ((SSet.cardinal cl_all_relevant_symb_set) != (SSet.cardinal filtered_in_symbs))
	      then
		(
		 dbg D_add_clause (lazy ("filtered_in_symbs: "
					 ^(list_to_string Symbol.to_string (SSet.elements filtered_in_symbs) ",")));
		)
	      );
	    filtered_in_symbs
	  end
      end
    else 
      cl_all_relevant_symb_set  
  in
  let add_symb_to_clauses symb = 
    let cl_set = 
      try 
	SMap.find symb full_rel.symb_to_clauses 
      with 
	Not_found -> CSet.empty
    in
    full_rel.symb_to_clauses <- SMap.add symb (CSet.add clause cl_set) full_rel.symb_to_clauses
  in 
  SSet.iter add_symb_to_clauses trigger_symb_set;

(* keep symbol in its successors for better sharing *)
  let add_succ symb_set = 
    let f symb = 
      let succ_set = 
	try 
	  SMap.find symb full_rel.succ_rel 
	with 
	  Not_found -> SSet.empty
      in
      full_rel.succ_rel <-
	SMap.add symb (SSet.union (* symb_set *) cl_all_relevant_symb_set succ_set) full_rel.succ_rel     	  
    in
    SSet.iter f symb_set
  in
  add_succ trigger_symb_set

(*---------------------------------*)
let create_full_rel_cl_list ?(tolerance=0.) ?(symb_num_of_occ_map=SMap.empty) ~is_relevant_symb ?(pred_symb_only=true) clause_list = 
  let full_rel = create_full_rel () in 
  List.iter 
    (fun cl -> add_clause full_rel ~tolerance ~symb_num_of_occ_map ~is_relevant_symb ~pred_symb_only cl) clause_list;
  full_rel

(*---------------------------------*)
module SymbReach = MakeReach (Symbol) (SMap) (SSet)

let compute_cone full_rel ?(terminating_symb_set=SSet.empty) ~depth_0_symb_set = 
  let succ_rel symb = 
    if (SSet.mem symb terminating_symb_set) 
    then 
      SSet.empty
    else
      try 
	let succ_symbs = (SMap.find symb full_rel.succ_rel) in 
(*
	if (SSet.exists (fun succ_symb -> SSet.mem succ_symb terminating_symb_set) succ_symbs) 
	then 
	  SSet.empty
	else
*) 
	 succ_symbs 
      with 
	Not_found ->  SSet.empty
  in
  let reach_map = SymbReach.compute_reachability_set ~succ_rel depth_0_symb_set in
  
   (* returns max depth of symbols in the cone *)    
  let cone_max_depth =
    let f symb s_depth curr_max =
      if (s_depth > curr_max)
      then
	s_depth
      else
	curr_max
    in
    SMap.fold f reach_map 0
  in
  let cone = 
    {
     cone_symb_depth_map = reach_map;
     cone_full_rel = full_rel;
     cone_max_depth = cone_max_depth;
     cone_id = !cone_id_counter;
   }
  in
  cone_id_counter := !cone_id_counter + 1;
  cone

(*--------*)
let get_cone_symb_depth_map cone =  cone.cone_symb_depth_map
let get_cone_max_depth cone = cone.cone_max_depth

(*--------*)
(* if ~depth:-1 returns all reachable clauses *)
let get_cone_clauses cone ~depth =    
  let reduced_depth_map = 
    if (depth > -1) 
    then
      SMap.filter (fun symb s_depth -> s_depth <= depth) cone.cone_symb_depth_map
    else       
      cone.cone_symb_depth_map
  in
  let f symb _d rest_cl = 
    try 
     let symb_cl = SMap.find symb cone.cone_full_rel.symb_to_clauses in
     (CSet.union symb_cl rest_cl)
    with
      Not_found -> rest_cl
  in
  let cone_clauses = SMap.fold f reduced_depth_map CSet.empty in
  cone_clauses 



(*-------*)
let out_cone ~symbs ~clauses ~stats cone =

  (* get into list and order by priority *)
  let symb_depth_list =
    SMap.fold (fun symb depth rest -> ((symb, depth):: rest)) cone.cone_symb_depth_map []
  in
  let sorted_symb_depth_list =
    List.sort (fun (_, d1) (_, d2) -> compare d1 d2) symb_depth_list in
  
  (if stats 
  then 
    out_str ("cone symbols: "^(string_of_int (List.length sorted_symb_depth_list))^"\n\n")
  );
  (if symbs
  then
    List.iter
      (fun (symb, depth) ->
	out_str ((Symbol.to_string symb)^": "^(string_of_int depth)))
      sorted_symb_depth_list;
  );

  let cone_clauses = get_cone_clauses cone ~depth:(-1) in
  (if stats 
  then 
  out_str ("cone clauses: "^(string_of_int (CSet.cardinal cone_clauses))^"\n\n");
  );

  (if clauses
  then
    out_str (Clause.clause_list_to_string (CSet.elements cone_clauses));
  )


  
(*    
(*---------------------------------*)
let compute_cone full_rel ?(reach_bound=0) ?(terminating_symb_set=SSet.empty) ~depth_0_symb_set = 
  let succ_rel symb = 
    if (SSet.mem symb terminating_symb_set) 
    then 
      SSet.empty
    else
      try 
	let succ_symbs = (SMap.find symb full_rel.succ_rel) in 
(*
	if (SSet.exists (fun succ_symb -> SSet.mem succ_symb terminating_symb_set) succ_symbs) 
	then 
	  SSet.empty
	else
*) 
	 succ_symbs 
      with 
	Not_found ->  SSet.empty
  in
  let reach_map = SymbReach.compute_reachability_set succ_rel depth_0_symb_set in
  let reduced_reach_map = 
    if reach_bound > 0 
    then
      SMap.filter (fun symb depth -> depth <= reach_bound) reach_map
    else       
      reach_map
  in
  let f symb _d rest_cl = 
    try 
     let symb_cl = SMap.find symb full_rel.symb_to_clauses in
     (CSet.union symb_cl rest_cl)
    with
      Not_found -> rest_cl
  in
  let cone_clauses = SMap.fold f reduced_reach_map CSet.empty in

  let cone = 
    {
     cone_symb_depth_map = reduced_reach_map;
     cone_clauses = cone_clauses
   }
  in
  cone




let out_cone ~symbs ~clauses ~stats cone =

  (* get into list and order by priority *)
  let symb_depth_list =
    SMap.fold (fun symb depth rest -> ((symb, depth):: rest)) cone.cone_symb_depth_map []
  in
  let sorted_symb_depth_list =
    List.sort (fun (_, d1) (_, d2) -> compare d1 d2) symb_depth_list in
  
  (if stats 
  then 
    out_str ("cone symbols: "^(string_of_int (List.length sorted_symb_depth_list))^"\n\n")
  );
  (if symbs
  then
    List.iter
      (fun (symb, depth) ->
	out_str ((Symbol.to_string symb)^": "^(string_of_int depth)))
      sorted_symb_depth_list;
  );

  (if stats 
  then 
  out_str ("cone clauses: "^(string_of_int (CSet.cardinal cone.cone_clauses))^"\n\n");
  );

  (if clauses
  then
    out_str (Clause.clause_list_to_string (CSet.elements cone.cone_clauses));
  )



*)
 (*   let symb_list = SSet.elements symb_set in 
    let add_edge s list =
      let succ_set = 
	try 
	  SMap.find s full_rel_symb.edges 
	with 
	  Not_found -> []
      in
      full_rel_symb.edges <- SMap.add s (list@succ_list) full_rel_symb.edges     	  
    in

    let rec f rest list  = 
      match list with 
      | h::tl -> 
	add_edge h rest;
	add_edge h tl;  
	  f (h::rest) tl
    in
    f [] symb_list 
  in
  
*)



  
