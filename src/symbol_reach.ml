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


(*-------- Reachability depth for father_of relation (Intel) -----------*)
          

module SymbReach = MakeReach (Symbol) (SMap) (SSet)

(*----------------*)
let succ_rel symb =
  let succ_symb_names =
    try
      SMap.find symb !(Parser_types.father_of_map)
    with
      Not_found -> []
  in
  let succ_symb_set =
    let f rest symb_name =
      try
	let symb = SymbolDB.find
	    (Symbol.create_template_key_symb symb_name) !symbol_db_ref in
	(SSet.add symb rest)
      with
	Not_found ->
	  rest
    in
    List.fold_left f SSet.empty succ_symb_names 
  in
  succ_symb_set
    

(*----------------*)
let symbol_reach conj_list =
  let get_preds_clause clause =
    Clause.fold_pred (fun sset _sign symb -> SSet.add symb sset) SSet.empty clause
  in

  let conj_pred_set = 
    List.fold_left (fun rest clause -> (SSet.union (get_preds_clause clause) rest)) SSet.empty conj_list
  in

  let reach_map = SymbReach.compute_reachability_set ~succ_rel conj_pred_set in
  SMap.iter
    (fun symb depth ->
      Symbol.assign_defined_depth depth symb) reach_map;
  reach_map


(*----------------*)
let out_symb_reach_map srm =
  (* get into list and order by priority *)
  let symb_depth_list =
    SMap.fold (fun symb depth rest -> ((symb, depth):: rest)) srm []
  in
  let sorted_symb_depth_list =
    List.sort (fun (_, d1) (_, d2) -> compare d1 d2) symb_depth_list in
  
  (* Output only in verbose mode *)
  if val_of_override !current_options.bmc1_verbose then
    List.iter
      (fun (symb, depth) ->
	out_str ((Symbol.to_string symb)^": "^(string_of_int depth)))
      sorted_symb_depth_list
