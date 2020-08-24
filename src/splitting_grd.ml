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
open Logic_interface
open Definitions 

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

	
let dbg_groups =
  [
   D_trace
 ]
    
let module_name = "splitting_grd"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)



type split_result =
    {
     split_list : clause list;
     num_of_splits : int;
     num_of_split_atoms : int;
   }

let get_split_list result = result.split_list
let get_num_of_splits result = result.num_of_splits
let get_num_of_split_atoms result = result.num_of_split_atoms

let empty_result () =
  { split_list = [];
    num_of_splits = 0;
    num_of_split_atoms = 0 }

module LitListKey =
  struct
    type t = lit list
    let compare l1 l2 = list_compare_lex Term.compare l1 l2
  end

module SplitMap = Map.Make(LitListKey)

type split_map = (lit * lit * clause) SplitMap.t
let create_split_map () = SplitMap.empty

let split_map_ref = ref (create_split_map ())

let reset_splitting () = ()
(*	split_map_ref := create_split_map ()*)


type lit_ext =
    { elit : lit;
      evar_set : VSet.t }

type part_entry =
    { mutable lit_list : lit list;
      mutable var_set : VSet.t;
    }

(*we assume no ground in unprocessed *)
type partition =
    {
     mutable current : part_entry param;
     mutable unprocessed : lit_ext list;
     mutable processed : (lit list) list
   }

exception All_var_tried
let rec get_next_var_to_check var_tried_set_ref var_set =
  let diff = VSet.diff var_set !var_tried_set_ref in 
  try 
    let v = VSet.choose diff in 
    var_tried_set_ref := VSet.add v !var_tried_set_ref;
    v
  with 
    Not_found -> raise All_var_tried
(*
  match var_list with
  | v:: tl ->
      if (VSet.mem v !var_tried_set_ref)
      then get_next_var_to_check var_tried_set_ref tl
      else
	(var_tried_set_ref:=VSet.add v !var_tried_set_ref;
	 v)
  | [] -> raise All_var_tried
*)
(* returns (lits,vars,new_unprocessed) where var occurs in lits *)
(* and does not occur in new_unprocessed *)

let get_all_lits_vars var unprocessed =
  let f rest lit_ext =
    let (rest_lits, rest_vars, new_unprocessed) = rest in
    if (VSet.mem var lit_ext.evar_set)
    then
      (lit_ext.elit:: rest_lits,
       (VSet.union lit_ext.evar_set rest_vars),
       new_unprocessed)
    else (rest_lits, rest_vars, lit_ext::new_unprocessed)
  in
  List.fold_left f ([],VSet.empty,[]) unprocessed

let rec partition_lit_list var_tried_set partition =
  match partition.current with
  | Def(part_entry) ->
      (try
	(let var = get_next_var_to_check var_tried_set part_entry.var_set in
	let (all_lits, all_vars, new_unprocessed)
	    = get_all_lits_vars var partition.unprocessed in
	partition.current <-
	  Def({ lit_list = (List.rev_append all_lits part_entry.lit_list);
		var_set = (VSet.union all_vars part_entry.var_set) });
	partition.unprocessed <- new_unprocessed;
	partition_lit_list var_tried_set partition)
      with
	All_var_tried ->
	  ( partition.processed <- (part_entry.lit_list):: (partition.processed);
	    partition.current <- Undef;
	    partition_lit_list var_tried_set partition)
      )
  | Undef ->
      match partition.unprocessed with
      |[] -> partition.processed
      | lit_ext:: tl ->
	  (partition.unprocessed <- tl;
	   partition.current <-
	     Def(
	     { lit_list = [lit_ext.elit];
	       var_set = lit_ext.evar_set
	     });
	   partition_lit_list var_tried_set partition)

(* was *)
(* C_1\/p_1;..C_n\/p_n; ~p_1\/..\/~p_n\/ground_lits *)

(* now *)
(* C_1\/~p_1;..C_n\/~p_n; p_1\/..\/p_n\/ground_lits *)

let ground_split_clause def_env clause =
  let var_tried_set = ref VSet.empty in
  let all_lits = Clause.get_literals clause in
  let (ground_lits, non_ground_lits) = List.partition Term.is_ground all_lits in
  let unprocessed =
    let f lit = { elit = lit;
		  evar_set = VSet.of_list (Term.get_vars lit)
		    (* fst (List.split (Term.get_var_ass_list lit))*) } in
    List.map f non_ground_lits in
  let init_partition =
    {
     current = Undef;
     unprocessed = unprocessed;
     processed = [];
   } in
  let split_ground_lits = ref ground_lits in
  let split_clauses = ref [] in
  let num_of_split_atoms = ref 0 in
  
  (* Record symbols introduced for splitting *)
  (* let split_symbols = ref [] in*)

(* TOD change *)
  let intersection_test elits  = 
    match elits with 
    |h::tl -> 
        let f inter_set elit =       
          VSet.inter inter_set elit.evar_set in
        let inter_var_set = List.fold_left f h.evar_set tl in 
        not (VSet.is_empty inter_var_set) 
    |[]-> false
  in     
  let processed =
    if (intersection_test init_partition.unprocessed) 
    then 
      [non_ground_lits]
    else
      partition_lit_list var_tried_set init_partition 
  in
  if
    (
     (not (processed = []) &&
      (not ((List.tl processed) = []))) ||
      ( not (processed = []) && not (ground_lits = []) &&
	(not ((List.tl ground_lits) = [])))
)
  then
    let create_split_clause_split_atom lit_list =
      let (split_atom, split_clause) = 
        add_def def_env ~parent:clause [(* no vars*)] lit_list in

      split_ground_lits:= split_atom:: (!split_ground_lits);
      split_clauses := split_clause::(!split_clauses) 
(*
      let norm_list = Clause.normalise_lit_list term_db_ref lit_list in
      (try
	(let (split_atom, _split_neg_atom, split_clause) = SplitMap.find norm_list !split_map_ref in
	(* split_clauses:= (Clause.create (split_atom::norm_list))::(!split_clauses);*)
	(* split_ground_lits:=split_neg_atom::(!split_ground_lits))*)
	split_ground_lits:= split_atom:: (!split_ground_lits);
(*	split_clauses := (Clause.copy_clause split_clause)::(!split_clauses) *)
	split_clauses := split_clause::(!split_clauses) 
	)
      with
	Not_found ->
	  (
	   let new_split_symb =
	     SymbolDB.create_new_split_symb
	       symbol_db_ref
	       (Symbol.create_stype [] Symbol.symb_bool_type)
	   in
	   
	   num_of_split_atoms := !num_of_split_atoms +1;
	   split_symbols := new_split_symb :: !split_symbols;
	   
               
	   let split_atom = add_fun_term new_split_symb [] in
	   let split_neg_atom = add_neg_atom split_atom in
	   
	   let tstp_source = Clause.tstp_source_split [split_atom] [clause] in
	   
	   let split_clause = create_clause tstp_source (split_neg_atom:: norm_list) in
	   (* assign when born in the corresponding search loop *)
(*	   Clause.set_ps_simplifying true split_clause; *)
           Clause.inherit_conjecture clause split_clause; 	   

	   split_map_ref :=
	     SplitMap.add norm_list (split_atom, split_neg_atom, split_clause) !split_map_ref;
	   
	   (* split_clauses:= (Clause.create (split_atom:: norm_list)):: (!split_clauses);
	      split_ground_lits:= split_neg_atom:: (!split_ground_lits)
	    *)
	   
	   split_clauses:= split_clause:: (!split_clauses);
	   split_ground_lits:= split_atom:: (!split_ground_lits)
	  )
      )
*)
    in
    List.iter create_split_clause_split_atom processed;

    let ground_clause = create_def_reduced_clause ~parent:clause !split_ground_lits in
(*
    let tstp_source_ground_clause = Clause.tstp_source_split (!split_ground_lits) [clause] in
    let ground_clause = create_clause tstp_source_ground_clause !split_ground_lits in
(*    Clause.set_ps_simplifying true ground_clause; *)
    Clause.inherit_conjecture clause ground_clause; 	
*)
    (* Clause.inherit_param_modif clause ground_clause; *)
    (* Clause.assign_split_history ground_clause clause; *)
    let split_final_list = ground_clause:: (!split_clauses) in

    let result ={
      split_list = split_final_list;
      num_of_splits = (List.length !split_clauses);
      num_of_split_atoms = !num_of_split_atoms;
    }
    in
(*    Clause.assign_replaced_by (Def(Clause.RB_splitting result.split_list)) clause; *)
(*    List.iter (Clause.inherit_conjecture clause) result.split_list; *)
(* debug *)
    
    dbg D_trace (lazy ("clause before split:\n"^(Clause.to_string clause)^"\n"));
    dbg D_trace (lazy ("clauses after split:\n"
                       ^(Clause.clause_list_to_string result.split_list)^"\n"));
    
(*
  out_str ("Clause to Split:\n"^(Clause.to_string clause)^"\n");
  out_str ("Clauses After Split: \n"
  ^(Clause.clause_list_to_string result.split_list)^"\n");		
 *)			
(* debug *)		

    result
  else
    let result ={
      split_list = [clause];
      num_of_splits = 0;
      num_of_split_atoms = 0;
    } in
    result

let ground_split_clause_list def_env clause_list =
  let init_result = empty_result () in
  let f rest clause =
    
    let clause_split_result =
      ground_split_clause def_env clause in
    (*		
      let unchanged =
      (match (clause_split_result.split_list)
      with
      | [cl] -> (cl == clause)
      | _ -> false
      )
      in
     *)		
    let result =
      { split_list = List.rev_append clause_split_result.split_list rest.split_list;
	num_of_splits = clause_split_result.num_of_splits + rest.num_of_splits;
	num_of_split_atoms =
	clause_split_result.num_of_split_atoms + rest.num_of_split_atoms;
      } in result
  in
  List.fold_left f init_result clause_list
