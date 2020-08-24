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


(* unification index for inst/res: map implementation (use for DEBUG) *)

open Lib
open Options
open Statistics
open Logic_interface


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

let dbg_groups =
  [
   D_trace;
 ]

let module_name = "unifIndexMap"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(*-----------------------------------*)


(* sort the unification candidate list *)
let sort_unif_candidates uc_list =
  (* compare the 2 unif_cand list elements *)
  let uc_compare uc1 uc2 =
    let (lit1, cl1) = uc1 in
    let (lit2, cl2) = uc2 in
    Term.compare lit1 lit2
  in
  (* sort the list using the above method *)
  
  let sorted_list = (List.sort uc_compare uc_list) in

  dbg_env D_trace
    (fun () -> 
      (
       let pair_to_string (lit,_) = Term.to_string lit in
	out_str (list_to_string pair_to_string sorted_list ",");
      )
    );

  sorted_list
  


(* type to map terms into lists of general elements *)
type 'a map_term_to_list = 'a list TMap.t

(*---------------------------------*)
(* operations with term->list maps *)
(*---------------------------------*)

(* add ELEM to the TERM binding of the MAP *)
let add_elem_to_term_list_map term elem map =
  try
    (* get the old list corresponding to TERM *)
    let old = TMap.find term map in
    (* put a new element to that list *)
    TMap.add term (elem::old) map
  with Not_found ->
    (* no such binding -- create a new one *)
    TMap.add term [elem] map

(* remove ELEM from the TERM binding of the MAP *)
let remove_elem_from_term_list_map term elem map =
  try
    (* get the old list corresponding to TERM *)
    let old = TMap.find term map in
    (* remove all instances of ELEM from the list *)
    let rest = List.filter (fun el -> not(elem == el)) old in
    (* check the result *)
    match rest with
    | [] ->
      (* last entity removed -- remove binding *)
      TMap.remove term map
    | _ ->
      (* something left -- save it back *)
      TMap.add term rest map
  with Not_found ->
    (* binding doesn't exists -- nothing to do *)
    map


(*----------------------------------------------------*)
(* term->list map implementation of unification index *)
(*----------------------------------------------------*)

(* type of the index *)
type 'a t = {
  mutable unif_index : 'a map_term_to_list;
}

(* create unification index: i/r *)
let create () =
{
  unif_index = TMap.empty;
}

(* clear unification index: i/r, like create *)
let clear ui =
  ui.unif_index <- TMap.empty

(* add elem with given selected literal: i/r *)
let add_elem_to_lit ui lit elem =
  ui.unif_index <- add_elem_to_term_list_map lit elem ui.unif_index

(* remove elem with given selected literal: i/r *)
let elim_elem_from_lit ui lit elem =
  ui.unif_index <- remove_elem_from_term_list_map lit elem ui.unif_index

(* eliminates all clauses indexed by lit from unif_index and returns *)
(* the eliminated clause list: i *)

let eliminate_lit ui lit =
  (* check whether lit' = lit modulo var *)
  (* if so, add elem to accum and remove binding *)
  let choose_lit_modulo_var lit' elem accum =
    if not((Term.compare_key_modulo_var lit lit') = cequal)
    then (* do nothing *)
      accum
    else (
      (* remove binding *)
      ui.unif_index <- TMap.remove lit' ui.unif_index;
      elem @ accum
    )
  in
  TMap.fold choose_lit_modulo_var ui.unif_index []

(* get unification candidates for given literal, i/r *)
let get_unif_candidates ui lit =
  (* returns true if l1 us unifiable with lit *)
  let unifyable l1 =
    try
      ignore(Unif.unify_bterms (1,l1) (2,lit));
      true
    with Unif.Unification_failed ->
      false
  in
  (* folder for the map: adds (l,[c1,...,cn]) to acc *)
  (* if l is unifyable with lit *)
  let folder l cl acc =
    if unifyable l
    then (l,cl)::acc
    else acc
  in
  (* get all pairs for which l is unifyable with lit *)
  let unsorted = TMap.fold folder ui.unif_index [] in
  (* return sorted result *)
  sort_unif_candidates unsorted

(* check whether given literal is in the unif index *)
let in_unif_index ui lit = TMap.mem lit ui.unif_index
