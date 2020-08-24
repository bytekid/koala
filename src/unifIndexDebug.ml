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

(*----------------------------------------------------*)
(* debug implementation of unification index *)
(*----------------------------------------------------*)

(* type of the index *)
type 'a t = {
  mutable trie_index : 'a UnifIndexDiscrTree.t;
  mutable map_index : 'a UnifIndexMap.t;
}

(* create unification index: i/r *)
let create () =
{
  trie_index = UnifIndexDiscrTree.create ();
  map_index = UnifIndexMap.create ();
}

(* clear unification index: i/r, like create *)
let clear ui =
  UnifIndexDiscrTree.clear ui.trie_index;
  UnifIndexMap.clear ui.map_index

(* add elem with given selected literal: i/r *)
let add_elem_to_lit ui lit elem =
  UnifIndexDiscrTree.add_elem_to_lit ui.trie_index lit elem;
  UnifIndexMap.add_elem_to_lit ui.map_index lit elem

(* remove elem with given selected literal: i/r *)
let elim_elem_from_lit ui lit elem =
  UnifIndexDiscrTree.elim_elem_from_lit ui.trie_index lit elem;
  UnifIndexMap.elim_elem_from_lit ui.map_index lit elem

(* eliminates all clauses indexed by lit from unif_index and returns *)
(* the eliminated clause list: i *)

let eliminate_lit ui lit =
  let ret_trie = UnifIndexDiscrTree.eliminate_lit ui.trie_index lit in
(*  let ret_map = UnifIndexMap.eliminate_lit ui.map_index lit in *)

  (* TODO: compare result *)
  ret_trie

(* compare the 2 unif_cand list elements *)
let uc_compare uc1 uc2 =
  let (lit1, cl1) = uc1 in
  let (lit2, cl2) = uc2 in
  (* FIXME!! Term.compare doesn't work here *)
  Term.compare lit1 lit2

module UCKey =
  struct
    type t = term * clause list
    let compare = uc_compare
  end

module UCSet = Set.Make(UCKey)

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
  let folder acc (l,cl) =
    if unifyable l
    then (l,(List.sort Clause.compare cl))::acc
    else acc
  in
  let folder' acc (l,cl) =
    (l,(List.sort Clause.compare cl))::acc
  in
  (* trie candidates *)
  let trie_ret = UnifIndexDiscrTree.get_unif_candidates ui.trie_index lit in
  (* map candidates *)
  let map_ret = UnifIndexMap.get_unif_candidates ui.map_index lit in
  (* keep only unifiable candidates from trie *)
  (* map is fine as we did this inside *)
  let trie_unif = List.sort uc_compare (List.fold_left folder [] trie_ret) in
  let map_unif = List.sort uc_compare (List.fold_left folder' [] map_ret) in
  (* fold all lists to a set *)
  (* let fold_to_set set (l,cl) = UCSet.add (l,cl) set in               *)
  (* let trie_set = List.fold_left fold_to_set UCSet.empty trie_unif in *)
  (* let map_set = List.fold_left fold_to_set UCSet.empty map_unif in   *)
  (* compare 2 UC elements *)
  let equal_uc uc1 uc2 =
    let (lit1, cl1) = uc1 in
    let (lit2, cl2) = uc2 in
    (*compare literals 1st *)
    if not(lit1 == lit2)
    then  (* not equal -- shouldn't happen *)
      false
    else
      try
        ignore(list_find_not_equal Clause.compare cl1 cl2);
        false
      with Not_found ->
        true
  in
  (* compare 2 UC lists *)
  let cmp_2l_f accum uc1 uc2 = accum && (equal_uc uc1 uc2) in
  let equal_lists =
    try
      List.fold_left2 cmp_2l_f true trie_unif map_unif
    with Invalid_argument _->
      false
    in
  (* if UCSet.equal trie_set map_set *)
  if equal_lists
  then (* OK -- return one of the answers *)
    map_ret
  else
    failwith "get_unif_candidates: DiscrTree and Map results differ"

(* check whether given literal is in the unif index *)
let in_unif_index ui lit =
  let ret_trie = UnifIndexDiscrTree.in_unif_index ui.trie_index lit in
  let ret_map = UnifIndexMap.in_unif_index ui.map_index lit in
  if ret_trie != ret_map
  then failwith "in_unif_index: DiscrTree and Map results differ"
  else ret_trie
