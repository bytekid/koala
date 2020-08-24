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

(*
  type clause  = Clause.clause
  type literal = Clause.literal
 *)


(* restricted subset subsumption very fast but 
   very incomplete :  
   literals in clauses assumed to be ordered by e.g. fast term comparison
   then we check whether given clause extents a clause in the index 
   and then this clause is subsumed
   or this clause is extended by a clause in the index and then the clause 
   in the index is subsumed 
 *)

exception Is_subsumed 
exception Subsumes
exception Already_in 
exception No_subsumed

(*
  module type SubsetSubsume = 
  sig
  type index
  
  val create : unit -> index
  
(* we assume that the literals in the clause are in term db*)
  val add_clause  : clause -> index -> index

(* returns list of  all strictly subsumed clauses by the clause 
   raises No_subsumed if no such clauses*)

  val find_subsumed : clause -> index -> clause list 
  
(* removes a subtrie corr. to all subsumed by the cluase clauses 
   after this the cluase is not in the index 
   for efficience can be joint with find_subsumed  
   (remove clauses from  separately)*)
  
  val  remove_subsumed : clause -> index -> index 
  

(*Restricted Subset subsumed*)
(*    val is_rsubset_subsumed : index -> clause -> bool
      
(* the list of clauses (rsubset)subsumed by the given clause*)
      val subsumed_clauses : index -> clause -> clause list
      

      (*   val remove : clause -> index ref -> unit	 *)
 *)
  end
 *)
(*
  module SubsetSubsume = 
  struct
 *)


  
module SIndexM = Trie_func.Make(Term.Key)

type core_index = clause SIndexM.trie
      
type index = 
    {
    mutable ind : core_index;
    mutable ind_clauses : CSet.t;
   }

let create () = 
  {
   ind = SIndexM.create ();
   ind_clauses = CSet.empty;
 }


let in_ss_index index clause =  
  CSet.mem clause index.ind_clauses

(* is_subsumed' returns the clause which subset subsumes lit_list *)
(* otherwise raises Not_found*)
(*  check also subclauses on subset subs*)
let rec is_subsumed' index lit_list =
  try (SIndexM.long_or_in lit_list index.ind) 
  with
    Not_found -> 
      (match lit_list with 
      |l::tl ->  
	  is_subsumed' index tl
      |[] -> raise Not_found
      )  

(* is_subsumed returns the clause which subset subsumes clause *)
(* otherwise raises Not_found*)

let is_subsumed index clause = 
  let lit_list = Clause.get_literals clause in
  is_subsumed' index lit_list
    
    
let add_clause index clause = 
  if (CSet.mem clause index.ind_clauses) 
  then 
    ()
  else
    begin
      try
        index.ind <- SIndexM.add (Clause.get_literals clause) clause index.ind;
        index.ind_clauses <- CSet.add clause index.ind_clauses;
    (* Clause.set_bool_param true Clause.in_subset_subsumption_index clause; *)
(*    Clause.set_ps_in_subset_subsumption_index true clause; *)
      with
      |Trie_func.Trie_add_leaf_extension -> raise Is_subsumed 
      |Trie_func.Trie_add_short_kyelist  -> raise Subsumes
      |Trie_func.Trie_add_already_in     -> raise Already_in 
    end
      
let find_subsumed index clause = 
  try
    SIndexM.all_elem_short (Clause.get_literals clause) index.ind
  with 
    Not_found -> raise No_subsumed

let cset_remove_list cset clist = 
  let f rest c = 
    CSet.remove c rest 
  in 
  List.fold_left f cset clist


let remove_subsumed index clause = 
  try
   (
    let all_subsumed = find_subsumed index clause in
    index.ind <- SIndexM.remove_short (Clause.get_literals clause) index.ind;
    index.ind_clauses <- cset_remove_list index.ind_clauses all_subsumed
   )
  with
    Not_found -> raise No_subsumed

let find_and_remove_subsumed index clause = 
  try
    (
     let all_subsumed = find_subsumed index clause in
     index.ind <- SIndexM.remove_short (Clause.get_literals clause) index.ind;
     index.ind_clauses <-  cset_remove_list index.ind_clauses all_subsumed;
     all_subsumed
    )
  with
    Not_found -> raise No_subsumed


let remove index clause = 
  if (in_ss_index index clause) 
  then 
    (
     index.ind <- SIndexM.remove (Clause.get_literals clause) index.ind;
     index.ind_clauses <- CSet.remove clause index.ind_clauses
    )
  else
    raise Not_found 


(*
  end
 *)
