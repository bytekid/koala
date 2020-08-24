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





(*DEBUG is On can be slow !!!*)

open Lib
(* index is based on feature index of S. Schulz  *)


type clause  = Clause.clause
type literal = Clause.literal


(* let pre_cond_true_fun ~cl_in ~cl_by = true *)
(* pre_cond_true_fun is the default fun for forward subsumtion *)
val pre_cond_true_fun : cl_in:clause -> cl_by:clause -> bool

module type Index = 
  sig
   
  
    type feature

    type index

    val create : unit -> index

  (* we assume that feature list is of the same length for 
     every clause, and if C subsumes D then feature list of  D)
     is greater or equal than feature list of  C*)


 (* we assume that the the clause is in clause db*)
    val add_clause  : index -> (* feature list ->*) clause -> unit

(* check if the clause is subsumed and 
   returns  Some ((d,unif)) if it is and None otherwise*)
	
    val is_subsumed : 
        ?pre_cond:(cl_in:clause ->cl_by:clause -> bool) ->
	index -> (* feature list ->*) clause -> (clause*Subst.subst) option
	
(* returns list of  all  subsumed clauses by the clause
   and removes them from the index
   [] if no such clauses*)

    val find_subsumed :  index -> (* feature list ->*) clause -> clause list


(* the same as find_subsumed but also gives subsitution: (subsumed, subst) list*)
    val find_subsumed_subst :   
	index -> (* feature list -> *) clause -> (clause*Subst.subst) list

    val remove_clause : index -> (* feature list -> *) clause -> unit 	
(*    val  remove_subsumed : clause -> index -> index *)
    
    val in_subs_index : index ->  clause -> bool

 end

module type Feature =
  sig
    type t
    val compare : t -> t -> int
    val get_feature_list : clause -> t list 
  end

module type FeatureCom =
  sig
    type t
(* compare position  *)
    val compare_p : t -> t -> int
(* compare the value *)
    val compare_v : t -> t -> int
(*for debug*)
    val to_string : t -> string
    val get_feature_list : clause -> t list 

  end

module Make(Feature:Feature): (Index with type feature=Feature.t)

module MakeCom(FeatureCom:FeatureCom): (Index with type feature=FeatureCom.t)

(* concrete implementation of a subsumtion index with fixed compressed features as defined above *)
module SCFVIndex :
  sig
    include Index
    (* val get_feature_list : clause -> feature list *)
end
