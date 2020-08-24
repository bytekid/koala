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


(* restricted subset subsumption very fast but 
   very incomplete :  
   literals in clauses assumed to be ordered by e.g. fast term comparison
   then we check whether given clause (or its subclause)
   extents a clause in the index 
   and then this clause is subsumed
   or this clause is extended by a clause in the index and then the clause 
   in the index is subsumed 
*)


exception Is_subsumed 
exception Subsumes
exception Already_in 
exception No_subsumed

type index
      
val create : unit -> index

val in_ss_index : index -> clause -> bool

(* we assume that the literals in the clause are in term db*)   
val add_clause  : index -> clause -> unit

(* is_subsumed returns the clause which subset subsumes clause *)
(* otherwise raises Not_found*)
val is_subsumed : index -> clause -> clause

(* returns list of  all strictly subsumed clauses by the clause 
   raises No_subsumed if no such clauses*)

val find_subsumed : index -> clause -> clause list 
    
(* removes a subtrie corr. to all subsumed by the clause clauses *)
(* after this the clause is not in the index *)
(* can raise No_subsumed if no subsumed clauses *)
val  remove_subsumed : index -> clause -> unit

(* combination of find_subsumed and remove_subsumed *)
(* can raise No_subsumed *)
val find_and_remove_subsumed : index -> clause -> clause list

(* removes clause from ss index *)
(* raises Not_found if the clause is not in the index *)
val  remove : index -> clause -> unit

       

(* add later!
(*Restricted Subset subsumed*)
   val is_rsubset_subsumed : index -> clause -> bool
   	
(* the list of clauses (rsubset)subsumed by the given clause*)
   val subsumed_clauses : index -> clause -> clause list
	

 (*   val remove : clause -> index ref -> unit	*)
*)
 
