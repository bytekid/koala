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


(* a simple priority queue based on OCaml map         *)
(* basic operations a log time                        *) 
(* provides both min and max                          *)
(* different elements can have the same priority      *)
(* elements occur only once                           *)

open Lib

(*
module type Ordered = 
  sig
    type t 
    val compare : t -> t -> int
  end
*)

module type PQSig = 
  sig
    type t
    type el 
    type pr
          
    val create : unit -> t
    val is_empty : t -> bool
    val size : t -> int 
    val mem : t -> el -> bool
    val add : t -> el -> pr -> unit
    val get_pr : t -> el -> pr
    val remove : t -> el -> unit
    val update_pr : t -> el -> pr -> unit
    val max_el : t -> pr * el
    val min_el : t -> pr * el
    val max_el_rm : t -> pr * el
    val min_el_rm : t -> pr * el
  end



module MakePQ (El:Ordered) (Pr:Ordered) = 
  struct
    type el  = El.t 
    type pr  = Pr.t

    module PMap = Map.Make(Pr)
    module ESet = Set.Make(El)
    module EMap = Map.Make(El)
        
    type t = (* pq *)
        {
         mutable pq_pr_to_el : ESet.t PMap.t;
         mutable pq_el_to_pr : pr EMap.t;          
         mutable pq_size : int;
       }
       
(*    type t = pq *)

    let create () =
      {
       pq_pr_to_el = PMap.empty;
       pq_el_to_pr = EMap.empty;
       pq_size = 0;
     }

    let is_empty pq = 
      pq.pq_size = 0

    let size pq = pq.pq_size
    
    let mem pq el = EMap.mem el pq.pq_el_to_pr

(* the pred should not be in the eq *)
    let add pq el pr  = 
      assert((not (mem pq el)));
    
      let el_set = 
        try 
          PMap.find pr pq.pq_pr_to_el
        with 
          Not_found -> ESet.empty
      in
      let new_set = ESet.add el el_set in
      pq.pq_pr_to_el <- PMap.add pr new_set pq.pq_pr_to_el;
      pq.pq_el_to_pr <- EMap.add el pr pq.pq_el_to_pr;
      pq.pq_size <- pq.pq_size + 1          

(* can raise Not_found *)
    let get_pr pq el = 
      EMap.find el pq.pq_el_to_pr

    let remove pq el = 
      try
        let pr = EMap.find el pq.pq_el_to_pr in          
        let el_set = PMap.find pr pq.pq_pr_to_el in
        let new_set = ESet.remove el el_set in 
        (if (ESet.is_empty new_set) 
        then 
          (pq.pq_pr_to_el <- PMap.remove pr pq.pq_pr_to_el;)
        else
          (pq.pq_pr_to_el <- PMap.add pr new_set pq.pq_pr_to_el;)
        ); 
        pq.pq_el_to_pr <- EMap.remove el pq.pq_el_to_pr;
        pq.pq_size <- pq.pq_size - 1
      with (* not in pq *)
        Not_found -> ()

    let update_pr pq el pr = 
      remove pq el;
      add pq el pr

    let max_el pq = 
      let (max_pr, el_set) = PMap.max_binding  pq.pq_pr_to_el in 
      (max_pr, ESet.choose el_set)

    let min_el pq = 
      let (max_pr, el_set) = PMap.min_binding  pq.pq_pr_to_el in 
      (max_pr, ESet.choose el_set)

       (* also removes *)
        
    let max_el_rm pq = 
      let (max_pr, el) = max_el pq in
      remove pq el; 
      (max_pr, el)

    let min_el_rm pq = 
      let (min_pr, el) = min_el pq in
      remove pq el; 
      (min_pr, el)

  end
  

      
(* module MakePQInt (El:Ordered) = MakePQ (El, Lib.IntKey) *)


module MakePQInt (El:Ordered) = MakePQ (El) (IntKey) 
