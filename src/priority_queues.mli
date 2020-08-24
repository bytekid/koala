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






(* A bare element module with only the type and no operations, those
   are given in a separate module at runtime *)
module type Elem0 =
sig 
  type t 
  val compare : t -> t -> int (* basic compare of id's of elements; used to track which elements are added *)
end


(* An element in a priority queue *)
module type ElemN = 
sig

  (* The type of an element in the queue *)
  type t

  (* A comparison function between two elements for each queue *)
  val compare : t -> t -> int

  (* The multiplier for each queue *)
  val mult : int
    
end

module QueueN(E : Elem0) : sig

  (* The type of an n-ary priority queue *)
  type t

  (* The type of the elements *)
  type elt = E.t

  (* All queues are empty 

     We should to call [clean] after the queues are empty. *)
  exception Empty 

  (* Create n priority queues containing elements of the same type but
     with different orderings *)
(*
  val create   : int -> (module ElemN with type t = elt) list ->
    (elt -> bool) -> (bool -> elt -> unit) -> t
*)

  val create   : int -> (module ElemN with type t = elt) list -> t

  (* The number of elements in the queues *)
  val num_elem : t -> int

  (* Add an element to all queues *)
  val add_all : t -> elt -> unit

  (* Are all queues empty? *)
  val is_empty : t -> bool

  val in_queue : t -> elt -> bool

(* if we find that passive queue is empty then we need to clean it: *)
(* (done by PassiveQueue.clean) *)
(* 1. assign in_queue param to false in all clauses in the remaining queue*)
(* 2. release memory and assign new queues *)

  (* Clean queues, that is, recreate the data structures *)
  val clean    : int -> t -> unit
    
  (* Removes the maximal element from some queue *)
  val remove   : t -> elt
    
end
