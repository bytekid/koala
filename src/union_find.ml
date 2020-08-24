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






module type Elem = 
  sig
    type t 
    val equal : t -> t -> bool
    val hash : t -> int
  end

module type UF = 
  sig 
    type e
    type t

(* expected size *)
    val create : int -> t
    val add : t -> e -> unit
    val find : t -> e -> e 
    val union : t -> e -> e -> unit
    val iter : (e -> e -> unit) -> t -> unit
    val length : t -> int
  end 

(*module Make: 
  functor (Elem : Elem) -> UF with type e = Elem.t
 *)

module Make(E : Elem) =
  struct
    type e  = E.t
    module EHash = Hashtbl.Make(E)
    type v = 
	{
(*parent can be itself (the key in EHash) *)
	 mutable parent : e;
	 mutable rank   : int;	 
       }

    type t = (v) EHash.t
    let create = EHash.create
    let add t e = 
      try 
	ignore (EHash.find t e)
      with 
	Not_found -> 
	  (
	   EHash.add t e {parent = e; rank = 0}
	  )

(* can raise Not_found *)
    let rec find_v t e =      
      let v = EHash.find t e in
      if (v.parent == e) 
      then v
      else 
	(
	 let new_v = find_v t v.parent in
	 v.parent <- new_v.parent; (* path compression*)
	 new_v
	)

    let find t e = (find_v t e).parent

    let rec union t e1 e2 =
      add t e1;
      add t e2;
      let v1 = find_v t e1 in
      let v2 = find_v t e2 in
      if v1 == v2 
      then ()
      else
	(
	 if v1.rank > v2.rank then 
	   v2.parent <- v1.parent 
	 else 
	   if v2.rank > v1.rank then
	     v1.parent <- v2.parent  
	   else 
	     if (v2.rank = v1.rank) 
	     then
	       (
		v2.parent <- v1.parent;
		v1.rank <- v1.rank+1
	       )
	     else ()
	)

    let iter f t = 
      let f' e _ =  
	let v = find t e in
	(f e v)
      in
      EHash.iter f' t

    let length = EHash.length
  end
