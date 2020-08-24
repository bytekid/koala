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

module MakePQ (El:Ordered) (Pr:Ordered) : PQSig with type el = El.t and type pr= Pr.t

module MakePQInt (El:Ordered) : PQSig with type el = El.t and type pr = int
