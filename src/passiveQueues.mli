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
exception Passive_Empty

type passive_queue

val create_passive_queue :
  Options.passive_queue_type ->
  Options.cl_cmp_type list list -> int list -> passive_queue

val add_to_passive : passive_queue -> clause -> unit

val add_list_to_passive : passive_queue -> clause list -> unit

val remove_from_passive : passive_queue -> clause

(*  return first clause on which f is true (which is also removed from the queue) *)
val remove_from_passive_until : passive_queue -> (clause -> bool) -> clause

val num_elem : passive_queue -> int

val finalise : passive_queue -> unit
