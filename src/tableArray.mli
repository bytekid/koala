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





(* table impl. on array *) 
(*is automatically extended when the *)

type key

type 'a table

(* creates a new table with the initial size *)
val create : int -> 'a -> 'a table 

(* assigns value to the key which should be in the admissible range *)
val assign : 'a table -> key -> 'a -> unit

val get    : 'a table -> key -> 'a

val num_of_elem : 'a table -> int

(* gets next admisible key;*)
(* extends the table if nessecary (by doubling the size) *)
val get_next_key : 'a table -> key 

val iter : ('a -> unit) -> 'a table -> unit

val fold_left : ('a -> 'b -> 'a) -> 'a -> 'b table -> 'a


(*returns int >= 0 *)
val key_to_int : key -> int
