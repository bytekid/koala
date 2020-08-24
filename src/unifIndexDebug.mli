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

type 'a t

val create : unit -> 'a t
val clear : 'a t -> unit

val add_elem_to_lit : 'a t -> lit -> 'a -> unit
val elim_elem_from_lit : 'a t -> lit -> 'a -> unit
val eliminate_lit : 'a t -> lit -> 'a list
val get_unif_candidates : clause t -> lit -> (lit * clause list) list
val in_unif_index : 'a t -> lit -> bool
