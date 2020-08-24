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

(*----------- initial state: setup code (AIG) ---------------*)

val set_state_size : int -> unit
val set_latch_value : int -> int -> unit
val set_latch_index : int -> symbol -> unit

(*----------- initial state: usage code (BMC1) --------------*)

val add_latch_value : symbol -> char -> unit
val print_initial_state : unit -> unit

(*----------- input vector: setup code (AIG) ----------------*)

val set_input_size : int -> unit
val set_input_value : int -> int -> unit
val set_input_index : int -> symbol -> unit

(*----------- input vector: usage code (BMC1) ---------------*)

val set_input_max_bound : int -> unit
val add_input_value : int -> symbol -> char -> unit
val print_input_vectors : unit -> unit
