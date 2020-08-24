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


open AigCommon
open Lib
open Logic_interface

val input_vars_list_ref : symbol list ref
val aig_is_input_var : symbol -> bool
val aig_is_input_pred : term -> bool

val aig_is_latch_var : symbol -> bool
val aig_is_latch_pred : term -> bool

val clausify_aig : aiger -> unit
val get_property_cone : unit -> clause list
val get_latch_cone : term -> clause list
val get_cone : TSet.t -> int -> clause list

val get_remainder : TSet.t -> SSet.t
