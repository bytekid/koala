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
open Definitions 

type split_map

val reset_splitting: unit -> unit

val create_split_map : unit -> split_map


type split_result 
   
val get_split_list         : split_result -> clause list
val get_num_of_splits      : split_result -> int
val get_num_of_split_atoms : split_result -> int


val ground_split_clause : def_env -> clause -> split_result 

val ground_split_clause_list : def_env -> clause list -> split_result 
