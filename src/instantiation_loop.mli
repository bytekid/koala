(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2016 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         *)
(*----------------------------------------------------------------------[C]-*)



open Lib
open Logic_interface
open Instantiation_env


exception Inst_satisfiable of inst_pre_model

type inst_state 
    
val inst_create_state : unit -> inst_state 

val inst_lazy_loop_body  : inst_state -> unit 
    
val inst_add_clause : inst_state -> clause -> unit 
val inst_add_clause_list : inst_state -> clause list -> unit 
    
val inst_get_all_input_clauses : inst_state -> BCSet.t
    
