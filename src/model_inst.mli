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
open Logic_interface
open Instantiation_env

type model 

(* clause list are added to all_clauses *)
(* normaly clauses list are clauses filtered out by prep_sem_filter_unif *)
val build_model : inst_pre_model:inst_pre_model -> inst_pre_model_filtered_out:inst_pre_model -> model

(*
val model_to_stream : 'a string_stream -> model -> unit
*)
    
val out_model : model -> unit

type aig_model 

(* normally is_relevant_pred is true on preds corresponding to aig input vars *)

val get_aig_model : is_relevant_pred:(symbol->bool) -> model  -> aig_model

(* let get_aig_val = aig_model bound symb -> '0', '1', 'x' --- false/true/don't care (not in the aig_model) *)
val get_aig_val : aig_model -> int -> symbol -> char
