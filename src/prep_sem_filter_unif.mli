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


open Instantiation_env
open Logic_interface


type filtered_clauses =
    {

     filtered_in  : clause list;

(* filtered out clauses represented as pre_model; used in the final model representation *)
     filtered_out_inst_pre_model : inst_pre_model;
   }


(* sem_filter_unif clause_list side_clause_list *)
(* side clauses are theory clauses: they are used to block removing needed     *)
(* clauses from the clause set but are not added to the resulting filtered set *)


val sem_filter_unif : clause list -> side_clauses:clause list -> side_atoms:term list -> filtered_clauses


(*
(* filtered_clauses  are used for output only *)
type filtered_clauses =
    {

      filtered_in  : clause list;
(* filtered out clauses are used in model representation *)
(* for convenience  clauses get assigned inst_sel_lit which *)
(* are the literals true in the model *)
      filtered_out : clause list 
   }
*)
