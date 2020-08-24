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

(* full_rel contains full symbol graph based on clauses *)

type full_rel

type cone

      (*
type cone = 
    {
     mutable cone_symb_depth_map : int SMap.t;
     mutable cone_clauses : CSet.t;
   }
*)
val create_full_rel : unit -> full_rel

val add_clause : full_rel -> ?tolerance:float -> ?symb_num_of_occ_map:(int SMap.t) -> is_relevant_symb:(symbol ->bool) -> ?pred_symb_only:bool -> clause -> unit

(* pred_symb_only:true then assume that only predicate symbols can be relevant *)

val create_full_rel_cl_list : ?tolerance:float -> ?symb_num_of_occ_map:(int SMap.t) -> is_relevant_symb:(symbol ->bool) -> ?pred_symb_only:bool -> clause list -> full_rel

(* cone is computedget_cone_max_depth starting from depth_0_symb_set; 
  successors of symbols from  terminating_symb_set are ignored;
  terminating_symbol_set: ignore successors of symbols from this set *)

val compute_cone : full_rel -> ?terminating_symb_set:SSet.t -> depth_0_symb_set:SSet.t -> cone

val get_cone_max_depth : cone -> int

(* if ~depth:-1 returns all reachable clauses *)
val get_cone_clauses: cone -> depth:int -> CSet.t   

val get_cone_symb_depth_map: cone -> int SMap.t 
    
val out_cone : symbs:bool -> clauses:bool -> stats:bool -> cone -> unit

val get_symb_to_clauses : full_rel ->  CSet.t SMap.t

val get_cone_id : cone -> int
