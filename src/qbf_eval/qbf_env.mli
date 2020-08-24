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



(* open Prop_var *)

open Lib
module PV    = Prop_var
module PVSet = Prop_var.VSet
module PVMap = Prop_var.VMap
module PE    = Prop_env
open Prop_var

type pclause = PE.clause


type quant = A | E | D


type quant_block =
    {
     qb_quant  : quant;
     mutable qb_vars   : PVSet.t;
     qb_level  : int; 
     (* for now level and id are the same; lineary ordered from left to right *)
     (* later level can be changed to non-linear tree like dependences *)     
   }


type quant_pref = quant_block IntMap.t

type qbf_cnf =
    {
     mutable qbf_pref : quant_pref; 
     mutable qbf_clauses : pclause list;
     mutable qbf_var_level : (int * quant) PVMap.t; (* maps vars to level *)
     mutable qbf_vars : PVSet.t;     
     (*  (qdimacs allows to have "free vars" which are implicitly outer-existentialy quantified) *)
     (* after parsing we create an existential qb of level 0 for such vars *)

(* TODO: currently inner dep only makes sense without dvars similar with preprocessing; 
         extend inner dep and prep with dvars *)
     mutable qbf_dvar_map : VSet.t VMap.t; (* map for dependency d vars -> a vars on which d depends *)

   }



type qbf_var_dep = PVSet.t PVMap.t (* maps existential  variables to sets of variables on which they depend *)

val qbf_get_var_qlevel : qbf_cnf -> var -> (int * quant)
val qbf_get_var_level  : qbf_cnf -> var -> int

val qbf_var_in_qbf : qbf_cnf -> var -> bool
val qbf_is_e_var : qbf_cnf -> var -> bool
val qbf_is_d_var : qbf_cnf -> var -> bool
val qbf_is_d_or_e_var : qbf_cnf -> var -> bool
val qbf_is_a_var : qbf_cnf -> var -> bool

val qbf_get_max_lvl_qb : qbf_cnf -> (int * quant_block)

(* can raise Unsatisfiable/ Eliminated (in the case of tautology) *)
val q_resolve_clause :  qbf_cnf -> PE.clause -> PE.clause
val qbf_q_resolve : qbf_cnf -> unit

(*  qbf_split_clauses sp_part_size qbf *)
val qbf_split_clauses : int -> qbf_cnf -> unit

val qbf_outer_var_dep  : qbf_cnf -> qbf_var_dep

(* assume no dvars *)
val qbf_inner_var_dep  : qbf_cnf -> qbf_var_dep
 
val qbf_parse_in_channel : string -> in_channel -> qbf_cnf
val qbf_parse_stdin : unit -> qbf_cnf

val qbf_cnf_test_parser : unit -> unit 

val get_var_dep : qbf_var_dep -> var -> PVSet.t

val out_var_dep : qbf_var_dep -> unit

val out_qbf : qbf_cnf -> unit 
