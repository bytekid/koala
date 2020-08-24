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

type t 

val create : unit -> t

val clear : t -> unit

val add_clause_with_sel :
  t -> term -> clause -> unit

val elim_clause_with_sel :
  t -> term -> clause -> unit

val eliminate_lit : t -> term -> clause list

val get_unif_candidates :
  t -> term -> (lit * clause list) list

val in_unif_index : t -> term -> bool

(* filters lits with minimal combined cl_measure of unif candidates in the index *)
(* cl_measure : cl -> int *)
val filter_lits_min_unif_cand : t -> (clause -> int) -> term list -> term list

val get_measure_unif_cand_lits : t -> (clause -> int) -> term list -> int
