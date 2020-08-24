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

type sym_set = Symbol.sym_set

type csig = Clause.clause_signature

(*
val axiom_list : unit -> clause list
*)

val eq_axiom_list : clause list -> clause list

(* typed_congr_axiom_list :  eq_type_set -> sym_set -> cong_axioms*)

val typed_eq_axioms_sig : csig -> clause list

(* val typed_congr_axiom_list : csig -> clause list *)

val flat_clause_list : clause list -> clause list

val eq_axioms_flatting  : clause list -> clause list

val pure_dis_eq_elim : clause list -> clause list 

val distinct_ax_list : unit -> clause list

val less_axioms : unit -> clause list

val range_axioms : unit -> clause list

val less_range_axioms : unit -> clause list

(* typed_symmetry_axiom_sym eq_type_sym *)
val typed_symmetry_axiom_sym : symbol -> clause

val bit_index_symb : int -> symbol 
val bit_index_term : int -> term

val get_bv_axioms : unit -> clause list
