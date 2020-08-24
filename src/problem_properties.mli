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

type prob_props =
    {
     mutable clauses : int;
     mutable conjectures : int;
     mutable epr : int;
     mutable horn : int;
     mutable unary : int;
     mutable binary : int;
     mutable lits : int;
     mutable lits_eq : int;
   }


(* val input_problem_props : problem_props ref *)


val get_prob_props : clause list -> prob_props

val prob_props_to_statistics : prob_props -> unit 

val prob_props_to_string : prob_props -> string

(*--------- derived properties -------*)

val is_epr        : prob_props -> bool
val is_horn       : prob_props -> bool 
val has_eq        : prob_props -> bool 
val is_unary      : prob_props -> bool 
val is_binary     : prob_props -> bool 
val is_unit_eq    : prob_props -> bool 

(*--------- clauses list properties computed directly -------*)
val has_equality : clause list -> bool

val change_prolific_symb_input : clause list -> unit
