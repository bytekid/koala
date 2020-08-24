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





exception Satisfiable 
exception Unsatisfiable 

module type PropStruct = 
  sig
    type var
    type lit 
    type clause = lit list 
    val pos_lit : lit -> bool
    val get_var : lit -> var
    val compare_var : var -> var -> int
    val var_to_string : var -> string
  end

module type DPLL = 
  sig
    type clause 
    type state
    val create_init_state : unit -> state
    val dpll : state -> clause list -> unit
  end

module Make (PS:PropStruct) : (DPLL with  type clause = PS.clause)
