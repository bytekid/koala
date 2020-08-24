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


type aig_and = {
  lhs : int;
  mutable rhs0 : int;
  mutable rhs1 : int;
  mutable in_use : bool;
  mutable simplified : bool;
}
val and_as_string : aig_and -> string
type aig_symbol = {
  mutable lit : int;
  mutable next : int;
  reset : int;
  size : int;
  lits : int list;
  name : string;
  mutable used : bool;
  mutable removed : bool
}
val latch_as_string : aig_symbol -> string
type aig_symbol_list = aig_symbol list
type aiger = {
  max_var : int;
  inputs : aig_symbol_list;
  latches : aig_symbol_list;
  outputs : aig_symbol_list;
  bad : aig_symbol_list;
  constraints : aig_symbol_list;
  justice : aig_symbol_list;
  fairness : aig_symbol_list;
  ands : aig_and list;
  comments : string list;
}
val aiger_stat : aiger -> string
val aig_pref : string
val lit2var : int -> int
val neg : int -> int
