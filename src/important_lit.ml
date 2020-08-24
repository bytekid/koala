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


(* implementation of a set of important literals *)

module SSet = Symbol.Set

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_add_lit
  | D_fold_important_lits

let dbg_gr_to_str = function 
  | D_add_lit -> "add_lit"
  | D_fold_important_lits -> "fold_important_lits"

let dbg_groups =
  [
  D_add_lit;
  D_fold_important_lits
 ]
    
let module_name = "important_lit"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(* type for set of symbols *)


(* set of important literals *)
let important_lit_set = ref SSet.empty

(* check whether the set is empty *)
let is_empty () = SSet.is_empty !important_lit_set

(* add a symbol to an important lits set *)
let add_lit symb =
  dbg D_add_lit (lazy (Symbol.to_string symb));
  important_lit_set := SSet.add symb !important_lit_set

(* check whether a symbol is important *)
let is_important symb =
  SSet.mem symb !important_lit_set

(* fold all important literals *)
let fold_important_lits folder =
  SSet.fold folder !important_lit_set
