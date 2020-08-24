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

(*-------------------------------------------------------------*)
(* Type to represent unsat core. Contains list of literals and *)
(* list of clauses. *)
(*-----------------------------------------------------------*)

type unsat_core =
  {
    uc_assumptions: lit list;
    uc_clauses: clause list;
  }

let create assumptions clauses =
  {
    uc_assumptions = assumptions;
    uc_clauses = clauses;
  }

let get_assumptions unsat_core = unsat_core.uc_assumptions
let get_clauses unsat_core = unsat_core.uc_clauses

let print unsat_core =
  let assumptions = get_assumptions unsat_core in
  let clauses = get_clauses unsat_core in
  let n_a = string_of_int (List.length assumptions) in
  let n_c = string_of_int (List.length clauses) in

  out_str ("unsat core: "^n_a^" assumptions, "^n_c^" clauses");
  out_str "assumptions:";
  out_str (Term.term_list_to_string assumptions);
  out_str "clauses:";
  out_str (Clause.clause_list_to_string clauses)
