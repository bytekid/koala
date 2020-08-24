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





(** Get parent clauses which are input clauses *)
val get_leaves : Clause.clause list -> Clause.clause list 

(** Get parent clauses; don't go into parents of those defined by ignore_parents predicate *)
val get_parents_filter : (Clause.clause -> bool) -> Clause.clause list -> Clause.clause list

(** Get parent clauses *)
val get_parents : Clause.clause list -> Clause.clause list

(** Output a clause and its source with justification for global subsumption *)
val pp_clause_with_source_gs : ?clausify_proof:bool -> Format.formatter -> Clause.clause -> unit

(** Output a clause and its source *)
val pp_clauses_with_clausification : Format.formatter -> Clause.clause list -> unit

(** Output a proof of the empty clause in TSTP format *)
val pp_tstp_proof_resolution : Format.formatter -> Clause.clause -> unit

(** Output a proof of an ground unsatisfiable core in TSTP format *)
val pp_tstp_proof_unsat_core : Format.formatter -> Clause.clause list -> unit
