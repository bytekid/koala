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





type var = Var.var 
type term = Term.term
type clause = Clause.clause

(*instead of renaming we use binding to distinguish 
  from which term the variables came 
  note that renaming destroys sharing*)

type bound_var   = Var.bound_var
type bound_term  = Term.bound_term
type bound_subst = SubstBound.bound_subst 
type subst = Subst.subst

(* bounds can be different on the different sides of the bound_equation *)
type bound_equation = bound_term * bound_term

exception Orient_equal
exception Orient_func_terms
exception Unification_failed 
exception Matching_failed
exception Subsumtion_failed
exception Unif_type_check_failed

val unify_bterms : bound_term -> bound_term -> bound_subst

(* unifies a list of equations ex. [((1,t_1),(2,s_1)); ((2,t_2),(2,s_2))] *)
val unify_beq_list :  bound_equation list -> bound_subst

(* check t matching s  with substit. extending subst returns extened subst*)

val matches_subst : term -> term -> subst -> subst 
val matches       : term -> term -> subst 

val subsumes      : clause -> clause -> subst
