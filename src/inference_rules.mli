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
open Instantiation_env
open Options
(*
val num_of_dismatch_blockings    :  int ref 
val num_of_non_proper_inst       :  int ref 
val num_of_duplicates            :  int ref
*)


(* assume literals are ordered as by default *)
val is_tautology : clause -> bool 
val is_eq_tautology : clause -> bool

(*-----------------------------------------------------------------*)
(*-- unflatting: x!=t\/ C[x,y] -> C[t,s] where x not in t ---------*)
(*-- 1) collect diequalities {x_i!=t_i}; unify {x_1 = t_1;..;x_n=t_n} and apply mgu to the remainder of the clause *)
(*--- if 1) fails due non-unification then collect disequality of vaiables and unify them and apply one substitution --*)
(*--- the ramaining disequalitites are applied one by one *)
(*-----------------------------------------------------------------*)

val unflatten_clause : clause -> clause
val unflatten : clause list -> clause list

val bmc1_merge_next_func : clause -> clause

(* strict_subset_subsume by_clause to_clause *)
(* we assume that to_subs_clause has defined length *)
(* and by_clause does not, but all lits a are in    *)

val strict_subset_subsume  : clause -> clause -> bool

(* resolution, factoring, instantiation_nrom can raise  Unif.Unification_failed *)
(* resolution can raise Main_subsumed_by*)

exception Main_subsumed_by of clause
val resolution    : clause -> literal ->
                      clause list -> literal -> clause list 



val resolution_dismatch   : bool -> bool -> bool -> (clause * inst_cp) -> literal ->
                      (clause * inst_cp) list -> literal -> clause list 


val subs_resolution    : clause -> literal ->
                      clause list -> literal -> clause list 

val factoring     : clause -> literal -> literal -> clause

(*
val instantiation : term_db ref -> clause -> literal -> literal ->
                      clause list -> literal -> clause list 
*)

val equality_resolution_simp: clause -> clause

val instantiation_norm : is_redundant_fun:(clause -> bool) -> (clause * inst_cp)  -> literal ->
  (clause * inst_cp) list -> literal -> clause list

(* val instantiation_norm : context -> (clause * inst_cp)  -> literal ->
  bool -> (clause * inst_cp) list -> literal -> clause list 
*)


(*------------- domain instantiation used in QBF/ also try finite domains ------------*)

(*
type dom_inst_param = 
    Dom_inst_single | 
    Dom_inst_chain
 *)

type inst_domain_result = 
  | Main_dom_inst of clause list (* main is redunandant in the presence of these clauses *)
  | Side_dom_inst of clause list (* side is redunandant in the presence of these clauses *)

(* let instantiation_domain_single : type_to_domain (c1,c1_param) l1 c_c_param_list2 l2 = *)
val instantiation_domain_single: 
    qbf_dom_inst_type -> (* defined in options.mli *)
    SystemDBs.type_to_domain -> 
      (clause * inst_cp)  -> literal ->
        (clause * inst_cp) list -> literal -> inst_domain_result


(* for element of domain pre-instantiates clause all variables mapped to this element *)
(* used in QBF *)
val dom_pre_inst: SystemDBs.type_to_domain -> clause -> clause list
