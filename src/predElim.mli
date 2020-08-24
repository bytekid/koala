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

type pe_options = 
    {
     pe_has_eq : bool; 
     
(* pe_has_eq can be true even if input does not contain equality explicitly, since it can be added by later operations *)
     
     mutable pe_estim_num_of_lits : int; 
     (* do not eliminate symbol if the number of potential resulting clauses is greater than pe_elim_num_of_cl_bound *)
     
(* not active *)
   mutable pe_conclusion_limit_test : clause -> bool; 
     (* do not eliminate symbol if (pe_conclusion_limit_test concl) is false *)
  
    mutable pe_preprocess_conclusion_extern : clause -> clause; (* preprocess conclusion, used in qbf *)

     
     pe_keep_elim : elim_symb: symbol -> clauses_before_elim: clause list -> clauses_after_elim: clause list -> bool;

(*num_lit_before:int -> num_lit_after:int -> num_cl_before:int -> num_cl_after:int -> bool; *)
(* if  pe_keep_elim is true we keep elimination of the predicated otherwise abort it *)
(* based on the number of clauses before elimination and after elimination *)

       pe_elim_order_cmp_fun : context -> (symbol -> symbol -> int); 	 
       (* compare function on symbols; elimination from smaller to larger, currently static *)

(*       input_protected : SSet.t;     *)

	 pe_elimination_set : Symbol.Set.t ; 
(*  predicates for elimination *)

         pe_time_limit : float; (* time limit if <=0. then unlimited *)

(*------- simplifications ---------*)

(* in backward simplifications  *)
(* Options.res_subs_type: type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int *)
(* length bound is of the given clause *)
	 
	 prop_glb_subs : bool;

	 subs_cl_to_cl_limit : int;

(* local *) 
         lcl_add_to_sub_index_test : clause -> bool;	 
	 lcl_fwd_subs : bool;
	 lcl_fwd_subs_res : bool;
	 
	 lcl_bwd_subs : Options.res_subs_type; 
	 lcl_bwd_subs_res : Options.res_subs_type; 
	 
(* global *)
	 glb_add_to_sub_index_test : clause -> bool;	 
	 glb_fwd_subs : bool;
	 glb_fwd_subs_res : bool;
	 
	 glb_bwd_subs : Options.res_subs_type; 
	 glb_bwd_subs_res : Options.res_subs_type; 

   }



(* input is Cl_Context(clause_context) | Cl_List (clause_list) *)

val predicate_elimination : pe_options ->  context_list -> clause list


(* resturns set of pred from the input for elimination             *)
(* and auxilary the number of pred occurences map *)
(* includes most predicates from the input but not special_symbols *)
(* one can remove extra symbols from the resulting set             *)
(* can be used to fill  pe_elimination_set in pe_options           *)
val get_most_preds_to_eliminate :  context_list -> (Symbol.Set.t * (int Symbol.Map.t))


val get_pred_depth : symbol -> int
