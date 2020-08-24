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




open Prop_var



(*----- clauses ----*)

type clause
type parents = 
    P_Input
  | P_BRes of lit * clause * clause 
  | P_URes of clause  (* implying clause *)
  | P_HRes of clause list (* hyper resolution *) 
  | Q_Res of clause (* q-res in qbf *)

val clause_create : lit list -> parents -> clause        
val clause_get_lits : clause -> lit list
val in_clause : lit -> clause -> bool
val get_parents : clause -> parents
val is_unit_clause : clause -> bool
val is_empty_clause : clause -> bool

val clause_to_string : clause -> string
val clause_list_to_string : clause list -> string
val out_clause_list : clause list -> unit
val dimacs_stdin : unit -> clause list
val clause_cmp_length : clause -> clause -> int 

(* used for parsing vars and lits *)
val var_str_list_to_var_list_0 : string list -> var list
val lit_str_list_to_lit_list_0 : string list -> lit list

module CKey :
  sig
    type t = clause
    val compare : t -> t -> int
  end

module CMap : Map.S with type key = clause
module CSet : Set.S with type elt = clause



(*---------- model --------------*)

type model
type var_impl_type = 
    Decided 
  | Implied of clause (* implied by clause and previous assignments *)

type var_model_val = 
    {
     var : var;
     var_val : bool;
     var_impl_type : var_impl_type;
     var_dlevel : int; (* not used in func impl. *)
   }	  

val var_model_val_to_string : var_model_val -> string

type model_res = 
  |M_False of var_model_val 
  |M_True of var_model_val
  |M_Undef 
      
val create_model : unit -> model
val in_model : model ->  var -> bool
val find_model : model -> var -> var_model_val
val check_model : model -> lit -> model_res
val add_to_model : model -> var -> var_model_val -> model
val remove_model : model -> var -> model 
val is_true_model : model -> lit -> bool
val out_model : model -> unit 

(*----------------------------*)	
exception Satisfiable of model
exception Unsatisfiable of clause
(*----------------------------*)	

(*--- watch ----*)
type watch_el = { wt_pos : CSet.t; wt_neg : CSet.t; }
val get_watch_size : bool -> watch_el -> int

(*-------------*)
val get_implying : clause -> clause
val unit_resolve_model : var_model_val -> clause -> clause

(* resolve lit main_clause side_clause *)
val resolve : lit -> clause -> clause -> clause 

(* binary resolves clause impl literal in the model and c *)
val resolve_model : var_model_val -> clause -> clause

val hyper_resolve_until_decided : model -> clause -> clause

val is_tautology : clause -> bool 

(*----var pripority queue -----*)

type var_priority_queue

val create_var_priority_queue  : unit -> var_priority_queue 

val mem_pq : var_priority_queue -> Prop_var.VMap.key -> bool

val remove_var_pq : var_priority_queue -> var -> var_priority_queue

(* remove_max_pq_var returns (max_priority_var, rest_queue) *)
(* raises Not_found if the queue is empty *)

(* returns (var, priority, pr_queue) *)
val remove_max_var_pq : var_priority_queue -> var * int * var_priority_queue

(* add_var_pq priority var pr_queu *)
val add_var_pq : int -> var -> var_priority_queue -> var_priority_queue

(*--------var score map --------*)

type var_score_map

val create_var_score_map : unit -> var_score_map

val get_var_score : var -> var_score_map -> int

val incr_var_score : var -> int -> var_score_map -> var_score_map

(* update_var_score f var var_score_map *)
val update_var_score : (int -> int) -> var -> var_score_map ->  var_score_map

val unpdate_all_vars_score : (int -> int) -> var_score_map ->  var_score_map
