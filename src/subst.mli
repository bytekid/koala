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




module SubstKey : Map.OrderedType with type t = Var.var

module SubstM : sig include Map.S with type key = SubstKey.t end

open Lib

type subst = Term.term SubstM.t
type term  = Term.term
type var   = Var.var
module VMap = Var.VMap

(*-------- flat_subst are used in model_inst and some constraints ------------*) 

(*-------- flat_subst are used in model_inst and some constraints ------------*) 

type flat_subst = (var*term) list

val compare_flat_subst : flat_subst -> flat_subst -> int

val flat_subst_to_string : flat_subst -> string

val subst_to_flat_subst : subst -> flat_subst

module FSKey :
  sig
    type t = flat_subst
    val compare : t -> t -> int
  end 

module FSMap : Map.S with type key = flat_subst
module FSSet : Set.S with type elt = flat_subst


(*----------- normal subst -----------------------*)
exception Subst_var_already_def

val create : unit -> subst
val is_empty : subst -> bool
val mem    : var -> subst -> bool 
val add    : var -> term -> subst -> subst
val singleton: var -> term -> subst
val remove : var -> subst -> subst 
val find   : var -> subst -> term
val map    : (term -> term) -> subst -> subst 
val fold   : (var -> term -> 'a -> 'a) -> subst -> 'a -> 'a
val iter   : (var -> term -> unit) -> subst -> unit


type termDBref = TermDB.termDB ref

(* replace_vars: returns term in which all varibles in_term are replaced by by_term *)
(* and adds this term to termDB *)
(* we assume that  by_term and in_term are in term_db*)

(* replace_vars does not put in new terms in termDB *)
                             (*by_term*) (*in_term*)

(*replace_vars Some(bot_term) by_term_map in_term *)														
val replace_vars : term option -> term Symbol.Map.t -> term -> term 

(* grounds terms according vtype -> term; if vtype is not in the map then bot is used *) 
val grounding    : termDBref -> term Symbol.Map.t -> term -> term 

val var_renaming_to_subst : termDBref -> Var.renaming -> subst

(* normalise var term by subst*)
(* we assume  that there is no var cycles in subst *)
val find_normalised : subst -> term -> term 

(* normalise any term by subst
   we assume that there is no var cycles in subst *)
(* new term is not added to the term_db *)
val normalise_term : subst -> term -> term  


(* applies substituion and adds obtained term into term_db *)
(* nothing is renamed, see substBound for this  *)
(* we assume that all terms in subst and t are in term_db *)
val apply_subst_term : termDBref -> subst -> term -> term


(*------- renaming terms ---------*)

(* let rename_term_init away_var_list = *)
(* returns initial  fresh_vars_env and rename_subst to be used for future renamings *)
val rename_term_init : var list -> Var.fresh_vars_env * subst

(* let rename_term term_db_ref fresh_vars_env rename_subst t = *)
val rename_term_env : termDBref -> Var.fresh_vars_env -> subst -> term -> subst * term
val rename_term_list_env : termDBref -> Var.fresh_vars_env -> subst -> term list -> subst * (term list)

(* let rename_term_list term_db_ref away_var_list term_list =  returns (rename_subst,renamed_term_list) *)
val rename_term_list : termDBref -> var list -> term list -> subst * (term list)


(*------------------*)
val to_stream      : 'a string_stream -> subst -> unit
val out            : subst -> unit


val to_string : subst -> string 
