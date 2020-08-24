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


(* Logical interface *)
(* shorthands for frequently used functions: building terms, clauses, equiations etc. *)

open Lib

module SSet  = Symbol.Set
module SMap  = Symbol.Map
module SHtbl = Symbol.Hashtbl


module VSet = Var.VSet
module VMap = Var.VMap
module VHtbl = Var.VHashtbl

module BVSet = Var.BSet
module BVMap = Var.BMap
module BVHtbl = Var.BHashtbl

module TSet = Term.Set
module TMap = Term.Map
module THtbl = Term.Hashtbl

module CSet = Clause.CSet
module CMap = Clause.CMap
module CHtbl = Clause.CHashtbl

(* basic clause as key *)
module BCSet = Clause.BCSet  
module BCMap = Clause.BCMap 
module BCHtbl = Clause.BCHashtbl

(*----------------------------*)

type var    = Var.var
type symbol = Symbol.symbol
type stype = Symbol.stype
type term = Term.term
type args = Term.args
type lit = term
type lits = lit list
type literal = lit
type clause = Clause.clause
type tstp_source = Clause.tstp_source
type context = Clause.context
(* type proof_search_param = Clause.proof_search_param *)

exception Empty_clause of clause (* = Clause.Empty_clause*)
(*exception Empty_clause of clause *)

(* check_empty_clause raises Empty_clause if the clause is empty *)
val check_empty_clause : clause -> unit 

(*----------- Symbols -----------------*)
type symbol_db_ref = SymbolDB.symbolDB ref
type term_db_ref = TermDB.termDB ref

(** db_refs are taken from Parser_types*)
val symbol_db_ref : SymbolDB.symbolDB ref
val term_db_ref : TermDB.termDB ref

(** create symbol type from arg types and value type; types are symbols themselves *)
val create_stype : (symbol list) -> symbol -> stype

(** create_symbol symbol_name symbol_stype *)
val create_symbol : ?is_special:bool -> string -> stype -> symbol

(* finds the symbol by name, can return Not_found *)
val find_symbol :  string -> symbol

(* val special_symbols_set : SSet.t *)
val is_special_symb : symbol -> bool

(*---------- Terms -------------*)
(* adds term to term_db *)
val add_term_db : term -> term

(** add_fun_term symb arg_list *)
val add_fun_term : symbol -> term list -> term

(** add_fun_term_args symb args *)
val add_fun_term_args : symbol -> args -> term

(** add_var_term var *)
val add_var_term : var -> term

(** add_neg_atom atom *)
val add_neg_atom : term -> term
val add_neg_atom_symb : symbol -> term list -> term

(** add_lit_symb sign symb args *)
val add_lit_symb : bool -> symbol -> term list -> term

(** add_compl_lit lit  *)
val add_compl_lit : term -> term

(* adds 0-ary predicate *)
val add_pred_0 : ?is_special:bool -> string -> term

val term_true : unit -> TermDB.term
val term_false : unit -> TermDB.term

(**  add_typed_equality_term stype_term t s *)
val add_typed_equality_term :
  term -> term -> term -> term

val add_typed_disequality_term :
  term -> term -> term -> term


(** add_typed_equality_term_sym eq_type_sym t s *)
val add_typed_equality_sym :
  symbol -> term -> term -> term

val add_typed_disequality_sym :
  symbol -> term -> term -> term
	
	
(** add_term_algebra_eq_term args *)
val add_term_algebra_eq_term : term list -> term

val term_true  : unit -> term 
val term_false : unit -> term 

(*----------- term views (not finished) ----------*)
(* term_eq_view_type_term decomposes equational term into *)
(* Def(Eq_type_term(equality_type_term, t,s)) or Undef if term is not equality  *)

type eq_view_type_term = Eq_type_term of term * term * term
val term_eq_view_type_term : Term.term -> eq_view_type_term param

(* term_eq_view_type_symb is similar only equality_type_symb in place of  equality_type_term *)
(* should be used with care since we assume that eq type is not a variable here *)	
type eq_view_type_symb = Eq_type_symb of symbol * term * term
val term_eq_view_type_symb : Term.term -> eq_view_type_symb param


(**---------Clause-----------*)


(** create_clause tstp_source proof_search_param lits, can raise  Empty_clause (empty_clause) *)
val create_clause :
    ?is_negated_conjecture:bool -> 
    ?bc_imp_inh:int ->
    tstp_source -> 
      lit list -> clause

(** create_clause_context: create and add clause to context/returns old if already exists in the context *)

val create_clause_context :
    context ->
      ?is_negated_conjecture:bool -> 
      ?bc_imp_inh:int ->
      tstp_source ->
	lit list -> clause
	    
	
val get_lits : clause -> lit list
	
val clause_register_subsumed_by : context -> by:clause -> clause -> unit

val normalise_blitlist_list :
    SubstBound.bound_subst ->
      ((lit list) Lib.bind) list -> term list


	
(**--- pretty printing clause ----*)		

val pp_clause_with_source :
			(* function for global justification of global subsumption, default is None, see tstpProof for such function *)
  ?global_subsumption_justification_fun:(int ->
                                         clause -> clause -> clause list)
                                        option ->
(* default is false *)																											
  ?clausify_proof:bool -> 
  Format.formatter ->
	clause -> unit

val pp_clause_list_with_source :
  ?global_subsumption_justification_fun:(int ->
                                         clause -> clause -> clause list)
                                        option ->													
  ?clausify_proof:bool -> 
	Format.formatter ->
	clause list -> unit

	
	
(**------------clause context-------------------*)	
val context_create : unit -> context
val context_add : context -> clause -> clause
val context_remove : context -> clause -> unit
val context_mem : context -> clause -> bool

(* literals are not normalised unlike when create_clause *)
(* val context_mem_lits : context -> lits -> bool *)

(* val context_reset : context -> unit *)
val context_find : context -> clause -> clause

(* literals are not normalised unlike when create_clause *)
(* val context_find_lits : context -> lits -> clause  *)
val context_iter : context -> non_dead:bool -> (clause -> unit) -> unit
val context_fold : context -> non_dead:bool -> (clause -> 'a -> 'a) -> 'a -> 'a
val context_size : context -> non_dead:bool -> int

(* context_add_context from_cxt to_cxt *)
(* val context_add_context : context -> context -> unit *)

(** replaces dead with simplified_by *)
(* val context_replace_by_clist : context -> clause list -> clause list *)


(*---- for aguments which are either context or list we can use --------*)

type context_list = Clause.context_list 

(* Clause.CL_Context of context | Clause.CL_List of clause list *)


val cl_iter :  (clause -> unit)  -> context_list -> unit
val cl_fold :  ('a -> clause -> 'a) -> 'a -> context_list -> 'a
val cl_size : context_list -> int

(*--------- check if the current mode is verification -------------------*)
val is_ver_epr : unit -> bool

(*------ debug output (outdated) ----------*)

val out_symbs : unit -> unit

val out_terms : unit -> unit

val out_basic_mem : unit -> unit
