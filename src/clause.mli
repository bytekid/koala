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
module VSet = Var.VSet
module SSet = Symbol.Set
module SMap = Symbol.Map
module TSet = Term.Set

type var = Var.var
type bound_var = Var.bound_var
type term = Term.term
type bound_term = Term.bound_term
type term_db = TermDB.termDB
type term_db_ref = term_db ref
type subst = Subst.subst
type bound = int
type bound_subst = SubstBound.bound_subst
type symbol = Symbol.symbol
type dismatching = Dismatching.constr_set
type literal = Term.literal
type lit = literal
type lits = lit list
type literal_list = literal list
type b_litlist = literal_list Lib.bind

exception Term_compare_greater
exception Term_compare_less



(* type basic_clause *)
(*
type sel_place = int
*)

type clause
(*
and proof_search_param
and replaced_by =
  | RB_subsumption of clause
  | RB_sub_typing of clause
  | RB_splitting of clause list
  | RB_copy of clause
  | RB_unflat of clause
  | RB_tautology_elim
  | RB_orphan_elim of clause (* is not used  for replacements *)
*)
(*and axiom = Eq_Axiom | Distinct_Axiom | Less_Axiom | Range_Axiom | BMC1_Axiom*)
and tstp_internal_source =
  | TSTP_definition
  | TSTP_assumption
  | TSTP_arg_filter_axiom
  | TSTP_def_merge_axiom 
  | TSTP_def_merge_nf_impl
  | TSTP_prop_impl_unit
  | TSTP_tmp
and tstp_theory_bmc1 =
    TSTP_bmc1_path_axiom of int
  | TSTP_bmc1_reachable_state_axiom of int
  | TSTP_bmc1_reachable_state_conj_axiom of int
  | TSTP_bmc1_reachable_state_on_bound_axiom of int
(*	|  TSTP_bmc1_reachable_sk_replacement of int * clause *)
  | TSTP_bmc1_only_bound_reachable_state_axiom of int
  | TSTP_bmc1_clock_axiom of int * Symbol.symbol * int list
(*	| TSTP_bmc1_instantiated_clause of int * clause *)
and tstp_theory =
    TSTP_equality
  | TSTP_distinct
  | TSTP_irref
  | TSTP_domain
  | TSTP_bmc1 of tstp_theory_bmc1
  | TSTP_less
  | TSTP_range
  | TSTP_bv_succ
  | TSTP_bv_shl1
  | TSTP_bv_shr1
  | TSTP_bv_add 
  | TSTP_bv_sub
  | TSTP_bv_bvugt 
  | TSTP_bv_bvuge 
  | TSTP_bv_bvult 
  | TSTP_bv_bvule  
  | TSTP_bv_bveq 

and tstp_external_source =
    TSTP_file_source of string * string
  | TSTP_theory of tstp_theory
and tstp_inference_rule =
    Instantiation of clause list
  | Resolution of literal list
  | Resolution_lifted of literal list
  | Factoring of literal list
  | Global_subsumption of int
  | Forward_subsumption_resolution
  | Backward_subsumption_resolution
  | Splitting of term list
  | Grounding of (var * term) list
  | Dom_res
  | Lifting
  | Non_eq_to_eq
  | Subtyping
  | Flattening
  | Unflattening
  | Arg_filter_abstr
  | True_false
  | Eq_res_simp
  | Dis_eq_elim
  | Def_merge
  | Copy
  | Renaming
  | TSTP_bmc1_instantiated_clause of int 
  | TSTP_bmc1_reachable_sk_replacement of int (* replacing c(sK) by c($constBN) where sK occured in $reachable(sK)*)
  | TSTP_bmc1_init_or_property_axiom
  | TSTP_bmc1_merge_next_func 
and tstp_inference_record = tstp_inference_rule * clause list
and tstp_source =
    TSTP_external_source of tstp_external_source
  | TSTP_internal_source of tstp_internal_source
  | TSTP_inference_record of tstp_inference_record

type bound_clause = clause Lib.bind
(*type bound_bclause = basic_clause Lib.bind *)

(* val get_bclause : clause -> basic_clause *)

(*type lits_fast_key*)

val get_fast_key : clause -> int

val equal_clause : clause -> clause -> bool
val equal : clause -> clause -> bool
val compare : clause -> clause -> int

val hash_bc : clause -> int
val hash    : clause -> int

(** a clauses always placed in a context *)

type context

(** create_context *)
val context_create : unit -> context
val context_add : context -> clause -> clause
val context_remove : context -> clause -> unit

val context_mem : context -> clause -> bool

(* literals are not normalised unlike wnen create_clause *)
(* val context_mem_lits : context -> lits -> bool *)

(* val context_reset : context -> unit *)
val context_find : context -> clause -> clause


(* if non_dead is true then function is applied only to non-dead clauses; otherwise to all clauses *)
val context_iter : context -> non_dead:bool -> (clause -> unit) -> unit
val context_fold : context -> non_dead:bool -> (clause -> 'a -> 'a) -> 'a -> 'a
val context_size : context -> non_dead:bool -> int

(* context_add_context from_cxt to_cxt *)
(* val context_add_context : context -> context -> unit *)

(** replaces clausews with replaced_by (recusively) *)
(*val context_replace_by : context -> clause -> clause list*)
(* val context_replace_by_clist :  context -> clause list -> clause list *)
(*val template_clause : basic_clause -> clause*)

val context_to_list : context -> non_dead:bool -> clause list 

val context_to_string : context -> non_dead:bool -> string


(* creates a new context to which clauses are added with new params *)
val context_copy : non_dead:bool -> context -> context

(* copies clauses from_cc into to_cc with new params if they are not already in to_cc *)
val context_copy_from_to : non_dead:bool -> from_cc:context -> to_cc:context -> unit

(*---- for aguments which are either context or list we can use --------*)

type context_list = CL_Context of context | CL_List of clause list

val cl_iter :  (clause -> unit)  -> context_list -> unit
val cl_fold :  ('a -> clause -> 'a) -> 'a -> context_list -> 'a
val cl_size : context_list -> int
val cl_to_string : context_list -> string

(*-----------------*)

(** creates a clause within a context; use create_neg_conjecture if a clause is a negate conjectue *)
(** literals are normalised, use create_clause_raw for creating with literals as it is *)
val create_clause :
    term_db_ref -> ?is_negated_conjecture:bool -> ?bc_imp_inh:int -> tstp_source -> literal_list -> clause

val create_neg_conjecture :
    term_db_ref -> ?bc_imp_inh:int -> tstp_source -> literal_list -> clause

(* clause with literals as it is (non-normalised)*)
val create_clause_raw :
    tstp_source -> ?bc_imp_inh:int -> literal_list -> clause

val copy_clause : clause -> clause
(* val refresh_ps_param_clause : clause -> clause *)

(* clears tstp_source of the clause should not be used after that     *)
(* unless it was recoreded in propositional solver for proof purposes *)

(*val clear_clause : clause -> unit*)

(*-----*)
val get_lits : clause -> literal_list

(** get_literals = get_lits *)
val get_literals : clause -> literal_list

val get_lits_clause_list : clause list -> TSet.t
val get_atoms_clause_list : clause list -> TSet.t

(* the same as equal_basic_clause *)
val equal_bc : clause -> clause -> bool	

(*val compare_lits : clause -> clause -> int*)

exception Empty_clause of clause 


val is_empty_clause : clause -> bool

(**-------- output ------------*)

val to_stream : 'a Lib.string_stream -> clause -> unit

val out : clause -> unit

val to_string : clause -> string

val clause_list_to_stream : 'a Lib.string_stream -> clause list -> unit

val out_clause_list : clause list -> unit

val clause_list_to_string : clause list -> string

(* val axiom_to_string : axiom -> string *)

val tptp_to_stream : 'a Lib.string_stream -> clause -> unit
val out_tptp : clause -> unit
val to_tptp : clause -> string
val clause_list_tptp_to_stream : 'a Lib.string_stream -> clause list -> unit
val out_clause_list_tptp : clause list -> unit
val clause_list_to_tptp : clause list -> string

(**------pretty priting------------*)
(* val pp_axiom : Format.formatter -> axiom -> unit *)
val pp_clause_name : Format.formatter -> clause -> unit
val pp_clause_with_id : Format.formatter -> clause -> unit
val pp_clause : Format.formatter -> clause -> unit
val pp_clause_min_depth : Format.formatter -> clause -> unit
val pp_literals_tptp : Format.formatter -> Term.term list -> unit
val pp_clause_literals_tptp : Format.formatter -> clause -> unit
val pp_clause_tptp : Format.formatter -> clause -> unit
val pp_clause_list_tptp : Format.formatter -> clause list -> unit

val pp_clause_with_source :

(* function for global justification of global subsumption, default is None, see tstpProof for such function *)
    ?global_subsumption_justification_fun: (int ->
      clause -> clause -> clause list)
    option ->
(* default is false *)
      ?clausify_proof: bool ->
	Format.formatter ->
	  clause -> unit

val pp_clause_list_with_source :
    ?global_subsumption_justification_fun: (int ->
      clause -> clause -> clause list)
    option ->
      ?clausify_proof: bool ->
	Format.formatter ->
	  clause list -> unit

(* output of parameters of a clause *)
(*
  type clause_fun_type =
  FInt of (clause -> int)
  | FStr of (clause -> string)
  | FFloat of (clause -> float)
  | FBool of (clause -> bool)
  | FTerm of (clause -> term)
  | FTerm_list of (clause -> term list)
  | FSymb of (clause -> symbol)
  | FClause of (clause -> clause)
  | FClause_list of (clause -> clause list)
  | FReplaced_by of (clause -> replaced_by)
 *)

type 'a fun_type =
    FInt of ('a -> int)
  | FStr of ('a -> string)
  | FFloat of ('a -> float)
  | FBool of ('a -> bool)
  | FTerm of ('a -> term)
  | FTerm_list of ('a -> term list)
  | FSymb of ('a -> symbol)
  | FClause of ('a -> clause)
  | FClause_list of ('a -> clause list)
(*  | FReplaced_by of ('a -> replaced_by) *)

type clause_fun_type = clause fun_type

(* one can output any list of [(paremater_name, fun_type)] *)
(* predefined param_lists are below *)

type param_out_list = (string * clause_fun_type) list

val param_out_list_gen : param_out_list
val param_out_list_bmc1 : param_out_list
(*
val param_out_list_ps : param_out_list
val param_out_list_res : param_out_list
val param_out_list_inst : param_out_list
*)
val param_out_list_all : param_out_list

val pp_clause_params :
    param_out_list -> Format.formatter -> clause -> unit

(*-------------------*)

(* val get_proof_search_param : clause -> proof_search_param *)

(*
exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef

val assign_prop_solver_id : clause -> int -> unit
val get_prop_solver_id : clause -> int option
*)
(* val get_bc : clause -> basic_clause
   val get_bc_node : clause -> basic_clause_node
   val equal_bc : clause -> clause -> bool
 *)

(*------------*)
val memq : literal -> clause -> bool
val exists : (literal -> bool) -> clause -> bool
val find : (literal -> bool) -> clause -> literal
val fold : ('a -> literal -> 'a) -> 'a -> clause -> 'a
val find_all : (literal -> bool) -> clause -> literal list
val partition : (literal -> bool) -> clause -> literal list * literal list
val iter : (literal -> unit) -> clause -> unit

(*
  val bc_set_bool_param : bool -> int -> clause -> unit
  val bc_get_bool_param : int -> clause -> bool
  val ccp_get_bool_param : int -> clause -> bool
  val ccp_set_bool_param : bool -> int -> clause -> unit
 *)

(** general clause params *)
val is_negated_conjecture : clause -> bool
val is_ground : clause -> bool
val is_horn : clause -> bool
val is_epr : clause -> bool
val is_eq_axiom : clause -> bool
val assign_is_eq_axiom : bool -> clause -> unit
val has_eq_lit : clause -> bool
val has_eq_lit_clause_list : clause list -> bool
val has_conj_symb : clause -> bool
val has_non_prolific_conj_symb : clause -> bool
val has_bound_constant : clause -> bool
val has_next_state : clause -> bool
val has_reachable_state : clause -> bool
val num_of_symb : clause -> int
val num_of_var : clause -> int
val length : clause -> int
val get_max_atom_input_occur : clause -> symbol Lib.param
val get_min_defined_symb : clause -> int Lib.param

val assign_bc_imp_inh : clause -> int -> unit
val get_bc_imp_inh : clause -> int

(** get/assign general clause params *)

(* val assign_tstp_source : clause -> tstp_source -> unit *)
val get_tstp_source : clause -> tstp_source
val get_main_parents : clause -> clause list
val get_parents : clause -> clause list

(** non recursive *)
(* val get_replaced_by : clause -> replaced_by Lib.param *)

(** recursively until non_replaced clauses *)
(*val get_replaced_by_rec : clause list -> clause list*)

(* val assign_replaced_by : replaced_by Lib.param -> clause -> unit *)

val get_conjecture_distance : clause -> int
val assign_conjecture_distance : int -> clause -> unit

val inherit_conjecture : clause -> clause -> unit
val get_min_conjecture_distance_clist : clause list -> int

val get_is_dead : context -> clause -> bool
val assign_is_dead : context -> bool -> clause -> unit

(*
val in_unsat_core : clause -> bool
val assign_in_unsat_core : bool -> clause -> unit
*)

(*
val in_prop_solver : clause -> bool
val assign_in_prop_solver : bool -> clause -> unit
*)

(* reevaluates has_non_prolific_conj_symb, assuming lits are already reevaluated *)
val reset_has_non_prolific_conj_symb : clause -> unit
val reset_has_conj_symb : clause -> unit

(** proof search bool param*)
(*
val get_ps_in_active : clause -> bool
val set_ps_in_active : bool -> clause -> unit
val get_ps_in_subset_subsumption_index : clause -> bool
val set_ps_in_subset_subsumption_index : bool -> clause -> unit
val get_ps_in_subsumption_index : clause -> bool
val set_ps_in_subsumption_index : bool -> clause -> unit
val get_ps_in_passive_queue : clause -> bool
val set_ps_in_passive_queue : bool -> clause -> unit
val get_ps_sel_max : clause -> bool
val set_ps_sel_max : bool -> clause -> unit
val get_ps_simplifying : clause -> bool
val set_ps_simplifying : bool -> clause -> unit
*)
(** proof search non-bool param *)

(* val clear_proof_search_param : clause -> unit *)

val get_ps_when_born : clause -> int
val assign_ps_when_born : int -> clause -> unit

val assign_ps_when_born_concl :
    prem1: clause list -> prem2: clause list -> c: clause -> unit

(*
val add_inst_child : clause -> child: clause -> unit
val get_inst_children : clause -> clause list
*)

(** res non-bool param *)

(*
exception Res_sel_lits_undef
val res_sel_is_def : clause -> bool
val get_res_sel_lits : clause -> literal_list
val res_assign_sel_lits : literal_list -> clause -> unit
*)
(** inst bool param *)

(** inst non-bool param *)
(*
exception Sel_lit_not_in_cluase
val inst_find_sel_place : 'a -> 'a list -> int
val inst_assign_sel_lit : literal -> clause -> unit
val inst_assign_dismatching : dismatching -> clause -> unit
exception Inst_sel_lit_undef
val inst_get_sel_lit : clause -> term
val inst_compare_sel_place : clause -> clause -> int
exception Dismatching_undef
val get_inst_dismatching : clause -> dismatching
val inst_get_activity : clause -> int
val inst_assign_activity : int -> clause -> unit
*)

(**---- tstp sources -----*)
val tstp_source_instantiation : clause -> clause list -> tstp_source
val tstp_source_resolution : clause list -> literal list -> tstp_source
val tstp_source_resolution_lifted : clause list -> literal list -> tstp_source
val tstp_source_factoring : clause -> literal list -> tstp_source
val tstp_source_subtyping : clause -> tstp_source
val tstp_source_input : string -> string -> tstp_source
val tstp_source_global_subsumption : int -> clause -> tstp_source
val tstp_source_non_eq_to_eq : clause -> tstp_source
val tstp_source_dom_res : clause -> tstp_source 
val tstp_source_lifting : clause -> tstp_source 
val tstp_source_copy : clause -> tstp_source
val tstp_source_def_merge : clause -> tstp_source
val tstp_source_renaming : clause -> tstp_source
val tstp_source_forward_subsumption_resolution :
    clause -> clause list -> tstp_source
val tstp_source_backward_subsumption_resolution : clause list -> tstp_source
val tstp_source_split : term list -> clause list -> tstp_source
val tstp_source_flattening : clause -> tstp_source
val tstp_source_unflattening : clause -> tstp_source
val tstp_source_arg_filter_abstr : clause -> tstp_source
val tstp_source_bmc1_merge_next : clause -> tstp_source
val tstp_source_true_false : clause -> tstp_source
val tstp_source_grounding : (var * term) list -> clause -> tstp_source
val tstp_source_theory_axiom : tstp_theory -> tstp_source
val tstp_source_axiom_equality : tstp_source
val tstp_source_axiom_distinct : tstp_source
val tstp_source_axiom_irref : tstp_source
val tstp_source_axiom_domain : tstp_source
val tstp_source_axiom_less : tstp_source
val tstp_source_axiom_range : tstp_source

(* bv operations axioms*)
val tstp_source_axiom_bv_succ : tstp_source
val tstp_source_axiom_bv_shl1 : tstp_source
val tstp_source_axiom_bv_shr1 : tstp_source
val tstp_source_axiom_bv_add :  tstp_source
val tstp_source_axiom_bv_sub :  tstp_source
val tstp_source_axiom_bv_bvugt : tstp_source
val tstp_source_axiom_bv_bvuge : tstp_source
val tstp_source_axiom_bv_bvult : tstp_source
val tstp_source_axiom_bv_bvule : tstp_source
val tstp_source_axiom_bv_bveq : tstp_source



val tstp_source_axiom_bmc1 : tstp_theory_bmc1 -> tstp_source
val tstp_source_assumption : tstp_source
val tstp_source_arg_filter_axiom : tstp_source
val tstp_source_def_merge_axiom : tstp_source
val tstp_source_def_merge_nf_impl : tstp_source
val tstp_source_prop_impl_unit : tstp_source
val tstp_source_definition : tstp_source
val tstp_source_tmp : tstp_source


(**---------*)
val fold_sym : ('a -> symbol -> 'a) -> 'a -> clause -> 'a
val iter_sym : (symbol -> unit) -> clause -> unit

(* bool is sign of the literal *)
val fold_pred : ('a -> bool -> Term.symbol -> 'a) -> 'a -> clause -> 'a
val iter_pred : (bool -> Term.symbol -> unit) -> clause -> unit

(* def below  
  val find_all_pred : is_relevant:(bool -> symbol -> bool) -> clause -> SSet.t
  val find_all_sym :  is_relevant:(symbol -> bool) -> clause -> SSet.t
 *)

val cut_literal_from_list : term -> term list -> term list

val cmp : ('a -> 'b) -> 'a -> 'a -> int
val cmp_num_var : clause -> clause -> int
val cmp_num_symb : clause -> clause -> int
val cmp_num_lits : clause -> clause -> int
val cmp_age : clause -> clause -> int
val cmp_ground : clause -> clause -> int
val cmp_horn : clause -> clause -> int
val cmp_epr : clause -> clause -> int
(* val cmp_in_unsat_core : clause -> clause -> int *)
val cmp_has_eq_lit : clause -> clause -> int
val cmp_has_conj_symb : clause -> clause -> int
val cmp_has_bound_constant : clause -> clause -> int
val cmp_has_next_state : clause -> clause -> int
val cmp_has_reachable_state : clause -> clause -> int
val cmp_has_non_prolific_conj_symb : clause -> clause -> int
val cmp_conjecture_distance : clause -> clause -> int
val cmp_max_atom_input_occur : clause -> clause -> int
val cmp_min_defined_symb : clause -> clause -> int
val cl_cmp_type_to_fun : Options.cl_cmp_type -> clause -> clause -> int
val cl_cmp_type_list_to_lex_fun :
    Options.cl_cmp_type list -> clause -> clause -> int
exception Literal_not_found

val cl_measure_to_fun : Options.cl_measure_type -> (clause -> int)

(*------------- Set/Map/Hashtbl --------------------------*)

(*- basic clause as the key ---*)
module BCSet : Set.S with type elt = clause 
module BCMap : Map.S with type key = clause
module BCHashtbl : Hashtbl.S with type key = clause


(*--------- clause as the key ---------*)
module Key :
    sig
      type t = clause
      val equal : 'a -> 'a -> bool
      val hash : clause -> int
      val compare : clause -> clause -> int
    end

module CMap : Map.S with type key = clause
module CSet : Set.S with type elt = clause
module CHashtbl : Hashtbl.S with type key = clause

type clause_set = CSet.t

(*-------*)
val clause_list_to_set : CSet.elt list -> CSet.t



val apply_bsubst :
    SubstBound.term_db_ref ->
      SubstBound.bound_subst -> int -> Term.term list -> SubstBound.term list

val apply_bsubst_norm_subst :
    SubstBound.term_db_ref ->
      SubstBound.bound_subst ->
	SubstBound.bound ->
	  Term.term list -> SubstBound.term list * SubstBound.subst

(**-----normalisations--------*)

val normalise_b_litlist :
    TermDB.termDB ref ->
      SubstBound.bound_subst ->
	Term.literal list Lib.bind -> SubstBound.term list

val normalise_blitlist_list :
    TermDB.termDB ref ->
      SubstBound.bound_subst ->
	Term.literal list Lib.bind list -> Term.term list

val normalise_lit_list :
    TermDB.termDB ref -> Term.literal list -> Term.term list

(* as normalise_lit_list but also returns variable renaming *)
(* normalise literals are exactly as they would be when creating a new clause *)
val normalise_lit_list_renaming : 
  TermDB.termDB ref -> Term.literal list -> (Term.term list * Var.renaming)


(*
  val create_normalise :
  TermDB.termDB ref ->
  context ->
  tstp_source ->
  proof_search_param -> Term.literal list -> clause
 *)

(*--------------*)
(*
val get_non_simplifying_parents : clause -> clause list
val get_orphans : clause -> clause list
*)

val get_skolem_bound_clause : clause -> Term.term option

(*--------------*)
val replace_subterm :
    TermDB.termDB ref ->
      Term.term -> Term.term -> Term.term list -> Term.term list

(**---clause signature ----*)

type sym_set = Symbol.sym_set

type clause_signature = {
    mutable sig_fun_preds : sym_set;
    mutable sig_eq_types : sym_set;
    mutable sig_pure_dis_eq_types : sym_set;

    mutable sig_flat_arg_flags : (bool list) SMap.t 
  (* 
     maps to flat signature: f->[b_1,..,b_n] 
     where b_i is true if all f-terms have a variable in arg_i and false otherwise 
     f include pred symbols other than equality; 
     used in congruence reduction
  *)
  }

val create_clause_sig : unit -> clause_signature
val extend_clause_sig_term : clause_signature -> bool ->Term.term -> unit
val extend_clause_sig_lit : clause_signature -> Term.literal -> unit
val extend_clause_sig_cl : clause_signature -> clause -> unit
val extend_clause_list_signature : clause_signature -> clause list -> unit
val clause_list_signature : clause list -> clause_signature

(*-------------*)
val add_var_set : Var.VSet.t -> clause -> Var.VSet.t
val get_var_set : clause -> Var.VSet.t
val get_var_list : clause -> Var.VSet.elt list

(* anti-skolemization *)
val get_all_skolem_constants : clause -> Symbol.Set.t
val set_to_list : Symbol.Set.t -> symbol list
val get_state_skolem_const : symbol list -> symbol list

val assign_is_essential_input_symb : context_list -> unit
val unassign_is_essential_input_symb : context_list -> unit

(* assime that symb is in the symbDB *)
val has_symb : symbol -> clause -> bool

val out_clauses_param : context_list -> unit

(* remove clauses with the same basic clause *)
val remove_bc_duplicates : clause list -> clause list 



(*---------------------------*)

(* (is_relevant sign symb) *)
val find_all_pred : is_relevant_pred:(bool -> symbol -> bool) -> clause -> SSet.t

val find_all_sym :  is_relevant_symb:(symbol -> bool) -> clause -> SSet.t

val out_mem : unit -> unit
