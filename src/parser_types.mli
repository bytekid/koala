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


exception Parsing_fails
exception FOF_format
exception TFF_format
exception THF_format
open Logic_interface

type buffer_name = FileName of string | Clausifier of string | Stdin
val buffer_name_to_string : buffer_name -> string
val position_init_lnum : Lexing.position -> Lexing.position

val buffer_name_ref : buffer_name Lib.param ref
val assign_current_buffer_name : buffer_name -> unit

val init_lexbuf : buffer_name -> Lexing.lexbuf -> unit
type includes = {
  includes_file_name : string;
  include_formula_list : string list;
  include_source_file_name : buffer_name;
}

(*
val create_clause :
  Clause.tstp_source -> Clause.literal_list -> Clause.clause
*)

(* type problem_format = CNF | FOF | TFF | THF *)

type input_problem_type = FOF | CNF | TFF | THF | AIG | QBF
val input_problem_type  :  (input_problem_type option) ref 

val input_problem_type_to_string : input_problem_type -> string

val assign_input_problem_type : input_problem_type -> unit 

val create_neg_conjecture :
  Clause.tstp_source -> Clause.literal_list -> Clause.clause
val parsed_clauses : Clause.clause list ref
val neg_conjectures : Clause.clause list ref
val includes : includes list ref
val less_map : int SMap.t ref
val range_map : (int * int) SMap.t ref
val clock_map : int list SMap.t ref
val cardinality_map : int SMap.t ref
val max_address_width_map : int SMap.t ref
val state_constant_map : int SMap.t ref
val address_base_name_map : string SMap.t ref
val father_of_map : string list SMap.t ref
val bit_vector_name_map : int SMap.t ref
val memory_name_map : (int * int) SMap.t ref
val pos_deadlock_name_set : Symbol.Set.t ref
val neg_deadlock_name_set : Symbol.Set.t ref

val tff_typed_variable_fun : string -> Symbol.symbol -> unit

val tff_reset_vt : unit -> unit 

type bv_operations =
    BV_add
  | BV_sub
  | BV_bvugt
  | BV_bvuge
  | BV_bvult
  | BV_bvule
  | BV_bveq
  | BV_shl1
  | BV_shr1
val bv_op_to_str : bv_operations -> string
exception Not_BV_OP
val bv_name_to_op : string -> bv_operations
module BV_OP_Key :
  sig
    type t = bv_operations
    val compare : 'a -> 'a -> int
    val equal : 'a -> 'a -> bool
    val hash : 'a -> int
  end
module BV_OP_Htbl :
  sig
    type key = BV_OP_Key.t
    type 'a t = 'a Hashtbl.Make(BV_OP_Key).t
    val create : int -> 'a t
    val clear : 'a t -> unit
    val reset : 'a t -> unit
    val copy : 'a t -> 'a t
    val add : 'a t -> key -> 'a -> unit
    val remove : 'a t -> key -> unit
    val find : 'a t -> key -> 'a
    val find_all : 'a t -> key -> 'a list
    val replace : 'a t -> key -> 'a -> unit
    val mem : 'a t -> key -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val length : 'a t -> int
    val stats : 'a t -> Hashtbl.statistics
  end
type bv_op_symb_arg_names_map = string list SMap.t
val bv_op_htbl : string list SMap.t BV_OP_Htbl.t
val bv_op_add_symb_htbl :
  BV_OP_Htbl.key -> SMap.key -> string list -> unit
val bv_op_get_symb_map : BV_OP_Htbl.key -> string list SMap.t
val distinct : term list list ref
val bot_term : TermDB.term
val top_term : TermDB.term
val is_less_symb : SMap.key -> bool
val is_range_symb : SMap.key -> bool
val is_clock_symb : SMap.key -> bool
val is_less_or_range_symb : SMap.key -> bool
val default_var_type : Symbol.symbol
val max_var_ref : var ref
val var_table_ref : (string, var) Hashtbl.t ref
val init : unit -> unit
val get_clauses_without_extra_axioms : unit -> Clause.clause list
val create_theory_term : Term.symbol -> Term.term list -> TermDB.term
val include_file_fun : string -> string list -> unit
val comment_fun : 'a -> unit
val comment_E_prover_fun : 'a -> unit
val annotation_fun : 'a -> unit
val contains_distinct : bool ref
val analyse_distinct : Term.term list -> unit
val retype_term : Var.symbol -> Term.term -> Term.term
val retype_term_list : Var.symbol list -> Term.term list -> Term.term list
val retype_lit : Term.term -> Term.term
val retype_lits : Term.term list -> Term.term list
val cnf_formula_fun : string -> string -> Term.term list -> 'a -> unit
val is_false_lit : Term.literal -> bool
val disjunction_fun : Term.literal list -> Term.literal -> Term.literal list
val equality_fun : TermDB.term list -> TermDB.term
val inequality_fun : TermDB.term list -> TermDB.term
val neg_fun : Term.term -> TermDB.term
val assign_param_input_symb : Symbol.symbol -> unit
val plain_term_fun : string -> Symbol.stype -> Term.term list -> Term.term
val overriding_arities_warning_was_shown_ref : bool ref
val plain_term_fun_typed :
  is_top:bool -> string -> Term.term list -> Term.term
val defined_term_fun : string -> Term.term list -> TermDB.term
val defined_pred_fun : string -> TermDB.term list -> TermDB.term
val defined_infix_pred_fun :
  string -> TermDB.term -> TermDB.term -> TermDB.term
val reg_exp_less : Str.regexp
val reg_exp_range : Str.regexp
val reg_exp_clock : Str.regexp
val system_pred_name_pref_reg_expr : Str.regexp
val system_pred_fun : string -> Term.term list -> TermDB.term
val system_term_fun : string -> Term.term list -> TermDB.term
val term_variable_fun : Term.var -> Term.term
val variable_fun : string -> var
val num_term : string -> Term.term
val term_of_int_number_fun : int -> Term.term
val term_of_rat_number_fun : int * int -> Term.term
val term_of_real_number_fun : Lib.real -> Term.term
val ttf_atomic_type_fun : string -> SymbolDB.symbol
val is_bound_constant_type : Symbol.symbol -> bool
val ttf_add_typed_atom_out_symb_fun :
  string -> Symbol.stype -> SymbolDB.symbol
val ttf_add_typed_atom_fun : string -> Symbol.stype -> unit
type attr_args =
    Attr_IList of int list
  | Attr_SList of string list
  | Attr_Int of int
  | Attr_Str of string
type attr_type =
    ALess of int
  | ARange of int * int
  | AFatherOf of string
  | ASonOf of string
  | AClock of int list
  | ACardinality of int
  | AStateConstant of int
  | AAddressBaseName of string
  | AAddressMaxWidth of int
  | ABitVector of int
  | AMemory of int * int
  | ABV_OP of bv_operations * string list
  | ADeadlockState of int
  | AAig of string
  | AOther of string * attr_args
type attr = Attr of attr_type * attr_args
val attr_fun : string -> attr_args -> attr_type
val find_recognised_main_attr : attr_type list -> attr_type option
val find_recognisd_bv_operation_attr : attr_type list -> attr_type option
val get_all_father_of : attr_type list -> string list
val is_defined_symbol : attr_type list -> bool
val process_deadlock_attribute : Symbol.Set.elt -> attr_type list -> unit
val ttf_add_typed_atom_atrr_fun :
  string -> Symbol.stype -> attr_type list -> unit
val bv_get_size : SMap.key -> int

val change_conj_symb_input : unit -> unit
