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

type var    = Var.var
type symbol = Symbol.symbol
type fun_info   
type var_info

type prop_key = TableArray.key


(*association list for counting the number of occurences of vars in a term*)
type var_ass_list = var num_ass_list

type term =
   Fun of symbol * args * fun_info
 | Var of var * var_info 

and grounding = 
  {
   (* id of grounding sustitution that was used to obtain grounded_term *)
   mutable grounding_subst_id : int; 

 (* grounding can change e.g. in finite models or bmc1 *)
   mutable grounded_term : term; (* term obtained after grounding *) 

 }
  and args = term list 
(*
(* when cluase is ground we only store prop_key and when it is non_ground we store current grounded term with the corresponding subst_id *)
and grounding_info =  Grounding_non_gr of grounding_non_gr | Grounding_gr_key of prop_key 
*)

exception Grounding_undef

val assign_grounding : grounding -> term -> unit

(*
type grounding = 
  {
   (* id of grounding sustitution that was used to obtain grounded_term *)
   mutable grounding_subst_id : int; 

(* grounding can change e.g. in finite models or bmc1 *)
   mutable grounded_term : term; (* term obtained after grounding *) 
   (* if the original term was already ground then ground_term reference the term itself *)

   mutable prop_gr_key : prop_key; (* prop_gr_key = prop_gr_key of grounded_term *)

  (* prop. key of term (without grounding) used for simplifiactions *)
(*   mutable prop_key : prop_key param; *)

 }
*)

type literal = term 

type bound_term = term Lib.bind

exception Term_fast_key_undef

val create_var_term       : var -> term
val create_var_term_info  : var -> var_info -> term

val create_fun_term       : symbol -> term list -> term
val create_fun_term_args  : symbol -> args -> term
val create_fun_term_info  : symbol -> term list -> fun_info -> term

val get_num_of_symb       : term -> int
val get_num_of_var        : term -> int

(* assume that term is a Var term*)
val get_var               : term -> var


(* association list of (vars, num_of_occ) *)
val get_var_ass_list          : term -> var_ass_list  

(* adds all vars of the term to the set *)
val add_var_set : Var.VSet.t -> term -> Var.VSet.t

val get_var_set : term -> Var.VSet.t

(** Return the list of variables occurring in the term *)
val get_vars : term -> var list 


(* bool params *)
type fun_term_bool_param 

val has_conj_symb       : fun_term_bool_param
val has_bound_constant  : fun_term_bool_param (* used for BMC *)

val is_next_state_lit   : term -> bool
val is_reachable_state_lit   : term -> bool

val assign_has_conj_symb      : term -> unit

val has_non_prolific_conj_symb : fun_term_bool_param
val assign_has_non_prolific_conj_symb :  term -> unit

val set_fun_bool_param : bool ->  fun_term_bool_param -> term -> unit
val get_fun_bool_param : fun_term_bool_param -> term -> bool 

(* prop_gr_key for the table prop_var-term *)



(* prop. key of term (without grounding) used for simplifiactions *)

exception Prop_key_undef
val get_prop_key          : term -> prop_key

val assign_prop_key       : prop_key -> term -> unit 

(* prop. key of term after grounding *)
(*exception Prop_gr_key_undef*)
val get_prop_gr_key          : term -> prop_key

(*val assign_prop_gr_key       : prop_key -> term -> unit *)
(* *)


(* in place of compl_lit always use: Logic_interface.add_compl_lit *)
val compl_lit   : term -> term
val is_neg_lit  : term -> bool
val is_pos_lit  : term -> bool 
val get_sign_lit : term -> bool (* the same as is_pos_lit *)
val split_sign_lit : term -> bool * term (* get sign and atom *)

(* *)
exception Type_check_failed
val type_check : ?allow_sub_types: bool-> term -> unit

(* as type_check but returns bool instead of raising Type_check_failed *)
val is_well_typed_term : ?allow_sub_types: bool ->  term -> bool 

val is_complementary : term -> term -> bool

(* apply only to literals, returns if a literal is in EPR: all arguments are eiter constants or vars*)
val is_epr_lit  : term -> bool

(* can raise exception Grounding_undef *)
val get_grounding : term -> grounding


val get_grounded_term         : term -> term

(* only atoms get assigned groundings *)
val get_grounding_lit: term -> term

val get_args : term -> args

(* use get_prop_key ! *)
(* propositional id of grounding of the literal *)
(* can raise Term_ground_undef*)
(* val get_propos_gr_id : term -> int *)

(*folds f on all symbols in the term*)
val fold_sym : ('a -> symbol -> 'a) -> 'a -> term -> 'a 

val iter_sym : (symbol-> unit) -> term -> unit

(* folds f to over all subterms inlcuding the term intself *)
val fold_subterms : ('a -> term -> 'a ) -> 'a -> term -> 'a 

(* f: first arg  is depth and second is sym, f is applied from top to bottom*)
(* depth starts with 1, (0 if symbol does not occur) *)
val iter_sym_depth : (int -> symbol -> unit) -> term -> unit 

(* assign_fast_key is done when building termDB *)
 
val assign_fast_key   : term -> int -> unit

val assign_db_id   : term -> int -> unit

(* only to be used in termDB*)
val assign_num_of_symb : term -> unit
(* first arg is a ground term assigned to the second arg *)
(* val assign_grounding  : term  -> term -> unit *)

(* val assign_var_list   : term -> unit *)
val assign_fun_all        : term -> unit
val assign_var_all        : term -> unit

(*
exception Term_hash_undef
(* assume that for all subterms hash has been assigned before*)
(*val assign_hash           : term -> unit*)

(* assigns hash to term without assumptions and returns this hash *)
val assign_hash_full      : term -> int
val get_hash              : term -> int
*)

val arg_map          : (term -> term) -> args -> args	
val arg_map_list     : (term -> 'a) -> args -> 'a list
val arg_to_list      : args -> term list
val list_to_arg      : term list -> args

val is_empty_args       : args -> bool
(* explicitly maps from left to right, 
   since order can matter when use imperative features *)
val arg_map_left     : (term -> term) -> args -> args	


val arg_fold_left    : ('a -> term -> 'a)-> 'a -> args -> 'a
val arg_fold_right   : (term -> 'a -> 'a)-> args -> 'a -> 'a 
val arg_fold_left2   : 
    ('a ->  term -> term -> 'a) -> 'a -> args -> args -> 'a
val arg_for_all2 : (term -> term -> bool) -> args -> args -> bool

val arg_iter  : (term -> unit) -> args -> unit 
val arg_iter2 : (term -> term -> unit) -> args -> args -> unit

(* folds over all subterems of the term including term itself *)
(*val fold_left : ('a -> term -> 'a) -> 'a -> term -> 'a *)
val fold_left_var : ('a -> var -> 'a) -> 'a -> term -> 'a

(* creates a new term by applying f to all its subterms bottom up including term itsef *)
(*val map  : (term -> term) -> term -> term *)
val map_var  : (var -> term) -> term -> term


(* iterates f over term bottom up *)
val iter : (term -> unit) -> term -> unit

(* check whether there extists a subterm (including term itself) satisfying f *)
val exists : (term -> bool) -> term -> bool 


(*  is_subterm s t = true if  s is a subterm of t using == *)
val is_subterm : term -> term -> bool 

val is_constant : term -> bool
val is_const_term : term -> bool
val is_ground   : term -> bool
val is_var      : term -> bool 
val var_in      : var -> term -> bool

(* compare = compare_fast_key and should not be used before 
   fast_key is assigned i.e. termDB is build; 
   before that use compare_key *)  

val compare               : term -> term -> int 

(* compare_key impl. as structural equality used for termDB*)
(* variables and variables as terms Var(v,i) can have different fast keys*)
val compare_key           : term -> term -> int
val compare_key_modulo_var: term -> term -> int
val compare_fast_key      : term -> term -> int

val is_neg_lit            : literal -> bool
val get_atom              : literal -> term
val is_eq_lit             : literal -> bool
val is_eq_atom            : term    -> bool

(* decompose_eq_atom atom then if atom =  "t = s" then returns [t;s], returns [] if atom is not equality *)
val decompose_eq_atom     : term -> term list 

val is_clock_lit : literal -> bool
val is_less_lit : literal -> bool
val is_range_lit : literal -> bool


exception Var_term
val get_top_symb          : term -> symbol
val lit_get_top_symb      : term -> symbol

val get_term_type : term -> symbol

(* compare two terms *)
val cmp_ground   : term -> term -> int 
val cmp_num_symb : term -> term -> int 
val cmp_num_var  : term -> term -> int 
val cmp_sign     : term -> term -> int 
val cmp_split    : term -> term -> int 

val is_split_lit : term -> bool

val lit_cmp_type_to_fun : Options.lit_cmp_type -> (literal -> literal -> int)
val lit_cmp_type_list_to_lex_fun :  
    Options.lit_cmp_type list -> (literal -> literal -> int) 

(*-----------*) 
val lit_bool_prop_to_bool : Options.lit_bool_prop_type -> literal -> bool
val compose_bool_prop_opt_list : (bool->bool->bool) -> bool -> Options.lit_bool_prop_type list -> literal -> bool


(* replace all occurrences of subterm by byterm in t *)
(* we assume that t, p, and q are in the term db and therefore we are using == *)
(* the resulting term will need to be  added in term db separately *)
(* replace : subterterm -> byterm:term -> term -> term *)
val replace : term -> term -> term -> term


val to_stream           : 'a string_stream -> term -> unit
val to_stream_tptp           : 'a string_stream -> term -> unit
val out                 : term -> unit

val pp_term : Format.formatter -> term -> unit
val pp_term_tptp : Format.formatter -> term -> unit

val term_list_to_stream : 'a string_stream -> (term list) -> unit
val out_term_list       : (term list) -> unit

(* better use to_stream *)
val to_string : term -> string
val term_list_to_string : (term list) -> string


(* applies function to atom i.e. if ~p then ~f(p); if p then f(p)  *)
(* f should not return negative literals *)
(* adding to term_db should be done separately  *)
val apply_to_atom : (term -> term) -> term -> term 

val get_fast_key : term -> int

val hash : term -> int

(*---------*)

val is_skolem_const : term -> bool 
val is_skolem_lit   : term -> bool
val is_addr_const   : term -> bool 


(*---------------------------------*)

(* Map/Set for lits of terms *)
module MapList : Map.S with type key = term list
module SetList : Set.S with type elt = term list 


(*---------------------------------*)


module Key :
  sig
    type t = term
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
  end


module Map : Map.S with type key = term
module Set : Set.S with type elt = term
module Hashtbl : Hashtbl.S with type key = term

type term_set = Set.t

val term_list_to_set : term list -> Set.t

(* terms are assumed in termDB *)
val remove_duplicate_terms : term list -> term list

(* replaces subterms based on map; the result needs to be added to term_db  *)
val replace_map : term Map.t -> term -> term

