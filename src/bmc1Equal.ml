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
open Options
open Logic_interface
open Bmc1Common


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_split

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_split -> "split"
	
let dbg_groups =
  [
   D_trace;
   D_split;
 ]
    
let module_name = "bmc1Equal"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    

(*----- debug -----*)


(* functions to create everything related to $$equiv_state(X,Y) predicate *)
let state_predicates = ref []

let split clauses = 
  Splitting.splitting Definitions.def_env_glb ~out_progress:false clauses


(* dirty hack *)
let is_split_sym_name str = 
  try
    match (Str.first_chars str 2) with
    |"sP" -> true
    | _ -> false
  with
    Invalid_argument _ -> false

let is_split_symbol symb = 
  is_split_sym_name (Symbol.get_name symb)

(* return true if a symbol is a predicate with a first parameter of a state_type *)
let is_state_predicate symb =
  if (Symbol.is_skolem symb) || (is_split_symbol symb)
  then false
  else
    begin
  (* return true if a type is state_type *)
    let is_state_type atype = (atype == state_type) in
    (* return true if 1st element in the non-empty list is state_type and all other aren't *)
    let is_state_pred_args_non_empty types = 
      (* folder for the list of types *)
      let f bool atype = bool && (not (is_state_type atype)) in
      (* return true if there are no state_type in a list of types *)
      let no_state_type types = List.fold_left f true types in
      (* head of a list is a state_type and the tail has no state_type *)
      (is_state_type (List.hd types)) && (no_state_type (List.tl types))
    in
    (* process arguments of a (possible empty) list *)
    let is_state_pred_args types =
      if list_is_empty types
      then false
      else is_state_pred_args_non_empty types
    in
    (* no arguments defined => not a state predicate *)
    match Symbol.get_stype_args_val symb with
    | Def((args,value)) -> is_state_pred_args args
    | Undef -> false
    end


(* helper function that returns a list of all the state predicates from given set *)
let get_state_predicates_from_set set =
  (* folder *)
  let f symb list =
    if is_state_predicate symb
    then symb :: list
    else list
  in
  (* fold the set *)
  Symbol.Set.fold f set []

(* helper finction: get a list of all state predicates from a given list of clauses *)
let get_state_predicates_from_clauses clauses =
  (* helper: all symbol to a set *)
  let add_symb set symb = Symbol.Set.add symb set in
  (* add all symbols from transition clause to a set *)
  let add_all_symb set clause =
    let equal_DEBUG = false in
    if equal_DEBUG
    then (* all all predicates anyway *)
      Clause.fold_sym add_symb set clause
    else (* add only predicates from the NEXT state clauses *)
      if Clause.has_next_state clause
      then Clause.fold_sym add_symb set clause
      else set;
  in
  (* collect all symbols from all clauses *)
  let set = List.fold_left add_all_symb Symbol.Set.empty clauses in
  (* get all the state predicates from the set *)
  get_state_predicates_from_set set

(* helper finction: get a list of all state predicates from a symbolDB *)
let get_state_predicates_from_db () =
  (* add the symbol to the set if it is an essential input *)
  let add_candidate symb set =
    if Symbol.is_essential_input symb
    then Symbol.Set.add symb set
    else set
  in
  (* get the set of all essential inputs *)
  let set = SymbolDB.fold add_candidate !symbol_db_ref Symbol.Set.empty in
  (* get all the state predicates from the set *)
  get_state_predicates_from_set set

(* helper function: remove from the list of symbols all those that are in the set *)
let remove_set_from_list set list =
  (* folder *)
  let f set list symb =
    if Symbol.Set.mem symb set
    then list
    else symb::list
  in
  (* fold the list *)
  List.fold_left (f set) [] list

(* set of system predicates *)
let get_system_state_predicates () =
  Symbol.Set.add Symbol.symb_ver_init
  (Symbol.Set.add Symbol.symb_ver_property
  (Symbol.Set.add Symbol.symb_ver_eligible
  Symbol.Set.empty))

(*** helpers for creating groundings of state predicates ***)

(* unique index of a constant *)
let const_index = ref 0

(* returns term for unique constant of a given type *)
let build_const_by_type const_type_symb =
  (* build up a const name *)
  let const_name = "const_"^(Symbol.to_string const_type_symb)^"_"^(string_of_int !const_index) in
  (* increase the counter *)
  const_index := succ !const_index;
  (* create a const with the built name *)
  let const = create_constant_term const_name const_type_symb in
  (* return that const *)
  const

(*** implementation of $$equiv_state(X,Y) <- axioms ***)

(* create $$equiv_pred_p(state,state') *)
let create_equal_p_atom p state state' =
  (* new name of a equal predicate for P *)
  let equal_p_name = "$$equiv_pred_"^(Symbol.to_string p) in
  (* create an atom with parameters state_type, state_type *)
  let equal_p_atom =
    create_atom ~is_special:true
      equal_p_name
      [ state_type; state_type ]
      [ state; state' ]
  in
  (* return that atom *)
  equal_p_atom

(* create axioms for \E S,S',C: (P(S,C)<->P(S',C) -> $$equiv_pred_P(S,S') *)
let create_not_equal_axioms state state' p =
  (* create $$equiv_pred_P(S,S') atom *)
  let eq_atom = create_equal_p_atom p state state' in
  (* create unique list C of constants for args of P *)
  let arg_types = get_arg_types_list p in
  let args = List.map build_const_by_type arg_types in
  (* create P(S,C) and P(S',C) *)
  let ps_atom = create_atom_symb p (state :: args) in
  let ps'_atom = create_atom_symb p (state' :: args) in
  (* create TSTP FORNOW *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom 0) in
  (* create clause {$$equiv_pred_P(S,S'), P(S,C), P(S',C)} *)
  let clause_1 = create_clause tstp_source
    [ eq_atom; ps_atom; ps'_atom ]
  in
  (* create clause {$$equiv_pred_P(S,S'), ~P(S,C), ~P(S',C)} *)
  let clause_2 = create_clause tstp_source
    [ eq_atom; (add_compl_lit ps_atom); (add_compl_lit ps'_atom) ]
  in
  (* return new clauses *)
  (clause_1, clause_2)

(* Create equal from clauses for all known predicates *)
let bmc1_create_not_equal_definition state state' =
  (* ensure that the list of predicates is built already *)
  assert (list_non_empty !state_predicates);
  (* fold predicate for non-equal axioms *)
  let non_equal_folder state state' accum p =
    let (cl1, cl2) = create_not_equal_axioms state state' p in
    cl1 :: (cl2 :: accum)
  in
  (* create new axioms for all predicates *)
  let clauses = List.fold_left (non_equal_folder state state') [] !state_predicates in
  (* return those axioms *)
  split clauses

(* create definition for $$equiv_state(S,S') via $$equiv_pred_P(S,S') *)
let create_equal_from_definition predicates =
  (* create S, S' *)
  let state = term_xn state_type 0 in
  let state' = term_xn state_type 1 in
  (* create $$equiv_state(S,S') *)
  let equal_atom = create_equal_state_atom state state' in
  (* create ~$$equiv_pred_P(S,S') *)
  let create_neq_p_lit state state' p =
    add_compl_lit (create_equal_p_atom p state state')
  in
  (* create all neg literals for all predicates *)
  let neg_p_lits = List.map (create_neq_p_lit state state') predicates in
  (* create TSTP FORNOW *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom 0) in
  (* create clause {$$equiv_state(S,S'), ~$$equiv_pred_P1(S,S'), ..., ~$$equiv_pred_Pn(S,S')} *)
  let eq_clause = create_clause tstp_source (equal_atom :: neg_p_lits) in
  (* return that clause *)
  eq_clause


(*** implementation of $$equiv_state(X,Y) -> axioms ***)

(* create axioms for $$equiv_state(S,S') -> A x: (P(S,x)<->P(S',x)) *)
let create_equal_axioms p =
  (* create S, S' *)
  let state = term_xn state_type 0 in
  let state' = term_xn state_type 1 in
  (* create ~$$equiv_state(S,S') *)
  let equal_atom = create_equal_state_atom state state' in
  let equal_lit = add_compl_lit equal_atom in
  (* create vector of free variables x *)
  let x = get_arg_var_list p in
  (* create P(S,x) *) 
  let ps_atom = create_atom_symb p (state :: x) in
  (* create P(S',x) *) 
  let ps'_atom = create_atom_symb p (state' :: x) in
  (* create TSTP FORNOW *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom 0) in
  (* create clause {~$$equiv_state(S,S'), ~P(S,x), P(S',x)} *)
  let clause_1 = create_clause tstp_source
    [ equal_lit; (add_compl_lit ps_atom); ps'_atom ]
  in
  (* create clause {~$$equiv_state(S,S'), P(S,x), ~P(S',x)} *)
  let clause_2 = create_clause tstp_source
    [ equal_lit; ps_atom; (add_compl_lit ps'_atom) ]
  in
  (* return new clauses *)
  (clause_1, clause_2)

(* Create equal clauses for all predicates *)
let create_equal_to_definition predicates =
  (* fold predicate for equal axioms *)
  let equal_folder accum p =
    let (cl1, cl2) = create_equal_axioms p in
    cl1 :: (cl2 :: accum)
  in
  (* create new axioms for all predicates *)
  let clauses = List.fold_left equal_folder [] predicates in
  (* return those axioms *)
  clauses

(* init state predicates var *)
let init_state_predicates clauses =
  (* selector: when true use clauses, when false, use symbolDB *)
  let use_clauses = true in
  (* let use_clauses = false in *)

  (* predicates to use in $$equiv_state definition *)
  let all_predicates =
    if use_clauses
    then get_state_predicates_from_clauses clauses
    else get_state_predicates_from_db ()
  in
  (* filter out system ones *)
  let predicates = remove_set_from_list (get_system_state_predicates ()) all_predicates in
  (* save those predicates *)
  state_predicates := predicates

(* main function: return axioms that define $$equiv_state(S,S') for the theory clauses *)
let bmc1_define_equal_predicate clauses =
  (* check whether the state predicates are needed *)
  if (need_equal_to_predicate ()) || (need_equal_from_predicate ())
  then init_state_predicates clauses;

  (* create clauses for $$equiv_state(X,Y)->... for those predicates *)
  let equal_to_clauses =
    if need_equal_to_predicate ()
    then create_equal_to_definition !state_predicates
    else []
  in
  (* add clauses for $$equiv_state(X,Y)<-... for those predicates *)
  let all_equal_clauses =
    if need_equal_from_predicate ()
    then (create_equal_from_definition !state_predicates) :: equal_to_clauses
    else equal_to_clauses
  in
  (* return those clauses *)

  split all_equal_clauses
