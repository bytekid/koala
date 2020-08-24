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
open Hashcons
open Options
open Statistics

(* do not use Logic_interface since it uses this module *)


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_copy
  | D_create
  | D_flat
  | D_norm

let dbg_gr_to_str = function 
  | D_copy -> "copy"
  | D_create -> "create"
  | D_flat -> "flat"
  | D_norm -> "norm"

let dbg_groups =
  [
(*   D_copy;
   D_create;
   D_flat;
*)
   D_norm;
 ]
    
let module_name = "clause"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)


module VSet = Var.VSet
module SSet = Symbol.Set
module SMap = Symbol.Map
module TSet = Term.Set

type sym_set = Symbol.sym_set

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
(*type dismatching = Dismatching.constr_list_feature *)
type dismatching = Dismatching.constr_set




type literal = Term.literal
type literal_list = literal list
type b_litlist = literal_list bind
type lit = literal
type lits = lit list

exception Term_compare_greater
exception Term_compare_less

let fprintf = Format.fprintf

let clause_global_counter = ref 0
let bc_global_counter = ref 0

let incr_clause_counter () = (clause_global_counter := !clause_global_counter +1)

(* all boolean param of a clause stored in a bit vector (should be in 0-30 range)*)
(* position of the param in the vector *)
(*------------Clause bool param----------------*)
type clause_bool_param = int

(*-------Basic clause bool Param-----*)
(* auto parameters set automatically when clause is created from lits*)
(* user parameters are set by the user *)
let bc_non_ground = 0 (* auto *)
let bc_horn = 1       (* auto *)
let bc_non_epr = 2    (* auto *)
let bc_eq_axiom = 3   (* user *)

(* input_under_eq  is true if a clause is (i) is a eq axiom or (ii) input   *)
(* or (iii) obtained from input by some number of inferences with eq axioms *)
(* so it is false for a cluase  obtained by an inference with two clauses   *)
(* which are both non equality *)
(* not used at the moment; may be in the future                             *)
(* let bc_input_under_eq = 4 *)

let bc_has_eq_lit = 4    (* auto *)
let bc_has_conj_symb = 5 (* auto *) (* basd on Term.has_conj_symb *)
let bc_has_non_prolific_conj_symb = 6 (* auto/user  can be recalculated by the user *)

let bc_has_bound_constant = 7 (* auto *)
let bc_has_next_state = 8 (* auto *)
let bc_has_reachable_state = 9 (* auto *)
(*let bc_large_ax_considered = 10 (* auto *) not used at the moment *)
(* let bc_is_negated_conjecture = 11 *) (* user *) (* TODO: change in the rest of the code! *)


    
(*--------proof search bool params --------------------------*)
(*--------common params for most proof search will be prefixed by ps--*)

(*-------- param common for other  ------------*)


(*----no specific for inst bool param ----*)

(*--------End Bool param------------------*)

(*-----------------*)
(* 1) basic clauses are difined by thier literals and all basic_clauses are globally shared                      *)
(* 2) basic_clauses are used only to define (context) clauses   and should not be used outside of this module *)
(* 3) a (context) clause is an extension of a basic clause with extra paramters including tstp source for proofs and  *)
(*    paramteres used in a process such proof search in inst/res/etc or preprocessing *)
(* 4) context clauses are indexed by basic clauses (so there is no two clauses with the same basic_clause in a contex) *)
(*    but clauses can have different parametes in different contexts  *)
(* 5) for proof reconstruction we are using one propositional solver so if a clauses was added to a uc_solver *)
(*    then later a clause with the same basic clause is never added  *)
(*    this may result in proof mixing contexts but should not be a problem *)
(* 6) in a clause context parameters can be reassigned inplace without switching clause to a new context *)
(*    thus sequantially the same context can be used for any number of inst/res cycles  *)
(*    we need to copy a clause to another context only if simultaniously the same basic clause is used in more than one place *)

type basic_clause =
    {
     lits : literal_list;
     mutable bc_fast_key : int;
     mutable bc_counter : int; (* when 0 we can remove clause from the bc_table *)
     mutable bc_bool_param : Bit_vec.bit_vec;
     mutable length : int;	(* number of all symbols in literals *)
     mutable num_of_symb : int;
     mutable num_of_var : int;
     mutable min_defined_symb : int param; (* minimal defined symbols *)
     mutable max_atom_input_occur : symbol param;
     mutable bc_imp_inh : int; (* user *) 
       (* importantance of clause across contexts; smaller is more important; importance is inherited from parents during inf. *)

(*     mutable prop_solver_id : int option;  *)
   }

(*
type sel_place = int
*)

(*------------------------------------------------------------------------------*)
(* in a given context there is at most one clause with the same  basic_clause *)
(* we can create any number of the same contexts: Inst/Res/Empty                *)
(* the same basic clause can have different proofs in different contexts        *)
(* proofs can have context depend and usage e.g.  deleting all parents of a simplified clause in a context may not be applicable in another context) *)

(* clause_with_context = clause *)
type clause =
    {
     basic_clause : basic_clause;
     fast_key : int;    (* unique id  based on clause_counter *)
     (*  mutable context_id : int; *)  (* clause is identified by context_id and fast_id *)

     tstp_source : tstp_source param;
       
(*     mutable prop_solver_id : int option; (* prop_solver_id is used in uc_solver for djoining special literls for unsat cores/proof recontruction *) *)
     mutable conjecture_distance : int;

     mutable when_born : int param; (* TODO change to local *)
   }

(*-------tstp_source-----------*)
(*
  and axiom =
  | Eq_Axiom
  | Distinct_Axiom
  | Less_Axiom
  | Range_Axiom
  | BMC1_Axiom
 *)
and tstp_internal_source =
  | TSTP_definition
  | TSTP_assumption
  | TSTP_arg_filter_axiom
  | TSTP_def_merge_axiom
  | TSTP_def_merge_nf_impl
  | TSTP_prop_impl_unit
  | TSTP_tmp

and tstp_theory_bmc1 =
  | TSTP_bmc1_path_axiom of int
  | TSTP_bmc1_reachable_state_axiom of int
  | TSTP_bmc1_reachable_state_conj_axiom of int
  | TSTP_bmc1_reachable_state_on_bound_axiom of int
(*	| TSTP_bmc1_reachable_sk_replacement of int * clause *) (* replacing c(sK) by c($constBN) where sK occured in $reachable(sK)*)
  | TSTP_bmc1_only_bound_reachable_state_axiom of int
  | TSTP_bmc1_clock_axiom of int * Symbol.symbol * (int list)

(*	| TSTP_bmc1_instantiated_clause of int * clause *)

and tstp_theory =
  | TSTP_equality
  | TSTP_distinct
  | TSTP_irref
  | TSTP_domain
  | TSTP_bmc1 of tstp_theory_bmc1
  | TSTP_less
  | TSTP_range
  | TSTP_bv_succ  (* succesor axiom on bit-vectors of size i+1 *)
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
  | TSTP_file_source of string * string
  | TSTP_theory of tstp_theory
	
(* if clause is not at a leaf of an inference it should be obtained by an inference rule *)
(* important for clause_protect; get_parents; etc. *)
and tstp_inference_rule =
  | Instantiation of clause list (* side clauses *)
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
  | Dis_eq_elim (* elim of pure disequalities *)
  | Def_merge 
  | Copy
  | Renaming
  | TSTP_bmc1_instantiated_clause of int 
  | TSTP_bmc1_reachable_sk_replacement of int (* replacing c(sK) by c($constBN) where sK occured in $reachable(sK)*)
  | TSTP_bmc1_init_or_property_axiom
  | TSTP_bmc1_merge_next_func 

and tstp_inference_record =
    tstp_inference_rule * clause list

and tstp_source =
  | TSTP_external_source of tstp_external_source
  | TSTP_internal_source of tstp_internal_source
  | TSTP_inference_record of tstp_inference_record

(*--------------Consing hash tables--------------------------*)


(* non-Weak basic clause hash table *)

module BClause_Node_Key =
  struct
    type t = lits
    let equal lits1 lits2 =
      try
	List.for_all2 (==) lits1 lits2
      with
	Invalid_argument _ -> false
    let hash lits = hash_list Term.hash lits
	(* alternative equal *)
	(*	let compare =
	  list_compare_lex Term.compare cl1.literals cl2.literals
	  let equal c1 c2 =
	  if (compare c1 c2) =0
	  then true
	  else false
	 *)	
  end

module BC_Htbl = Hashtbl.Make(BClause_Node_Key) 
    
let bc_clause_db = BC_Htbl.create 50821 (* medium large prime number *)

(* Weak basic clause hash table *)

let bc_get_lits bc = bc.lits 

module BClause_Weak_Key =
  struct
    type t = basic_clause 
    let equal  bc1 bc2 =
      try
	List.for_all2 (==) (bc_get_lits bc1) (bc_get_lits bc2)
      with
	Invalid_argument _ -> false
    let hash bc = hash_list Term.hash (bc_get_lits bc)
	(* alternative equal *)
	(*	let compare =
	  list_compare_lex Term.compare cl1.literals cl2.literals
	  let equal c1 c2 =
	  if (compare c1 c2) =0
	  then true
	  else false
	 *)
  end


module BC_WHtbl = Weak.Make(BClause_Weak_Key)

let bc_clause_db_weak = BC_WHtbl.create 50821 (* medium large prime number *)

(* basic clause hash table *)
(* Key for consing table *)

(*---------------------------------------------*)
(* clause db which contains all basic clauses *)
(*
  let basic_clause_db = BClause_Htbl.create 50821  (* a midium size prime *)
  let add_bc_node bc_node = BClause_Htbl.hashcons basic_clause_db bc_node
 *)

(*-----------------------------------------*)

(*-----------------------------------------*)
let get_bclause c =
  c.basic_clause

let get_bc = get_bclause (* shorthand *)

type bound_clause = clause Lib.bind

type bound_bclause = basic_clause Lib.bind

(* fast_key is unique for each generated clause  *)
let get_fast_key c = c.fast_key

(* lits_fast_key is the basic_clause rather than basic_clause.tag since if we use tag basic clause may be removed *)
(* by weak table since no refernce will be held *)
(*  unique for each literal list *)

let bc_get_fast_key bc = bc.bc_fast_key
let bc_compare bc1 bc2 = Pervasives.compare (bc_get_fast_key bc1) (bc_get_fast_key bc2)

let get_lits_fast_key c = c.basic_clause
let get_lits_hash c = c.basic_clause
let compare_bc c1 c2 = bc_compare (get_bc c1) (get_bc c2)
let equal_bc c1 c2 = c1.basic_clause == c2.basic_clause


(* let get_context_id c = c.context_id *)

(*-----------------------------------------*)
(*
  let compare_basic_clause c1 c2 =
  Pervasives.compare c1.tag c2.tag
 *)

(* let equal_basic_clause = (==)*) 

(*
  let compare_clause c1 c2 =
  pair_compare_lex
  Pervasives.compare
  Pervasives.compare
  ((get_fast_key c1), (get_context_id c1))
  ((get_fast_key c2), (get_context_id c2))
 *)

let compare_clause c1 c2 =
  Pervasives.compare (get_fast_key c1) (get_fast_key c2)

let equal_clause = (==)

let equal = equal_clause

let compare = compare_clause

(*
  let compare_lits c1 c2 = compare_basic_clause (get_bc c1) (get_bc c2)

  let equal_lits c1 c2 = equal_basic_clause (get_bc c1) (get_bc c2)
 *)

(*---------- filling Bool params of a basic clause ----------------------------*)

(*--------from term params to lits param-------------------------*)

let exists_lit_with_true_bool_param term_bool_param lits =
  List.exists (Term.get_fun_bool_param term_bool_param) lits

let has_conj_symb_lits lits =
  exists_lit_with_true_bool_param Term.has_conj_symb lits

let has_non_prolific_conj_symb_lits lits =
  exists_lit_with_true_bool_param Term.has_non_prolific_conj_symb lits

(*----------------------------------*)
let length_lits lits = List.length lits

let num_of_symb_lits lits =
  let f rest term = rest + (Term.get_num_of_symb term) in
  List.fold_left f 0 lits

let num_of_var_lits lits =
  let f rest term = rest + (Term.get_num_of_var term) in
  List.fold_left f 0 lits

let max_atom_input_occur_lits lits =
  let get_symb lit =
    let atom = Term.get_atom lit in
    match atom with
    | Term.Fun(symb, _, _) -> symb
    | _ -> failwith "assign_max_atom_input_occur should not be var"
  in
  let cmp lit1 lit2 =
    let symb1 = get_symb lit1 in
    let symb2 = get_symb lit2 in
    Pervasives.compare
      (Symbol.get_num_input_occur symb1) (Symbol.get_num_input_occur symb2) in
  let max_atom_input_occur = get_symb (list_find_max_element cmp lits) in
  max_atom_input_occur
    
(* defined depth -> circuit_depth *)
let min_defined_symb_lits lits =
  let cmp_lit l1 l2 =
    let d1 = Symbol.get_defined_depth (Term.lit_get_top_symb l1) in
    let d2 = Symbol.get_defined_depth (Term.lit_get_top_symb l2) in
    match (d1, d2) with
    | (Def(i1), Def(i2)) -> Pervasives.compare i1 i2
	  
	  (* changed to the opposite since spliting symbols by vapi become big!
	     (* Undef is greater then Def *)
	     | (Undef, Def _) -> 1
	     | (Def _, Undef) -> -1
	   *)
    | (Undef, Def _) -> -1
    | (Def _, Undef) -> 1
    | (Undef, Undef) -> 0
  in
  let min_lit = list_find_min_element cmp_lit lits in
  let min_d = Symbol.get_defined_depth (Term.lit_get_top_symb min_lit) in
  min_d

(*--------------------------------------------------------------*)

(* function to fill the clause parameters in one pass *)
let fill_in_bc_params lits =
  (* bit-vec that accumilates flags *)
  let bv = ref Bit_vec.false_vec in
  (* number of positive lits *)
  let num_pos = ref 0 in
  (* evaluate literal wrt the required properties *)
  let eval_lit lit =
    (* check whether the lit is positive *)
    if Term.is_pos_lit lit
    then
      num_pos := succ !num_pos;
    (* check the next state predicate *)
    if Term.is_next_state_lit lit
    then
      bv := Bit_vec.set true bc_has_next_state !bv;
    (* check for the reachable state predicate *)
    if Term.is_reachable_state_lit lit
    then
      bv := Bit_vec.set true bc_has_reachable_state !bv;
    (* check for eq literal *)
    if Term.is_eq_lit lit
    then
      bv := Bit_vec.set true bc_has_eq_lit !bv;
    (* check for groundness of literal *)
    if not (Term.is_ground lit)
    then
      bv := Bit_vec.set true bc_non_ground !bv;
    (* check for EPR of literal *)
    if not (Term.is_epr_lit lit)
    then
      bv := Bit_vec.set true bc_non_epr !bv;
    (*--------from term params to lits param-------------------------*)
    (* check for conj symbols *)
    if Term.get_fun_bool_param Term.has_conj_symb lit
    then
      bv := Bit_vec.set true bc_has_conj_symb !bv;
    (* check for non-prolific conj symbols *)
    if Term.get_fun_bool_param Term.has_non_prolific_conj_symb lit
    then
      bv := Bit_vec.set true bc_has_non_prolific_conj_symb !bv;
    (* check for bound constant symbols *)
    if Term.get_fun_bool_param Term.has_bound_constant lit
    then
      bv := Bit_vec.set true bc_has_bound_constant !bv;
  in
  (* evaluate all literals *)
  List.iter eval_lit lits;
  (* set the hornness of a clause *)
  bv := Bit_vec.set (!num_pos <= 1) bc_horn !bv;
  (* return the final bit_vec *)
  !bv

(* can be dangerous since options are redefined after schedules take place; but clauses added during parsing*)
(* can make definite exclusion list when we do not use cicuit topology
   let defined_symb_enabled_check () =
   !current_options.bmc1_incremental || !current_options.schedule = Options.verification_epr
 *)

(* us to check whether the clause is in the *)
let bc_template ~bc_fast_key lits =
  {
   lits = lits;
   bc_fast_key = bc_fast_key;
   bc_counter = 1;
   bc_bool_param = Bit_vec.false_vec;
   length = 0;
   num_of_symb = 0; 	(* number of all symbols in literals *)
   num_of_var = 0;
   max_atom_input_occur = Undef; 	(* minial defined symbols *)
   min_defined_symb = Undef;
(*   prop_solver_id = None; *)
   bc_imp_inh = Options.bc_imp_inh_default_val;

 }

(* auto fill non bit-vector params should be added here *)
let fill_bc_auto_params bc_node =
  let auto_bool_param = fill_in_bc_params bc_node.lits in
  let lits = bc_node.lits in
  bc_node.bc_bool_param <- auto_bool_param;
  bc_node.length <- length_lits lits;
  bc_node.num_of_symb <- num_of_symb_lits lits;
  bc_node.num_of_var <- num_of_var_lits lits;
  bc_node.max_atom_input_occur <- Def(max_atom_input_occur_lits lits);
  bc_node.min_defined_symb <- min_defined_symb_lits lits

(* Non Weak Hashtbl *)

let create_basic_clause_non_weak lits =
  try
    let bc = BC_Htbl.find bc_clause_db lits in
    bc.bc_counter <- bc.bc_counter + 1;
    bc
  with
    Not_found ->
      (
       let bc = bc_template ~bc_fast_key: (!bc_global_counter) lits in
       bc_global_counter := !bc_global_counter + 1;
       (if (not (lits = []))
       then
	 (fill_bc_auto_params bc;));
       BC_Htbl.add bc_clause_db lits bc;
       bc
      )

(* Weak Hashtbl *)
let create_basic_clause_weak lits =
  let bc_template = bc_template ~bc_fast_key: (!bc_global_counter) lits in
  try
    let bc = BC_WHtbl.find bc_clause_db_weak bc_template in
    bc.bc_counter <- bc.bc_counter + 1;
    bc
  with
    Not_found ->
      (
       (*	let bc = bc_template ~bc_fast_key: (!bc_global_counter) lits in *)
       bc_global_counter := !bc_global_counter + 1;
       (if (not (lits = []))
       then
	 (fill_bc_auto_params bc_template;));
       BC_WHtbl.add bc_clause_db_weak bc_template;
       bc_template
      )

let incr_gc_bc_elim _c = 
  incr_int_stat 1 gc_basic_clause_elim
    
(*------weak/non-weak should be choosen only once------------------*)
(* i.e.!current_options.clauses_weak_htbl should not change during execution *)	

let create_basic_clause lits = 
  if !current_options.clause_weak_htbl 
  then 
    let new_clause = 
      create_basic_clause_weak lits
    in 
    if !current_options.gc_record_bc_elim 
    then 
      (Gc.finalise incr_gc_bc_elim new_clause;
       new_clause)
    else 
      new_clause
  else
    create_basic_clause_non_weak lits
      
(*
  let added_bc = add_bc_node template in
  let new_bc =
  (if (added_bc.node == template_bc_node) (* there was no copy in clause cons *)
  then
  (
  fill_bc_auto_params added_bc.node;
  added_bc
  )
  else (* there was a bc clause with these lits; so we just return it*)
  added_bc
  )
  in
  new_bc
 *)

(*
  let is_negated_conjecture clause =
  clause.conjecture_distance = conjecture_int
 *)

(*---------------end basic clause-----------------------*)

(*------------------*)

let get_lits c = c.basic_clause.lits
let get_literals = get_lits

(* returns set of literals *)
let get_lits_clause_list clause_list =   
  let g lit_set c = 
    let lits = get_lits c in 
    List.fold_left (fun curr_set lit -> TSet.add lit curr_set) lit_set lits 
  in
  List.fold_left g TSet.empty clause_list

let get_atoms_clause_list clause_list = 
  let lits = get_lits_clause_list clause_list in
  TSet.map Term.get_atom lits

(*
  let compare_lits c1 c2 =
  bc_get_fast_key bc_fast_key
  list_compare_lex Term.compare (get_lits c1) (get_lits c2)
 *)

exception Empty_clause of clause 

let is_empty_clause c =
  if (get_lits c) = [] then true
  else false

(*------------output: to stream/string to_tptp is later due to dependences on getting parameters------------*)

let to_stream s clause =
  s.stream_add_char '{';
  (list_to_stream s Term.to_stream (get_lits clause) ";");
  s.stream_add_char '}'

let out = to_stream stdout_stream

let to_string =
  to_string_fun_from_to_stream_fun 100 to_stream

let clause_list_to_stream s c_list =
  list_to_stream s to_stream c_list "\n"

let out_clause_list = clause_list_to_stream stdout_stream

let clause_list_to_string =
  to_string_fun_from_to_stream_fun 300 clause_list_to_stream


(*-------------------------------*)

(*
  let assign_tstp_source tstp_source c =
  c.node.tstp_source <- tstp_source

  let get_tstp_source c =	c.node.tstp_source

 *)

(*-----------------------------------------*)
(*
  let axiom_to_string axiom =
  match axiom with
  | Eq_Axiom -> "Equality Axiom"
  | Distinct_Axiom -> "Distinct Axiom"
  | Less_Axiom -> "Less Axiom"
  | Range_Axiom -> "Range Axiom"
  | BMC1_Axiom -> "BMC1 Axiom"
 *)
(*
  let pp_axiom ppf = function
  | Eq_Axiom -> Format.fprintf ppf "Equality Axiom"
  | Distinct_Axiom -> Format.fprintf ppf "Distinct Axiom"
  | Less_Axiom -> Format.fprintf ppf "Less Axiom"
  | Range_Axiom -> Format.fprintf ppf "Range Axiom"
  | BMC1_Axiom -> Format.fprintf ppf "BMC1 Axiom"
 *)

(*----------------------------*)
(*let get_node c = c.node*)

let get_bc c = c.basic_clause

let get_bc_node c = c.basic_clause

let equal_bc c1 c2 = (get_bc c1) == (get_bc c2)

(*
  let compare_in_context c1 c2 = Pervasives.compare c1.tag c2.tag

  let compare_globally c1 c2 =
  pair_compare_lex
  Pervasives.compare
  Pervasives.compare
  (c1.tag, c1.node.context_id)
  (c2.tag, c2.node.context_id)

  let compare = compare_globally

(* clauses with the same literals but in different contexts are not equal*)
  let equal = (==)

(* clauses with the same literals are equal_bc *)
  let equal_bc c1 c2 = (get_bc c1) == (get_bc c2)
 *)

(*--------------------*)
let memq lit clause = List.memq lit (get_lits clause)
let exists p clause = List.exists p (get_lits clause)
let find p clause = List.find p (get_lits clause)
let fold f a clause = List.fold_left f a (get_lits clause)
let find_all f clause = List.find_all f (get_lits clause)
let partition f clause = List.partition f (get_lits clause)
let iter f clause = List.iter f (get_lits clause)

(*----------------------------------------------------*)

(*---------------------------------------------------------*)
let bc_set_bool_param value param clause =
  let bc = get_bc_node clause in
  bc.bc_bool_param <- Bit_vec.set value param bc.bc_bool_param

let bc_get_bool_param param clause =
  Bit_vec.get param (get_bc_node clause).bc_bool_param

let reset_has_non_prolific_conj_symb clause =
  bc_set_bool_param (has_non_prolific_conj_symb_lits (get_lits clause)) bc_has_non_prolific_conj_symb clause

let reset_has_conj_symb clause =
  bc_set_bool_param (has_conj_symb_lits (get_lits clause)) bc_has_conj_symb clause


(*--------clause bc params get/assign -------------*)

let is_negated_conjecture c =
  c.conjecture_distance = 0
(*  bc_get_bool_param bc_is_negated_conjecture c *)

let is_ground c =
  not (bc_get_bool_param bc_non_ground c)

let is_horn c =
  bc_get_bool_param bc_horn c

let is_epr c =
  not (bc_get_bool_param bc_non_epr c)

let is_eq_axiom c =
  bc_get_bool_param bc_eq_axiom c

let assign_is_eq_axiom value c = (* user *) (* assign only for user parameters *)
  bc_set_bool_param value bc_eq_axiom c

let has_eq_lit c =
  bc_get_bool_param bc_has_eq_lit c

let has_eq_lit_clause_list c_list = List.exists has_eq_lit c_list

let has_conj_symb c =
  bc_get_bool_param bc_has_conj_symb c

let has_non_prolific_conj_symb c =
  bc_get_bool_param bc_has_non_prolific_conj_symb c

let has_bound_constant c =
  bc_get_bool_param bc_has_bound_constant c

let has_next_state c =
  bc_get_bool_param bc_has_next_state c

let has_reachable_state c =
  bc_get_bool_param bc_has_reachable_state c

let num_of_symb c =
  let bc_node = get_bc_node c in
  bc_node.num_of_symb

let num_of_var c =
  let bc_node = get_bc_node c in
  bc_node.num_of_var

let length c =
  let bc_node = get_bc_node c in
  bc_node.length

(* int param *)
let get_max_atom_input_occur c =
  let bc_node = get_bc_node c in
  bc_node.max_atom_input_occur

(* symb param*)
let get_min_defined_symb c =
  let bc_node = get_bc_node c in
  bc_node.min_defined_symb

let get_bc_imp_inh c = 
  (get_bc c).bc_imp_inh

let assign_bc_imp_inh c i = 
  (get_bc c).bc_imp_inh <- i 

(*------clause params get/assign------*)

(*
let assign_tstp_source c tstp_source =
  match c.tstp_source with
  | Def _ -> raise (Failure "Clause source already assigned")
  | Undef -> c.tstp_source <- Def(tstp_source)
*)

let get_tstp_source c =
  match c.tstp_source with
  | Def (tstp_source) -> tstp_source
  | Undef -> failwith ("tstp_source is not defined for clause: "^(to_string c))

(*let get_context_id c = c.node.context_id*)

(*
  let assign_context_id id c =
  c.context_id <- id
 *)


let get_conjecture_distance c =
  c.conjecture_distance

let assign_conjecture_distance d c =
  c.conjecture_distance <- d

(*
let inherit_conj_dist from_c to_c =
  to_c.conjecture_distance <- from_c.conjecture_distance
*)

let inherit_conjecture from_c to_c = 
(*  bc_set_bool_param (bc_get_bool_param bc_is_negated_conjecture from_c) bc_is_negated_conjecture to_c; *) 
  to_c.conjecture_distance <- (pair_get_min from_c.conjecture_distance to_c.conjecture_distance)
  


(*
let in_prop_solver c =
  ccp_get_bool_param cpp_in_prop_solver c
*)
(*

let assign_in_prop_solver b c =
  ccp_set_bool_param b cpp_in_prop_solver c
*)

(*
let is_solver_protected c = 
  ccp_get_bool_param ccp_solver_protected c

let assign_solver_protected b c = 
  ccp_set_bool_param b ccp_solver_protected c
*)

(*-------------------------------*)

let get_main_parents_tstp tstp_source = 
  match tstp_source with
  | TSTP_inference_record
      (_tstp_inference_rule, main_parents) ->
	main_parents
  |_->[]

let get_main_parents clause = 
  get_main_parents_tstp (get_tstp_source clause)

let get_parents_tstp tstp_source =
  match tstp_source with
  | TSTP_inference_record
      (tstp_inference_rule, main_parents) ->
	let side_parents =
	  begin
	    match tstp_inference_rule with
	    | Instantiation side_parents -> side_parents
	    | Resolution _ -> []
	    | Resolution_lifted _ -> []
	    | Factoring _ -> []
	    | Global_subsumption _ -> []
	    | Forward_subsumption_resolution -> []
	    | Backward_subsumption_resolution -> []
	    | Splitting _ ->[]
	    | Grounding _ -> []
	    | Non_eq_to_eq -> []
            | Dom_res -> []
	    | Lifting -> []
	    | Subtyping ->[]
	    | Flattening ->[]
	    | Unflattening -> []
            | Arg_filter_abstr -> []
	    | True_false -> []
	    | Eq_res_simp -> []
	    | Dis_eq_elim -> []
            | Def_merge -> []
            | Copy -> []
            | Renaming -> []
	    | TSTP_bmc1_instantiated_clause _ -> [] 
	    | TSTP_bmc1_reachable_sk_replacement _ -> []
	    | TSTP_bmc1_init_or_property_axiom -> []
	    | TSTP_bmc1_merge_next_func -> []

	  end
	in main_parents@side_parents
  | _ ->	[] (* other tstp_sources*)

let get_parents clause = 
  get_parents_tstp (get_tstp_source clause)

(*
exception Clause_prop_solver_id_is_def
exception Clause_prop_solver_id_is_undef


let rec protect_solver_clist clist = 
  match clist with 
  |c::tl ->
      (
       if (not (is_solver_protected c)) 
       then 
	 (assign_solver_protected true c;
	  let main_parents = get_main_parents (get_tstp_source c) in
	  let to_protect =  (main_parents@tl) in
	  protect_solver_clist to_protect
	 )
       else 
	 (protect_solver_clist tl)
      )
  | [] -> ()
	
let protect_solver clause = 
  protect_solver_clist [clause]
    
let assign_prop_solver_id c id =
  let bc = c.basic_clause in
(*  dbg D_prop_solver ((Clause.to_tptp c)^(" ")^(string_of_int id)); *)
  match bc.prop_solver_id with
  | None -> 
      (bc.prop_solver_id <- Some (id);
       protect_solver c
      )
  | Some id_old -> assert (id_old = id) (* raise Clause_prop_solver_id_is_def *)

let get_prop_solver_id clause = 
  let bc = clause.basic_clause in
  bc.prop_solver_id
*)

(*-----proof search params-------*)
(*--------------------------------*)

(*
let create_ps_param () =
  {
   ps_bool_param = Bit_vec.false_vec;
   ps_when_born = Undef;
   
   (* inst params *)
   inst_sel_lit = Undef;
   inst_dismatching = Undef;
   inst_activity = 0;
   inst_children = [];
   
   
   (* res params *)
   res_sel_lits = Undef;
 }
*)
(*----------------*)
(*
let get_proof_search_param c = 
  get_param_val c.proof_search_param

let get_ps_param = get_proof_search_param

let clear_proof_search_param c = c.proof_search_param <- Def(create_ps_param ())

let get_ps_bv_param c =
  let ps_param = get_ps_param c in
  ps_param.ps_bool_param

let get_ps_bool_param param c =
  let bv = get_ps_bv_param c in
  Bit_vec.get param bv

let set_ps_bool_param value param c =
  let ps_param = get_ps_param c in
  ps_param.ps_bool_param <- Bit_vec.set value param ps_param.ps_bool_param

(*---res non-boolean param--*)
let get_ps_when_born c =
  let ps_param = get_ps_param c in
  match ps_param.ps_when_born with
  | Def(n) -> n
  | Undef ->
      (
       let fail_str = "Clause: ps_when_born is undef for "^(to_string c) in
       failwith fail_str
      )
let assign_ps_when_born i c =
  let ps_param = get_ps_param c in
  ps_param.ps_when_born <- Def(i)

let res_assign_sel_lits sel_lits clause =
  let ps_param = get_ps_param clause in
  ps_param.res_sel_lits <- Def(sel_lits)

let res_sel_is_def clause =
  let ps_param = get_ps_param clause in
  match ps_param.res_sel_lits with
  | Def(_) -> true
  | Undef -> false

exception Res_sel_lits_undef
let get_res_sel_lits clause =
  let ps_param = get_ps_param clause in
  match ps_param.res_sel_lits with
  | Def(sel_lits) -> sel_lits
  | Undef -> raise Res_sel_lits_undef

let get_ps_in_active c = get_ps_bool_param ps_in_active c
let set_ps_in_active v c = set_ps_bool_param v ps_in_active c

let get_ps_in_subset_subsumption_index c = get_ps_bool_param ps_in_subset_subsumption_index c
let set_ps_in_subset_subsumption_index v c = set_ps_bool_param v ps_in_subset_subsumption_index c

let get_ps_in_subsumption_index c = get_ps_bool_param ps_in_subsumption_index c
let set_ps_in_subsumption_index v c = set_ps_bool_param v ps_in_subsumption_index c

let get_ps_in_passive_queue c = get_ps_bool_param ps_in_passive_queue c
let set_ps_in_passive_queue v c = set_ps_bool_param v ps_in_passive_queue c

let get_ps_sel_max c = get_ps_bool_param ps_sel_max c
let set_ps_sel_max v c = set_ps_bool_param v ps_sel_max c

let get_ps_simplifying c = get_ps_bool_param ps_simplifying c
let set_ps_simplifying v c = set_ps_bool_param v ps_simplifying c
*)


let assign_ps_when_born i c =
  c.when_born <- Def(i)

let get_ps_when_born c =
  match c.when_born with
  | Def(n) -> n
  | Undef ->
      (
       let fail_str = "Clause: when_born is undef for "^(to_string c) in
       failwith fail_str
      )


(*
  let get_ c = ps_get_bool_param c
  let set_ v c = ps_set_bool_param v c
 *)

(*

  let get_ c = inst_get_bool_param c
  let set_ v c = inst_set_bool_param v c

  let inst_in_active = 1
  let inst_in_unif_index = 2
  let inst_in_subset_subsumption_index = 3
  let inst_in_subsumption_index = 4
(* let inst_in_prop_solver = 5 *)
  let inst_in_sim_passive = 6

  let inst_pass_queue1 = 7
  let inst_pass_queue2 = 8
  let inst_pass_queue3 = 9
 *)

(*
  let get_inst_in_active c = inst_get_bool_param inst_in_active c
  let set_inst_in_active v c = inst_set_bool_param v inst_in_active c

  let get_inst_in_unif_index c = inst_get_bool_param inst_in_unif_index c
  let set_inst_in_unif_index v c = inst_set_bool_param v inst_in_unif_index c

  let get_inst_in_subset_subsumption_index c = inst_get_bool_param inst_in_subset_subsumption_index c
  let set_inst_in_subset_subsumption_index v c = inst_set_bool_param v inst_in_subset_subsumption_index c

  let get_inst_in_subsumption_index c = inst_get_bool_param inst_in_subsumption_index c
  let set_inst_in_subsumption_index v c = inst_set_bool_param v inst_in_subsumption_index c

  let get_inst_in_sim_passive c = inst_get_bool_param inst_in_sim_passive c
  let set_inst_in_sim_passive v c = inst_set_bool_param v inst_in_sim_passive c

  let get_inst_pass_queue1 c = inst_get_bool_param inst_pass_queue1 c
  let set_inst_pass_queue1 v c = inst_set_bool_param v inst_pass_queue1 c

  let get_inst_pass_queue2 c = inst_get_bool_param inst_pass_queue2 c
  let set_inst_pass_queue2 v c = inst_set_bool_param v inst_pass_queue2 c

  let get_ c = inst_get_bool_param c
  let set_ v c = inst_set_bool_param v c

  let get_inst_pass_queue3 c = inst_get_bool_param inst_pass_queue3 c
  let set_inst_pass_queue3 v c = inst_set_bool_param v inst_pass_queue3 c
 *)

(*----inst non-boolean params -----------*)
(*
exception Sel_lit_not_in_cluase
let rec inst_find_sel_place sel_lit lit_list =
  match lit_list with
  | h:: tl ->
      if (h == sel_lit) then 0
      else 1 + (inst_find_sel_place sel_lit tl)
  |[] -> raise Sel_lit_not_in_cluase

let inst_assign_sel_lit sel_lit clause =
  let sel_place = inst_find_sel_place sel_lit (get_lits clause) in
  let ps_param = get_ps_param clause in
  (* Format.eprintf
     "Selecting literal %s in clause (%d) %s@."
     (Term.to_string sel_lit)
     (match clause.fast_key with
     | Def key -> key
     | Undef -> -1)
     (to_string clause); *)
  ps_param.inst_sel_lit <- Def((sel_lit, sel_place))

let inst_assign_dismatching dismatching clause =
  let ps_param = get_ps_param clause in
  ps_param.inst_dismatching <- Def(dismatching)

exception Inst_sel_lit_undef
let inst_get_sel_lit clause =
  let ps_param = get_ps_param clause in
  match ps_param.inst_sel_lit with
  | Def((sel_lit, _)) -> sel_lit
  | Undef -> raise Inst_sel_lit_undef

(* should be changed dependeing on the tstp_source
   exception Parent_undef
   let get_parent clause =
   clause.parent
 *)

(* match clause.parent with
   | Def(p) -> p
   | Undef -> raise Parent_undef *)

let inst_compare_sel_place c1 c2 =
  let c1_ps_param = get_ps_param c1 in
  let c2_ps_param = get_ps_param c2 in
  match (c1_ps_param.inst_sel_lit, c2_ps_param.inst_sel_lit) with
  | (Def((_, sp1)), Def((_, sp2)))
    -> Pervasives.compare sp1 sp2
  | _ -> raise Inst_sel_lit_undef

exception Dismatching_undef
let get_inst_dismatching clause =
  let ps_param = get_ps_param clause in
  match ps_param.inst_dismatching with
  | Def(dismatching) -> dismatching
  | Undef -> raise Dismatching_undef

let add_inst_child clause ~child =
  let ps_param = get_ps_param clause in
  ps_param.inst_children <- child:: (ps_param.inst_children)

let get_inst_children clause =
  let ps_param = get_ps_param clause in
  ps_param.inst_children

let inst_get_activity clause =
  let ps_param = get_ps_param clause in
  ps_param.inst_activity

let inst_assign_activity act clause =
  let ps_param = get_ps_param clause in
  ps_param.inst_activity <- act

*)
(*-------inst/res when born assignments--*)

(* assigns when the clause born based on when the clauses in the premise where born *)
(*                                    *)
(* if the the prem1 and prem2 is [] then zero is assined (e.g. imput clauses) *)
(* we assign when_born when 1) conclusion of an inference was generated       *)
(* 2) clause is replaced and 3) splitting 4)model transformation/equation axiom  *)
(* 5) it is an imput clause                                                   *)
(* in the case 1) we calculate when born of the conclusion as  *)
(* when_born=max(min(pem1),min(prem2)) + 1                     *)
(* case 4),5) we use assign_when_born prem1 [] [] clause       *)
(* is case 2),3) we use inherit  inherit_param_modif           *)

(* aux: if list is empty then 0 else max element*)

let list_find_max_element_zero comp l =
  try
    list_find_max_element comp l
  with Not_found -> 0

let when_born_concl prem1 prem2 clause =
  let born_list1 = List.map get_ps_when_born prem1 in
  let born_list2 = List.map get_ps_when_born prem2 in
  let inv_compare = compose_sign false Pervasives.compare in
  (* finds min element *)
  let min_prem1 = list_find_max_element_zero inv_compare born_list1 in
  let min_prem2 = list_find_max_element_zero inv_compare born_list2 in
  let max_born = list_find_max_element Pervasives.compare [min_prem1; min_prem2] in
  let when_cl_born = max_born + 1 in
  when_cl_born

let assign_ps_when_born_concl ~prem1 ~prem2 ~c =
  c.when_born <- Def(when_born_concl prem1 prem2 c)


(*--------------pp printing ------------------------------------*)
(* Print the name of a clause

   Clauses are named [c_n], where [n] is the identifier (fast_key) of
   the clause. If the identifier is undefined, the clause is named
   [c_tmp].
 *)
let clause_get_name clause = 
  "c_"^(string_of_int (get_fast_key clause))

let pp_clause_name ppf clause =
  (*	Format.fprintf ppf "c_%d" (*(get_context_id clause)*) (get_fast_key clause)*)
  Format.fprintf ppf "%s" (clause_get_name clause)

let pp_clause_with_id ppf clause =
  Format.fprintf
    ppf
    "(%d) {%a}"
    (*(get_context_id clause)*)
    (get_fast_key clause)
    (pp_any_list Term.pp_term ";") (get_lits clause)

let pp_clause ppf clause =
  Format.fprintf
    ppf
    "@[<h>{%a}@]"
    (pp_any_list Term.pp_term ";") (get_lits clause)

let pp_clause_min_depth ppf clause =
  pp_clause ppf clause;
  let s = clause.basic_clause.min_defined_symb in
  (* let d = Symbol.get_defined_depth
     (Term.lit_get_top_symb s) in
   *)
  (*  out_str *)
  Format.fprintf
    ppf "@[<h> depth: %s @]" (param_to_string string_of_int s)

let rec pp_literals_tptp ppf = function
    
  | [] -> ()
	
  | [l] -> Format.fprintf ppf "@[<h>%a@]" Term.pp_term_tptp l
	
  | l :: tl ->
      pp_literals_tptp ppf [l];
      Format.fprintf ppf "@ | ";
      pp_literals_tptp ppf tl

(* Output clause in TPTP format *)
let pp_clause_literals_tptp ppf clause =
  
  (* Print empty clause *)
  if (is_empty_clause clause)
  then
    Format.fprintf ppf "@[<h>( %a )@]" Symbol.pp_symbol Symbol.symb_false
  else
    (* Print non-empty clause as disjunction of literals *)
    Format.fprintf
      ppf
      "@[<hv>( %a )@]"
      pp_literals_tptp
      (get_lits clause)

(* Output clause in TPTP format *)
let pp_clause_tptp ppf clause =
  Format.fprintf
    ppf
    "@[<hov>cnf(c_%d,%s,@,@[<hov>(%a)@]).@]"
    (* (get_context_id clause) *) (get_fast_key clause)
    (if (is_negated_conjecture clause)
    then "negated_conjecture"
    else "plain")
    (pp_any_list Term.pp_term_tptp " | ") (get_lits clause)

(* Output list of clauses in TPTP format, skipping equality axioms *)
let rec pp_clause_list_tptp ppf = function
    
  | [] -> ()
	
	(* Skip equality axioms *)
	(*  | { history = Def (Axiom Eq_Axiom) } :: tl ->      *)
  | c:: tl when
      (get_tstp_source c) = TSTP_external_source (TSTP_theory TSTP_equality) ->
	pp_clause_list_tptp ppf tl
	  
	  (* Clause at last position in list *)
  | [c] -> pp_clause_tptp ppf c
	
	(* Clause at middle position in list *)
  | c :: tl ->
      pp_clause_tptp ppf c;
      Format.pp_print_newline ppf ();
      pp_clause_list_tptp ppf tl


(*----tptp output without pp-----*)
let tptp_to_stream s clause =
  begin
    s.stream_add_str "cnf(";
    s.stream_add_str ("id_"^(string_of_int (get_fast_key clause)));
    s.stream_add_char ',';
    (if (is_negated_conjecture clause)
    then
      s.stream_add_str "negated_conjecture"
    else
      s.stream_add_str "plain"
    );
    s.stream_add_char ',';
    s.stream_add_char '(';
    list_to_stream s Term.to_stream_tptp (get_lits clause) "|";
    s.stream_add_str "))."
  end


let out_tptp = tptp_to_stream stdout_stream

let to_tptp =
  to_string_fun_from_to_stream_fun 30 tptp_to_stream


let clause_list_tptp_to_stream s c_list =
  list_to_stream s tptp_to_stream c_list "\n"

let out_clause_list_tptp = clause_list_tptp_to_stream stdout_stream

let clause_list_to_tptp =
  to_string_fun_from_to_stream_fun 300 clause_list_tptp_to_stream




(*----------*)
let rec add_var_set vset cl =
  List.fold_left Term.add_var_set vset (get_lits cl)

let get_var_set cl = 
  add_var_set (VSet.empty) cl

let get_var_list cl =
  let vset = get_var_set cl in
  VSet.elements vset

(*
  let inherit_history from_c to_c =
  to_c.history <- from_c.history
 *)

(*--------------------------------------*)


let fold_sym f a clause =
  List.fold_left (Term.fold_sym f) a (get_lits clause)

let iter_sym f clause =
  List.iter (Term.iter_sym f) (get_lits clause)

let fold_pred f a clause = 
  let f_lit x l = 
    f x (not (Term.is_neg_lit l)) (Term.lit_get_top_symb l)
  in
  List.fold_left f_lit a (get_lits clause)

let iter_pred f clause = 
  let f_lit l = 
    f (not (Term.is_neg_lit l)) (Term.lit_get_top_symb l)
  in
  List.iter f_lit (get_lits clause)



(*-------------------------------------------------------------------------------------------*)
(*------------------------- Normalising binded lit_lists /clauses ---------------------------*)
(*-------------------------------------------------------------------------------------------*)

(* changed from *)
(* apply_bsubst term_db_ref bsubst bclause *)

let apply_bsubst term_db_ref bsubst bound lits =
  let bterm_list = propagate_binding_to_list (bound, lits) in
  let new_lit_list =
    SubstBound.apply_bsubst_btlist term_db_ref bsubst bterm_list in
  new_lit_list

let apply_bsubst_norm_subst term_db_ref bsubst bound lits =
  let bterm_list = propagate_binding_to_list (bound, lits) in
  let (new_term_list, norm_subst) =
    SubstBound.apply_bsubst_btlist_norm_subst
      term_db_ref bsubst bound bterm_list in
  ((new_term_list), norm_subst)

(*
  let apply_bsubst_norm_subst term_db_ref bsubst bound clause =
  let bterm_list = propagate_binding_to_list (bound, clause.literals) in
  let (new_term_list, norm_subst) =
  SubstBound.apply_bsubst_btlist_norm_subst
  term_db_ref bsubst bound bterm_list in
  ((create_parent clause new_term_list), norm_subst)
(*  (create_parent clause new_term_list,norm_subst)*)
 *)

let cmp_arity s1 s2 = 
  try
    Pervasives.compare (Symbol.get_arity s1) (Symbol.get_arity s2) 
  with 
    Symbol.Arity_undef -> 0 

let cmp_symb =  lex_combination [cmp_arity; Symbol.compare]
  

(* term_compare' returns cequal
   if the skeletons of terms the same or raises an exception above *)

let rec term_compare' t s =
  match (t, s) with
  | (Term.Fun(t_sym, t_args, _), Term.Fun(s_sym, s_args, _)) ->
      let cmp = cmp_symb t_sym s_sym in
      if cmp = cequal 
      then
	Term.arg_fold_left2
	  (fun result t' s' -> term_compare' t' s') cequal t_args s_args
      else
	if cmp > cequal 
        then raise Term_compare_greater
	else raise Term_compare_less
  | (Term.Var(_, _), Term.Fun(_, _, _)) -> raise Term_compare_greater
  | (Term.Fun(_, _, _), Term.Var(_, _)) -> raise Term_compare_less
  | (Term.Var(_, _), Term.Var(_, _)) -> cequal

(*term_compare used to normalise clauses for better sharing and all...*)

let term_compare t s =
  try 
    term_compare' t s
  with
  | Term_compare_greater -> cequal +1
  | Term_compare_less -> cequal -1

(*
  let bound_term_compare ((_, t) : bound_term) ((_, s) : bound_term) =
  term_compare t s
 *)

let norm_bterm_wrt_subst bound_t bound_subst =
  match bound_t with
  | (b_t, Term.Var(t_v, _)) ->
      (
       try (SubstBound.find_norm (b_t, t_v) bound_subst)
       with Not_found -> bound_t
      )
  | _ -> bound_t

let cmp_bmc1_atom_fun () = Term.lit_cmp_type_list_to_lex_fun
    [
     (*	Lit_next_state false;*)
     Lit_range true;
     Lit_less true;
     (* Lit_clock true;
	Lit_eq false *)]

let rec bterm_subst_compare' bound_t bound_s bound_subst =
  let norm_bt = norm_bterm_wrt_subst bound_t bound_subst and
      norm_bs = norm_bterm_wrt_subst bound_s bound_subst in
  let (b_t, t) = norm_bt and
      (b_s, s) = norm_bs in
  match (t, s) with
  | (Term.Fun(t_sym, t_args, _), Term.Fun(s_sym, s_args, _)) ->
      let cmp = (cmp_symb t_sym s_sym) in
      dbg D_norm (lazy ("cmp_symb: t_sym:"^(Symbol.to_string t_sym)
                  ^(" s_sym: "^(Symbol.to_string s_sym))
                  ^" cmp: "^(string_of_int cmp)));
      if cmp = cequal 
      then
	Term.arg_fold_left2
	  (fun result t' s' -> bterm_subst_compare' (b_t, t') (b_s, s') bound_subst)
	  cequal t_args s_args
      else
	if cmp > cequal 
        then raise Term_compare_greater
	else raise Term_compare_less
  | _ -> term_compare' t s

let bterm_subst_compare bound_t bound_s bound_subst =
  let b_atom_t = apply_to_bounded Term.get_atom bound_t in
  let b_atom_s = apply_to_bounded Term.get_atom bound_s in
  
  let (bt, atom_t) = b_atom_t in
  let (bs, atom_s) = b_atom_s in
  let pre_comp_fun =
    if (val_of_override !current_options.bmc1_incremental)
    then
      cmp_bmc1_atom_fun ()
    else
      Term.lit_cmp_type_to_fun (Lit_eq(false))
	
  in
  let pre_comp = pre_comp_fun atom_t atom_s in

  let cmp_res = 
    if pre_comp = 0
    then    
      (
       let cmp_b_atoms = 
         try bterm_subst_compare' b_atom_t b_atom_s bound_subst
         with
         | Term_compare_greater -> +1
         | Term_compare_less    -> -1
       in 
       if cmp_b_atoms = 0 
       then (* compare signs *)
         - ( Term.cmp_sign (unbound bound_t) (unbound bound_s)) (* neg larger *)
       else
         cmp_b_atoms
      )      
    else
      pre_comp 
  in
   - cmp_res (* "-" since List.sort below sorts lits in ascending order *)


type var_param = var param

module VarTableM = Var.VHashtbl

let rec normalise_term_var' var_table (max_var_ref : var ref) term =
  match term with
  | Term.Fun(sym, args, _) ->
      let new_args =
	Term.arg_map_left (normalise_term_var' var_table max_var_ref) args in
      Term.create_fun_term_args sym new_args
  | Term.Var(v, _) ->
      try
	let new_v = VarTableM.find var_table v in
	Term.create_var_term new_v
      with
	Not_found ->
	  let old_max_var = !max_var_ref in
	  VarTableM.add var_table v old_max_var;
	  (*  env_ref := (v,old_max_var)::(!env_ref);*)
	  max_var_ref := Var.get_next_var old_max_var;
	  Term.create_var_term old_max_var

let normalise_bterm_list term_db_ref bsubst bterm_list =
  let bterm_compare bt bs = bterm_subst_compare bt bs bsubst in
  let sorted_list = List.sort bterm_compare bterm_list in
  let renaming_env = SubstBound.init_renaming_env () in
  let rename_bterm_var rest bterm =
    (SubstBound.apply_bsubst_bterm' term_db_ref renaming_env bsubst bterm):: rest in
  let rev_new_term_list = List.fold_left rename_bterm_var [] sorted_list in
  (List.rev rev_new_term_list, renaming_env)

(* normilse v1 with reordering for better renaming of vars, *)

(* normalise v2  simply removes duplicate lits  *)
(*
let remove_duplicate_terms term_list = 
  let term_set = TSet.of_list term_list in 
  TSet.elements term_set
*)

(* returns: (norm_lit_list, ren_env) *)
let normalise_b_litlist_v1 term_db_ref bsubst b_litlist =
  let list_blit = propagate_binding_to_list b_litlist in
  normalise_bterm_list term_db_ref bsubst list_blit 
(*  we can not remove duplicates here since it will reshuffle the order *)
(*  let removed_duplicates = Term.remove_duplicate_terms new_lit_list in *)
(* removed_duplicates *)




(* blitlist_list -- list of bound list of literals e.g. [(1,[l1;l2]);(2,[l2])]*)
(* returns: (norm_lit_list, ren_env) *)
let normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list =
  let blit_list_list =
    List.map propagate_binding_to_list blitlist_list in
  let list_blit = List.flatten blit_list_list in
  normalise_bterm_list term_db_ref bsubst list_blit 
(*  we can not remove duplicates here since it will reshuffle the order *)
(*  let removed_duplicates = Term.remove_duplicate_terms new_lit_list in *)
(* removed_duplicates *)



(*
(* complicated version *)
let normalise_bclause_v1 term_db_ref bsubst (b, clause) =
  normalise_b_litlist_v1 term_db_ref bsubst (b, (get_lits clause))

let normalise_bclause_list_v1 term_db_ref bsubst bclause_list =
  let blitlist_list =
    List.map
      (fun (b_c, clause) ->
	(b_c, (get_lits clause))) bclause_list in
  normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list
*)

(* simpler version v2*)
(**)

let normalise_b_litlist_v2' term_db_ref bsubst blit_list =
  let blits = propagate_binding_to_list blit_list in
  Term.remove_duplicate_terms (SubstBound.apply_bsubst_btlist term_db_ref bsubst blits)

let normalise_b_litlist_v2 term_db_ref bsubst blit_list =
  (* create (normalise_b_litlist_v2' term_db_ref bsubst blit_list)*)
  (normalise_b_litlist_v2' term_db_ref bsubst blit_list)

(* blitlist_list -- list of bound list of literals e.g. [(1,[l1;l2]);(2,[l2])]*)
let normalise_blitlist_list_v2 term_db_ref bsubst blitlist_list =
  List.concat
    (List.map
       (fun blit_list -> normalise_b_litlist_v2' term_db_ref bsubst blit_list)
       blitlist_list
    )

(* normilse v1 is with reordering for better renaming of vars, *)
(* normalise v2 is simply removes duplicate lits  *)

let normalise_b_litlist_ren_env = normalise_b_litlist_v1
let normalise_blitlist_list_ren_env = normalise_blitlist_list_v1

(* without ren_env *)
let normalise_b_litlist term_db_ref bsubst b_litlist = 
  let (norm_lits, _ren_env) = normalise_b_litlist_v1 term_db_ref bsubst b_litlist in
  norm_lits

(* without ren_env *)
let normalise_blitlist_list term_db_ref bsubst blitlist_list = 
  let  (norm_lits, _ren_env) = normalise_blitlist_list_v1 term_db_ref bsubst blitlist_list in
  norm_lits

(*
  let normalise_b_litlist = normalise_b_litlist_v2
  let normalise_blitlist_list = normalise_blitlist_list_v2
 *)

(*
  let normalise_bclause term_db_ref bsubst bclause =
  let (b_c, clause) = bclause in
  let bterm_list = propagate_binding_to_list (b_c, (get_lits clause)) in
  let new_term_list = normalise_bterm_list term_db_ref bsubst bterm_list in
  create new_term_list
 *)

(*
  let normalise_bclause_list term_db_ref bsubst bclause_list =
  let bterm_list_list =
  List.map
  (fun (b_c, clause) ->
  propagate_binding_to_list (b_c, (get_lits clause))) bclause_list in
  let bterm_list = List.flatten bterm_list_list in
  let new_term_list = normalise_bterm_list term_db_ref bsubst bterm_list in
  create new_term_list
 *)
(* for uniformity ise normalise_bclause with empty substitution *)


let normalise_lit_list term_db_ref lit_list =
(* in some cases lits are not yet added to term_db *)
  let db_lit_list = List.map (fun term -> TermDB.add_ref term term_db_ref) lit_list in
  let removed_duplicates = Term.remove_duplicate_terms db_lit_list in 

(*  
  let norm_lit_list = normalise_blitlist_list term_db_ref (SubstBound.create ()) [(1, removed_duplicates)] in
  norm_lit_list
  *)  

(* List.rev norm_lit_list solves a bit less but set difference is quite large; so experiment in changing order during schedule *)
  let norm_lit_list = normalise_blitlist_list term_db_ref (SubstBound.create ()) [(1, removed_duplicates)] in
  dbg D_create (lazy ("before norm:"^(Term.term_list_to_string removed_duplicates)));
  dbg D_create (lazy ("after  norm:"^(Term.term_list_to_string norm_lit_list)^"\n"));
  norm_lit_list


(* as normalise_lit_list but also returns ren_subst *)
let normalise_lit_list_renaming term_db_ref lit_list =
(* in some cases lits are not yet added to term_db *)
  let db_lit_list = List.map (fun term -> TermDB.add_ref term term_db_ref) lit_list in
  let removed_duplicates = Term.remove_duplicate_terms db_lit_list in 
  
(* List.rev norm_lit_list solves a bit less but set difference is quite large; so experiment in changing order during schedule *)
  let (norm_lit_list, ren_env) = 
    normalise_blitlist_list_ren_env term_db_ref (SubstBound.create ()) [(1, removed_duplicates)] in
  dbg D_create (lazy ("before norm:"^(Term.term_list_to_string removed_duplicates)));
  dbg D_create (lazy ("after  norm:"^(Term.term_list_to_string norm_lit_list)^"\n"));
  (norm_lit_list, SubstBound.project_renaming ren_env 1)


(*
  let create_normalise term_db_ref context tstp_source proof_search_param lit_list =
  let normalised_lit_list = normalise_lit_list term_db_ref lit_list in
  create_clause context tstp_source proof_search_param normalised_lit_list
 *)

(*----------------conjecture distance------------------------------------*)
(* a very big number *)
let max_conjecture_dist = 1 lsl 28
let conjecture_int = 0

let get_min_conjecture_distance_clist c_list =
  let f current_min c =
    let d = (get_conjecture_distance c) in
    (if d < current_min then d
    else current_min)
  in List.fold_left f max_conjecture_dist c_list


(* we assume that the check if the clause is a conjecture is done before*)
(* applying get_conjecture_distance_tstp_source *)
(* this is min distance of the parents, so we would need to increase before assigning to the clause *)

let get_conjecture_distance_tstp_source tstp_source =
  let parents = get_parents_tstp tstp_source in
  get_min_conjecture_distance_clist parents



(**-------- create clause ----------------------------*)

let new_clause ~is_negated_conjecture ?(bc_imp_inh=bc_imp_inh_default_val) tstp_source bc =
  let conjecture_distance =
    if is_negated_conjecture
    then 0
    else
      (get_conjecture_distance_tstp_source tstp_source) +1
  in
  let bc_imp_inh_final = 
    let parents = get_main_parents_tstp tstp_source in 
    let imp_parent_list = List.map get_bc_imp_inh parents in
    list_find_min_element Pervasives.compare (bc_imp_inh::imp_parent_list)
  in
  
  let fast_key = !clause_global_counter in
  incr_clause_counter ();
(*  let ps_param = create_ps_param () in *)
  let new_clause =
    {
     basic_clause = bc;
     fast_key = fast_key;
     (*	context_id = 0; *)(* auto assigned when added to context *)
     tstp_source = Def(tstp_source);
  (*   replaced_by = Undef; *)
     (* prop_solver_id = None;*)
     conjecture_distance = conjecture_distance;
     when_born = Undef;
   (*  proof_search_param = Def(ps_param); *)
   (*  ccp_bool_param = Bit_vec.false_vec *)
   }
  in
(*  bc_set_bool_param is_negated_conjecture bc_is_negated_conjecture new_clause; *)
  assign_bc_imp_inh new_clause bc_imp_inh_final;

  let parents = get_parents_tstp tstp_source in
  assign_ps_when_born_concl ~prem1: parents ~prem2:[] ~c: new_clause;

  new_clause

(*
  let fill_clause_param is_conjecture tstp_source ps_param c =
  c.tstp_source <- Def(tstp_source);
  c.proof_search_param <- ps_param;
  c.conjecture_distance <-

(* No auto bool context params *)
(* TODO: conjecture_distance from the rest of the code to here*)
 *)

let create_clause_opts ~is_negated_conjecture ?(bc_imp_inh=bc_imp_inh_default_val) term_db_ref tstp_source lits =
  let bc = create_basic_clause (normalise_lit_list term_db_ref lits) in
  new_clause ~is_negated_conjecture ~bc_imp_inh tstp_source bc

(*---------------*)
(* by default all literals in clauses are normalised *)
(* assume clause is not a negated conjecture *)

let create_clause term_db_ref ?(is_negated_conjecture=false) ?(bc_imp_inh=bc_imp_inh_default_val) tstp_source lits =
  create_clause_opts ~is_negated_conjecture ~bc_imp_inh term_db_ref tstp_source lits

(* assume clause is a negate_conjecture *)
let create_neg_conjecture term_db_ref ?(bc_imp_inh=bc_imp_inh_default_val) tstp_source lits =
  create_clause_opts ~is_negated_conjecture:true ~bc_imp_inh term_db_ref tstp_source lits

(* clause without normalising lits *)
let create_clause_raw tstp_source ?(bc_imp_inh=bc_imp_inh_default_val) lits =
  let bc = create_basic_clause lits in
  new_clause ~is_negated_conjecture:false ~bc_imp_inh tstp_source bc

(* protected for example can be used for proof generation *)	
(*
let in_prop_solver_protected c =
  is_some (c.prop_solver_id)
  *)  

(*--------------Compare two clauses-------------------*)

(* f_perv returns a value that can be compared by Pervasives.compare; ususally int or bool *)
let cmp f_perv c1 c2 = Pervasives.compare (f_perv c1) (f_perv c2)

let cmp_num_var c1 c2 = cmp num_of_var c1 c2

let cmp_num_symb c1 c2 = cmp num_of_symb c1 c2

let cmp_num_lits c1 c2 = cmp length c1 c2

let cmp_age c1 c2 =
  let (when_born1, when_born2) =
    ((get_ps_when_born c1), (get_ps_when_born c2))
  in
  - (Pervasives.compare (when_born1) (when_born2))

let cmp_ground c1 c2 = cmp is_ground c1 c2

let cmp_horn c1 c2 = cmp is_horn c1 c2

let cmp_epr c1 c2 = cmp is_epr c1 c2

(*
let cmp_in_unsat_core c1 c2 = cmp in_unsat_core c1 c2
*)
let cmp_has_eq_lit c1 c2 = cmp has_eq_lit c1 c2

let cmp_has_conj_symb c1 c2 = cmp has_conj_symb c1 c2

let cmp_has_bound_constant c1 c2 = cmp has_bound_constant c1 c2

let cmp_has_next_state c1 c2 = cmp has_next_state c1 c2

let cmp_has_reachable_state c1 c2 = cmp has_reachable_state c1 c2

let cmp_has_non_prolific_conj_symb c1 c2 = cmp has_non_prolific_conj_symb c1 c2

let cmp_conjecture_distance c1 c2 = cmp get_conjecture_distance c1 c2

let cmp_bc_imp_inh c1 c2 = Pervasives.compare  (get_bc_imp_inh c2) (get_bc_imp_inh c1) 
   (* swap the arguments to get smaller, greater*)

let cmp_max_atom_input_occur c1 c2 =
  let d1 = get_max_atom_input_occur c1 in
  let d2 = get_max_atom_input_occur c2 in
  match (d1, d2) with
  | (Def(i1), Def(i2)) -> Pervasives.compare i1 i2
	(* Undef is greater then Def *)
  | (Undef, Def _) -> -1
  | (Def _, Undef) -> 1
  | (Undef, Undef) -> 0

let cmp_min_defined_symb c1 c2 =
  let d1 = get_min_defined_symb c1 in
  let d2 = get_min_defined_symb c2 in
  match (d1, d2) with
  | (Def(i1), Def(i2)) -> Pervasives.compare i1 i2
	(* Undef is greater then Def *)
  | (Undef, Def _) -> -1
  | (Def _, Undef) -> 1
  | (Undef, Undef) -> 0

let cl_cmp_type_to_fun t =
  match t with
  | Options.Cl_Age b -> compose_sign b cmp_age
  | Options.Cl_Num_of_Var b -> compose_sign b cmp_num_var
  | Options.Cl_Num_of_Symb b -> compose_sign b cmp_num_symb
  | Options.Cl_Num_of_Lits b -> compose_sign b cmp_num_lits
  | Options.Cl_Ground b -> compose_sign b cmp_ground
  | Options.Cl_Conj_Dist b -> compose_sign b cmp_conjecture_distance
  | Options.Cl_Has_Conj_Symb b -> compose_sign b cmp_has_conj_symb
  | Options.Cl_has_bound_constant b -> compose_sign b cmp_has_bound_constant
  | Options.Cl_has_next_state b -> compose_sign b cmp_has_next_state
  | Options.Cl_has_reachable_state b -> compose_sign b cmp_has_reachable_state
  | Options.Cl_Has_Non_Prolific_Conj_Symb b -> compose_sign b cmp_has_non_prolific_conj_symb
  | Options.Cl_Max_Atom_Input_Occur b -> compose_sign b cmp_max_atom_input_occur
  | Options.Cl_Horn b -> compose_sign b cmp_horn
  | Options.Cl_EPR b -> compose_sign b cmp_epr
 (* | Options.Cl_in_unsat_core b -> compose_sign b cmp_in_unsat_core *)
  | Options.Cl_Has_Eq_Lit b -> compose_sign b cmp_has_eq_lit
  | Options.Cl_min_defined_symb b -> compose_sign b cmp_min_defined_symb
  | Options.Cl_bc_imp_inh b -> compose_sign b cmp_bc_imp_inh
  | _ -> failwith ("clause compare option is currenlty not supported: "^(Options.cl_cmp_type_to_str t)^"\n")

let cl_cmp_type_list_to_lex_fun l =
  lex_combination ((List.map cl_cmp_type_to_fun l)@[(compose_12 (~-) compare)])

(*------------------------------------------*)

let cl_measure_to_fun cl_measure = 
  match cl_measure with 
  |Options.CM_num_lit  -> length
  |Options.CM_num_var  -> num_of_var
  |Options.CM_num_symb -> num_of_symb
  |Options.CM_cnt      -> (fun _ -> 1)
  |Options.CM_none     -> (fun _ -> 0)


(*------------------------------------------*)
exception Literal_not_found

let rec cut_literal_from_list literal list =
  match list with
  | h:: tl ->
      if h == literal then tl
      else h:: (cut_literal_from_list literal tl)
  |[] -> raise Literal_not_found

(*
  let cut_literal literal lit_list =
 *)

(* ------------ TSTP source  ----------------------- *)

(*  *)
(*
  let assign_tstp_source clause source =

  match clause.tstp_source with

(* Fail if source already defined *)
  | Def _ -> raise (Failure "Clause source already assigned")

(* Only if source undefined *)
  | Undef -> clause.tstp_source <- Def source
 *)

(* Clause is generated in an instantiation inference *)
let tstp_source_instantiation parent parents_side =
  (TSTP_inference_record ((Instantiation parents_side), [parent]))

(* Clause is generated in a resolution inference *)
let tstp_source_resolution parents upon_literals =
  (TSTP_inference_record ((Resolution upon_literals), parents))

(* Clause is generated in a lifted resolution inference *)
let tstp_source_resolution_lifted parents upon_literals =
  (TSTP_inference_record ((Resolution_lifted upon_literals), parents))


(* Clause is generated in a factoring inference *)
let tstp_source_factoring parent upon_literals =
  (TSTP_inference_record ((Factoring upon_literals), [parent]))

let tstp_source_subtyping parent =
  (TSTP_inference_record ((Subtyping), [parent]))

(* Clause is in input *)
let tstp_source_input file name =
  (TSTP_external_source (TSTP_file_source (file, name)))

(* Clause is generated in a global propositional subsumption *)
let tstp_source_global_subsumption max_clause_id parent =
  (TSTP_inference_record (Global_subsumption max_clause_id, [parent]))

(* Clause is generated in a translation to purely equational problem *)
let tstp_source_non_eq_to_eq parent =
  (TSTP_inference_record (Non_eq_to_eq,[parent]))

 let tstp_source_dom_res parent = 
  (TSTP_inference_record (Dom_res,[parent]))

let tstp_source_lifting parent = 
  (TSTP_inference_record (Lifting,[parent]))


(* Clause is generated in a forward subsumption resolution *)
let tstp_source_forward_subsumption_resolution main_parent parents =
  (TSTP_inference_record
     (Forward_subsumption_resolution, (main_parent :: parents)))

(* Clause is generated in a backward subsumption resolution *)
let tstp_source_backward_subsumption_resolution parents =
  (TSTP_inference_record (Backward_subsumption_resolution, parents))

(* Clause is generated in splitting *)
let tstp_source_split atoms parent_list =
  (TSTP_inference_record (Splitting atoms, parent_list))

let tstp_source_flattening parent =
  (TSTP_inference_record (Flattening, [parent]))

let tstp_source_unflattening parent =
  (TSTP_inference_record (Unflattening, [parent]))

let tstp_source_arg_filter_abstr parent =
  (TSTP_inference_record (Arg_filter_abstr, [parent]))

let tstp_source_true_false parent = 
  (TSTP_inference_record (True_false, [parent]))

(* Clause is generated in grounding *)
let tstp_source_grounding grounding parent =
  (TSTP_inference_record (Grounding grounding, [parent]))

(* Clause is generated in copying *)
let tstp_source_copy parent =
  (TSTP_inference_record (Copy, [parent]))

(* Clause is generated by merging definitins *)
let tstp_source_def_merge parent =
  (TSTP_inference_record (Def_merge, [parent]))


(* Clause is generated by variable renaming *)
let tstp_source_renaming parent =
  (TSTP_inference_record (Renaming, [parent]))


let tstp_source_bmc1_merge_next parent =
  (TSTP_inference_record (TSTP_bmc1_merge_next_func, [parent]))

(* Clause is a theory axiom *)
let tstp_source_theory_axiom theory =
  (TSTP_external_source (TSTP_theory theory))

(* Clause is an equality axiom *)
let tstp_source_axiom_equality =
  tstp_source_theory_axiom TSTP_equality

(* Clause is a distinct axiom *)
let tstp_source_axiom_distinct =
  tstp_source_theory_axiom TSTP_distinct

(* Clause is a irreflexivity axiom *)
let tstp_source_axiom_irref =
  tstp_source_theory_axiom TSTP_irref


(* Clause is a domain axiom used in finite models *)
let tstp_source_axiom_domain =
  tstp_source_theory_axiom TSTP_domain

(* Clause is an less axiom *)
let tstp_source_axiom_less =
  tstp_source_theory_axiom TSTP_less

(* Clause is an range axiom *)
let tstp_source_axiom_range =
  tstp_source_theory_axiom TSTP_range

let tstp_source_axiom_bv_succ = 
  tstp_source_theory_axiom TSTP_bv_succ

let tstp_source_axiom_bv_shl1 = 
  tstp_source_theory_axiom TSTP_bv_shl1 

let tstp_source_axiom_bv_shr1 = 
  tstp_source_theory_axiom TSTP_bv_shr1

let tstp_source_axiom_bv_add = 
  tstp_source_theory_axiom TSTP_bv_add

let tstp_source_axiom_bv_sub = 
  tstp_source_theory_axiom TSTP_bv_sub

let tstp_source_axiom_bv_bvugt = 
  tstp_source_theory_axiom TSTP_bv_bvugt

let tstp_source_axiom_bv_bvuge = 
  tstp_source_theory_axiom TSTP_bv_bvuge

let tstp_source_axiom_bv_bvult = 
  tstp_source_theory_axiom TSTP_bv_bvult


let tstp_source_axiom_bv_bvule = 
  tstp_source_theory_axiom TSTP_bv_bvule

let tstp_source_axiom_bv_bveq = 
  tstp_source_theory_axiom TSTP_bv_bveq
  

(* Clause is an bmc1 axiom *)
let tstp_source_axiom_bmc1 bmc1_axiom =
  tstp_source_theory_axiom (TSTP_bmc1 bmc1_axiom)

(* Clause is generated in grounding *)
let tstp_source_assumption =
  (TSTP_internal_source TSTP_assumption)

(* Clause is arg_filter axiom *)
let tstp_source_arg_filter_axiom =
  (TSTP_internal_source TSTP_arg_filter_axiom)

(* Clause is definition merge axiom *)
let tstp_source_def_merge_axiom =
  (TSTP_internal_source TSTP_def_merge_axiom)

let tstp_source_def_merge_nf_impl = 
  (TSTP_internal_source TSTP_def_merge_nf_impl)

let tstp_source_prop_impl_unit =
  (TSTP_internal_source TSTP_prop_impl_unit)

(* term definitions in finite_models *)
let tstp_source_definition =
  (TSTP_internal_source TSTP_definition)

(* in some cases we introduce auxilary clauses which are not kept *)
let tstp_source_tmp =
  (TSTP_internal_source TSTP_tmp)

(*---------------- end TSTP --------------------------*)

(*-------------- Hash/Map/Set -------------------------*)

let hash_bc c =  (bc_get_fast_key (get_bc c))

(* first BMap/BSet/BHashtbl where clauses are uniquely defined by literals (basic clauses) *)
module BKey =
  struct
    type t = clause
    let equal = equal_bc
    let hash = hash_bc
	(*	let hash c = hash_sum (get_fast_key c) (get_context_id c)*)
    let compare = compare_bc
  end

module BCMap = Map.Make(BKey)

module BCSet = Set.Make(BKey)

type bclause_set = BCSet.t

module BCHashtbl = Hashtbl.Make(BKey)

let hash c = (get_fast_key c)

(* Map/Set/Hashtbl can contain different clauses with the same lits (basic_clauses) *)
module Key =
  struct
    type t = clause
    let equal = (==)
    let hash = hash
	(*	let hash c = hash_sum (get_fast_key c) (get_context_id c)*)
    let compare = compare
  end


module CMap = Map.Make(Key)

module CSet = Set.Make(Key)
type clause_set = CSet.t

module CHashtbl = Hashtbl.Make(Key)

(*-------------------- Context -----------------*)

(*----------clause context bool paramters-----------*)

(* context paramters are set outside of reasoning processes *)

let ccp_is_dead = 0  (* user *)
(* ccp_is_dead true the the clause is replaced in a context and replaced by other clauses *)
(* invariant: set of (not ccp_is_dead) clauses imply the set of all clauses in the context *)

(* let cpp_in_prop_solver = 1 (* user *) *)
(* cpp_in_prop_solver means that either this clause is in prop_solver *)
(* or there is  a clause in prop_solver which makes this clause redundant in prop_solver *)
(* the clause itself is not necessarily in the solver *)
(* to check wether clause itself in the solver check prop_solver_id *)

let ccp_in_unsat_core = 2 (* user *)
(* clause was in unsat core in the last proof search run *)
(* used in bmc1 *)

(* if a clause is added to a solver all its parents should be recursively protected from *)
(* clearing tstp_source since they can participate in a proof/unsat core *)

(* let ccp_solver_protected = 3 (* user *)*)

type replaced_by =
    (* when clause got replaced we record the clauses which is got replaced by *)
    (* assumption are: 1) orginal cluase logically follows from the simplifed_by cluases *)
    (* in particular we can replace the original clause by replaced_by clauses *)
    (* there is no cyclic simplification depdendences; we can recover the leaf replacing clauses*)
    (*  which are not replaced *)
  | RB_subsumption of clause
  | RB_sub_typing of clause
  | RB_splitting of clause list
  | RB_copy of clause
  | RB_unflat of clause
  | RB_tautology_elim
  | RB_orphan_elim of clause (* is not used as for replacements at the moment *)

 
type ccp_param = 
    {
     ccp_clause : clause;
   
     (* replaced_by invariants : *)
     (* 1. in a context we can replace all clauses by replaced_by obtaining an equisat set of clauses *)
     (* 2. there is no cycles when following replaced_by *)
     mutable ccp_replaced_by : replaced_by param;
 
(*     mutable proof_search_param : proof_search_param param; *)  (* we can reassign clause paramters within the same context *)

     mutable ccp_bool_param : Bit_vec.bit_vec;

   }

let create_ccp_param clause = 
  {
   ccp_clause = clause;
   ccp_replaced_by = Undef;
   ccp_bool_param = Bit_vec.false_vec;
 }


(*------------- *)
let ccp_get_bool_param param ccp_param =
  Bit_vec.get param ccp_param.ccp_bool_param

let ccp_set_bool_param value param ccp_param =
  ccp_param.ccp_bool_param <- Bit_vec.set value param ccp_param.ccp_bool_param


let ccp_get_is_dead ccp_param = 
  ccp_get_bool_param ccp_is_dead ccp_param


let ccp_get_replaced_by ccp_param =
  ccp_param.ccp_replaced_by

let ccp_assign_replaced_by sby ccp_param =
  ccp_param.ccp_replaced_by <- sby
  


(*
(* clause parameters can contain clauses themselves like inst_children *)
and proof_search_param =
    {
     (* shared paramtes *)
     mutable ps_bool_param : Bit_vec.bit_vec;
     mutable ps_when_born : int param;
     
     (* inst params *)
     mutable inst_sel_lit : (term * sel_place) param;
     mutable inst_dismatching : dismatching param;
     mutable inst_activity : int;
     mutable inst_children : clause list;
     
     (* res params *)
     mutable res_sel_lits : literal_list param;
   }

*)

module Context = BCMap

type context =  
    {mutable cc : ccp_param Context.t;
     mutable cc_size : int;
     mutable cc_num_dead : int;
   }


(* cc -- context*)

(* creates context with an inital size *)
let context_create () = 
  {
   cc = Context.empty;
   cc_size = 0;
   cc_num_dead = 0;
 }

(* let context_reset cc = Context.reset cc (* empties context*) *)

let context_mem cc c = Context.mem c cc.cc 

let context_add cc c =
  try 
    let ccp_param  = Context.find c cc.cc in
    ccp_param.ccp_clause 
  with 
    Not_found -> 
      (
       let new_cpp_param = create_ccp_param c in
       cc.cc <- Context.add c new_cpp_param cc.cc;
       cc.cc_size <- cc.cc_size + 1;     
       c
      )


let context_add_ignore cc c =
  ignore (context_add cc c)

let context_add_list cc c_list =
  List.iter (context_add_ignore cc) c_list

let context_remove cc c = 
  if (Context.mem c cc.cc) 
   then
     (
      cc.cc <-Context.remove c cc.cc;
      cc.cc_size <- cc.cc_size - 1;   
     )
   else
     ()

(* let context_mem_lits cc lits = context_mem cc (create_basic_clause lits) *)

let context_find cc c = 
  let ccp_param = Context.find c cc.cc in 
  ccp_param.ccp_clause 

(* let context_find_lits cc lits = Context.find (create_basic_clause lits) !cc *)

(* first is_dead *)
let context_iter cc ~non_dead f = 
  let g c ccp_param =     
    if ((not non_dead) || not (ccp_get_is_dead ccp_param))
    then 
        (f c)
    else 
        ()
  in
  Context.iter g cc.cc

let context_fold cc ~non_dead f a = 
  let g c ccp_param rest = 
    if ((not non_dead) || not (ccp_get_is_dead ccp_param))
    then
      f c rest
    else
      rest 
  in
  Context.fold g cc.cc a

(* TODO: fix non_dead *)

(*------ccp bool params get/assign-------*)
let get_is_dead cc c =
  try
    ccp_get_is_dead (Context.find c cc.cc)
  with 
    Not_found -> false 

let assign_is_dead cc b c =
  let ccp_param = 
    try 
      (Context.find c cc.cc)
    with 
      Not_found -> 
        (
         let new_ccp_param = create_ccp_param c in 
         cc.cc <- Context.add c new_ccp_param cc.cc;
         cc.cc_size <- cc.cc_size +1;
         new_ccp_param
        )
  in
  let old_dead_val =  ccp_get_is_dead ccp_param in
  if (old_dead_val = b) 
  then ()
  else
    (ccp_set_bool_param b ccp_is_dead ccp_param;
     (if b 
     then (* changed from non-dead to dead *)
       (cc.cc_num_dead <- cc.cc_num_dead +1)
     else (* changed from dead to non-dead *)
       (cc.cc_num_dead <- cc.cc_num_dead - 1)       
     )
    )

let context_size cc ~non_dead = 
  if (not non_dead) 
  then 
    cc.cc_size
  else
    (
     cc.cc_size - cc.cc_num_dead
    )

(* too expensive

let context_size cc ~non_dead = 
  if (not non_dead) 
  then 
    Context.cardinal !cc
  else
    (
     let f c rest = 1 + rest in 
     context_fold cc ~non_dead f 0
    )
*)

(** copy_context from_cxt to_contxt; if a clause in to_context it will remain and not replaced by from_cxt; *)
(** from_cxt remains unchanged;  clauses are not renewed but added so changing paramtes in to_cxt will affect on from_cxt *)
(* use context_reset which clears and resizes to the initial size *)

(*
let context_add_context from_cxt to_cxt =
  let f c =
    ignore (context_add to_cxt c)
  in
  context_iter from_cxt f
*)

let context_to_list cc ~non_dead = context_fold cc ~non_dead (fun c rest -> c::rest) []

let context_to_string cc ~non_dead = clause_list_to_string (context_to_list cc ~non_dead)


let context_copy_from_to ~non_dead ~from_cc ~to_cc = 
  context_iter from_cc ~non_dead (context_add_ignore to_cc)
    
let context_copy ~non_dead cc = 
  let to_cc = context_create () in
  context_copy_from_to ~non_dead ~from_cc:cc ~to_cc;
  to_cc





 (*     
let in_unsat_core c =
  ccp_get_bool_param ccp_in_unsat_core c

let assign_in_unsat_core b c =
  ccp_set_bool_param b ccp_in_unsat_core c
*)

(*---- for aguments which are either context or list we can use --------*)

type context_list = CL_Context of context | CL_List of clause list

let cl_iter f cl = 
  match cl with 
  | CL_Context  cc -> context_iter cc ~non_dead:true f
  | CL_List l -> List.iter f l 

let cl_fold f a cl = 
  match cl with 
  | CL_Context cc -> context_fold cc ~non_dead:true  (fun x y -> f y x) a
  | CL_List l -> List.fold_left  f a l 
  
let cl_size cl = 
  match cl with 
  | CL_Context cc -> context_size ~non_dead:true cc
  | CL_List l -> List.length l

let cl_to_string cl = 
  match cl with 
  | CL_Context cc -> context_to_string cc ~non_dead:true
  | CL_List l -> clause_list_to_string l

(*
 *)

    
(*	let f c =
  let rep_by = get_replaced_by_rec [c] in
  if (rep_by = [])
  then ()
  else
  (context_remove cc c;
  context_add_list cc rep_by
  )
  in
  context_iter cc f
 *)

(* a diferent version prossible to merge from smaller to larger
   let merge_context from_cxt to_contxt =

   let (smaller_cxt, larger_cxt) =
   if (context_size from_cxt) < (context_size to_cxt)
   then
   (from_cxt, to_cxt)
   else
   (to_cxt, from_cxt)
   in (* move from smaller to bigger cxt*)
   let f c =
   if (context_mem larger_cxt c)
   then ()
   else
 *)

(*
(* cc -- context*)
  let cc_create size name = Context.create_name size name
  let cc_mem cc bc = Context.mem cc bc
  let cc_find cc bc = Context.find cc bc
  let cc_size cc = Context.size cc

(* in cc_fold f: bc -> c -> 'a -> 'a *)
  let cc_fold f cc a = Context.fold f cc a

(* in cc_iter f: bc -> c -> unit *)
  let cc_iter f cc = Context.iter f cc
  let cc_add cc clause =
  Context.add clause db_ref

(* should be copyed since add_ref is different....*)
  let cc_add context elem =
  let cc_ref = ref context in
  let _ = cc_add_ref cc_ref elem in
  !cc_ref

  let cc_remove context clause =
  let new_context = Context.remove clause context in
  set_bool_param false in_clause_db clause;
  new_db

  let cc_get_name = ClauseDBM.get_name

  let to_stream s clause_db =
  ClauseDBM.to_stream s to_stream ",\n" clause_db

  let out = to_stream stdout_stream

  let to_string clause_db =
  ClauseDBM.to_string to_stream ",\n" clause_db
 *)

(*
  let normalise term_db_ref clause =
  normalise_bclause term_db_ref (SubstBound.create ()) (1, clause)
 *)

(*----Orphan Search Not Finished--------------*)

(*
let get_non_simplifying_parents clause =
  match clause.tstp_source with
  | Def (TSTP_inference_record ((Resolution upon_literals), parents)) ->
      parents

  | Def (TSTP_inference_record ((Resolution_lifted upon_literals), parents)) ->
      parents
	
  | Def (TSTP_inference_record ((Factoring upon_literals), parents)) ->
      parents
	
  | _ -> []

(* we collect all oprphans in a branch to a dead parent *)
(* if we meet a simplifying clause then we stop and do not include this branch*)
let rec get_orphans clause =
  if (get_is_dead clause)
  then [clause]
  else
    if (get_ps_simplifying clause)
    then []
    else
      let parents = get_non_simplifying_parents clause in
      let parent_result =
	List.fold_left (fun rest curr -> ((get_orphans curr)@rest)) [] parents in
      if not (parent_result = [])
      then
	(clause:: parent_result)
      else []
*)

(*-----assume clause is of the from [pred(sK)] where sK is a state skolem fun---*)
let get_skolem_bound_clause clause =
  match (get_literals clause) with
  |[Term.Fun(symb, args, _)] ->
      if (Symbol.is_a_state_pred_symb symb)
      then
	(match (Term.arg_to_list args)
	with
	|[term] ->
	    if (Term.is_skolem_const term)
	    then Some term
	    else None
	| _ -> None
	)
      else None
  | _ -> None

let replace_subterm termdb_ref subterm byterm lits =
  normalise_lit_list
    termdb_ref
    (List.map (Term.replace subterm byterm) lits)



(*------------ clause signature --------------------*)		  	  
	   (*------------------*)
type clause_signature =
    {
     (* sig_fun_pred contains all functions and predicate symbols *)
     (* occurring in the set of clauses except eq_types which are in sig_eq_types *)
     mutable sig_fun_preds : sym_set;
     mutable sig_eq_types : sym_set;
     mutable sig_pure_dis_eq_types : sym_set; (* types with pure disequality;  *)
     mutable sig_flat_arg_flags : (bool list) SMap.t 
  (* 
     maps to flat signature: f->[b_1,..,b_n] 
     where b_i is true if all f-terms have a variable in arg_i and false otherwise 
     f include pred symbols other than equality; 
     used in congruence reduction
  *)
   }

let create_clause_sig () =
  {
   sig_fun_preds = SSet.empty;
   sig_eq_types = SSet.empty; 
   sig_pure_dis_eq_types = SSet.empty;
   sig_flat_arg_flags = SMap.empty
 
 }

let fill_flat_args csig symb args = 
  let current_flat_args = 
    try 
      SMap.find symb csig.sig_flat_arg_flags
    with
      Not_found -> 
        List.map (fun _-> true) args  (* init assume all vals are true *)
  in
  let f arg flat_b = 
    if (Term.is_var arg)
    then 
      flat_b
    else
      false
  in
  let new_flat_args = List.map2 f args current_flat_args in 
  csig.sig_flat_arg_flags <- SMap.add symb new_flat_args csig.sig_flat_arg_flags
        
let rec extend_clause_sig_term csig sign t =
  match t with
  | Term.Fun(symb, args, _) ->
      let relevant_args =
	if (symb == Symbol.symb_typed_equality)
	then
	  (
	   let (eq_type, t1, t2) =
	     get_triple_from_list (Term.arg_to_list args) in
	   let eq_type_sym = Term.get_top_symb eq_type in
(* deal first with sig_pure_dis_eq_types *)
	   begin
	     if sign 
	     then (* remove from pure_dis *)
	       (
	        csig.sig_pure_dis_eq_types <- SSet.remove eq_type_sym csig.sig_pure_dis_eq_types
	       )
	     else
	       ( (* neg lit *)
		 if (SSet.mem eq_type_sym csig.sig_eq_types) 
		 then () (* the type  was already considered*)
		 else (*add to sig_pure_dis_eq_types *)
		(
		 csig.sig_pure_dis_eq_types <- SSet.add eq_type_sym csig.sig_pure_dis_eq_types
		)
		)
	   end;
	   csig.sig_eq_types <- SSet.add eq_type_sym csig.sig_eq_types;
	   Term.list_to_arg [t1; t2]
	  )
	else
	  (
	   csig.sig_fun_preds <- SSet.add symb csig.sig_fun_preds;
           fill_flat_args csig symb (Term.arg_to_list args);
	   args
	  )
      in
      Term.arg_iter (extend_clause_sig_term csig sign) relevant_args
  | Term.Var _ -> ()

let extend_clause_sig_lit csig lit =
  extend_clause_sig_term csig (Term.is_pos_lit lit) (Term.get_atom lit)

let extend_clause_sig_cl csig clause =
  iter (extend_clause_sig_lit csig) clause

let extend_clause_list_signature csig clause_list =
  List.iter (extend_clause_sig_cl csig) clause_list

let clause_list_signature clause_list =
  let cl_sig = create_clause_sig () in
  extend_clause_list_signature cl_sig clause_list;
  cl_sig


(*--------------------------------------*)
let clause_list_to_set clause_list =
  List.fold_left (fun set cl -> CSet.add cl set) CSet.empty clause_list


let find_all_pred ~is_relevant_pred clause = 
   let add_symb sset sign symb = 
     if (is_relevant_pred sign symb) 
     then
       SSet.add symb sset
     else
       sset
    in
   fold_pred add_symb SSet.empty clause 

let find_all_sym ~is_relevant_symb clause = 
   let add_symb sset symb = 
     if (is_relevant_symb symb) 
     then
       SSet.add symb sset
     else
       sset
    in
   fold_sym add_symb SSet.empty clause 

  

(*---------------------------------------------------*)

let pp_bind ppf (var, term) =
  Format.fprintf
    ppf
    "@[<h>bind(%a,$fot(%a))@]"
    Var.pp_var var
    Term.pp_term_tptp term

let pp_clause_name_bind bind ppf clause =
  Format.fprintf ppf "@[<hov>%a:[%a]@]"
    pp_clause_name clause
    (pp_any_list pp_bind ",") bind

(* Print the name of the BMC1 theory axiom *)
let pp_tstp_theory_bmc1 ppf = function
    
  | TSTP_bmc1_path_axiom b ->
      Format.fprintf ppf "bmc1,[path(%d)]" b
	
  | TSTP_bmc1_reachable_state_axiom b ->
      Format.fprintf ppf "bmc1,[reachable_state(%d)]" b
	
  | TSTP_bmc1_reachable_state_on_bound_axiom b ->
      Format.fprintf ppf "bmc1,[reachable_state_(%d)]" b

	(*	
	  | TSTP_bmc1_reachable_sk_replacement (b, c) ->
	  Format.fprintf
	  ppf "bmc1,[reachable_sk_replacement(%a,%d)]"
	  pp_clause_name c
	  b
	 *)
	
  | TSTP_bmc1_reachable_state_conj_axiom b ->
      Format.fprintf ppf "bmc1,[reachable_state_conj(%d)]" b
	
  | TSTP_bmc1_only_bound_reachable_state_axiom b ->
      Format.fprintf ppf "bmc1,[only_bound_reachable(%d)]" b
	
  | TSTP_bmc1_clock_axiom (b, s, _) ->
      Format.fprintf ppf "bmc1,[clock(%a,%d)]" Symbol.pp_symbol s b

	(*	
	  | TSTP_bmc1_instantiated_clause (b, c) ->
	  Format.fprintf
	  ppf "bmc1,[bound_instantiate_clause(%a,%d)]"
	  pp_clause_name c
	  b
	 *)

(* Print the name of a theory *)
let pp_tstp_theory ppf = function
  | TSTP_equality -> Format.fprintf ppf "equality"
  | TSTP_distinct -> Format.fprintf ppf "distinct"
  | TSTP_irref ->   Format.fprintf ppf "irreflexivity"
  | TSTP_domain -> Format.fprintf ppf "domain"
  | TSTP_bmc1 a -> Format.fprintf ppf "%a" pp_tstp_theory_bmc1 a
  | TSTP_less -> Format.fprintf ppf "less"
  | TSTP_range -> Format.fprintf ppf "range"
  | TSTP_bv_succ  -> Format.fprintf ppf "bv_succ"
  | TSTP_bv_shl1 -> Format.fprintf ppf "bv_shl1"
  | TSTP_bv_shr1 -> Format.fprintf ppf "bv_shr1"
  | TSTP_bv_add -> Format.fprintf ppf "bv_add"
  | TSTP_bv_sub -> Format.fprintf ppf "bv_sub"
  | TSTP_bv_bvugt -> Format.fprintf ppf "bv_bvugt" 
  | TSTP_bv_bvuge -> Format.fprintf ppf  "bv_bvuge" 
  | TSTP_bv_bvult -> Format.fprintf ppf "bv_bvult"
  | TSTP_bv_bvule  -> Format.fprintf ppf "bv_bvule"
  | TSTP_bv_bveq -> Format.fprintf ppf "bv_bveq"


(* Print name of inference rule and its useful info *)
let pp_inference_rule parents ppf = function
    
    (* Useful info for instantiation are side parent clauses *)
  | Instantiation side_parents ->
      
      Format.fprintf
	ppf
	"instantiation,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* Useful info for resolution are resolved literals *)
  | Resolution literals ->
      
      Format.fprintf
	ppf
	"resolution,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

  | Resolution_lifted literals ->
      
      Format.fprintf
	ppf
	"resolution_lifted,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* Useful info for factoring are factored literals *)
  | Factoring literals ->
      
      Format.fprintf
	ppf
	"factoring,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* No useful info for global propositional subsumption *)
  | Global_subsumption _ ->
      
      Format.fprintf
	ppf
	"global_propositional_subsumption,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* No useful info for forward subsumption resolution *)
  | Forward_subsumption_resolution ->
      
      Format.fprintf
	ppf
	"forward_subsumption_resolution,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* No useful info for backward subsumption resolution *)
  | Backward_subsumption_resolution ->
      
      Format.fprintf
	ppf
	"backward_subsumption_resolution,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* No useful info for splitting *)
  | Splitting atoms ->
      
      Format.fprintf
	ppf
	"splitting,@,[splitting(split),new_symbols(definition,[%a])],@,@[<hov 1>[%a]@]"
	(* (pp_any_list Term.pp_term_tptp ",")
	   atoms *) (* Goeff/TPTP expect symbol list rather than atom list *)
        (pp_any_list Symbol.pp_symbol_tptp ",")
        (List.map Term.lit_get_top_symb atoms)
	(pp_any_list pp_clause_name ",")
	parents
	
	(* No useful info for splitting *)
  | Grounding bindings ->
      
      Format.fprintf
	ppf
	"grounding,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list (pp_clause_name_bind bindings) ",")
	parents
	
  | Subtyping ->
      Format.fprintf
	ppf
	"subtyping,@,[status(esa)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
  | Dom_res ->
       Format.fprintf
	ppf
	"domain_res,@,[status(esa)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

  | Lifting -> 
      Format.fprintf
	ppf
	"lifting,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
	(* Clause is from translation to purely equational clauses *)
  | Non_eq_to_eq ->
      Format.fprintf
	ppf
	"non_eq_to_eq,@,[status(esa)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	

  | Flattening ->
      Format.fprintf
	ppf
	"flattening,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
  
  | Unflattening ->
      Format.fprintf
	ppf
	"unflattening,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

  | Arg_filter_abstr ->
      Format.fprintf
	ppf
	"unflattening,@,[status(unp)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

 | True_false ->
      Format.fprintf
	ppf
	"true_false,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents


  | Eq_res_simp ->
      Format.fprintf
	ppf
	"equality_resolution_simp,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
	
  | Dis_eq_elim -> 
      Format.fprintf
	ppf
	"dis_equality_elim,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

  | Def_merge -> 
      Format.fprintf
	ppf
	"def_merge,@,[status(esa)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents	

  | Copy -> 
      Format.fprintf
	ppf
	"copy,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents	

  | Renaming -> 
       Format.fprintf
	ppf
	"renaming,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

  | TSTP_bmc1_instantiated_clause b ->
      Format.fprintf
	ppf "bmc1_instantiate_clause_bound_%i,@,[status(thm)],@,@[<hov 1>[%a]@]"
	b
	(pp_any_list pp_clause_name ",")
	parents				
	
  | TSTP_bmc1_reachable_sk_replacement b ->
      Format.fprintf
	ppf
	"bmc1_reachable_sk_replacement_bound_%i,@,[status(thm)],@,@[<hov 1>[%a]@]"
	b
	(pp_any_list pp_clause_name ",")
	parents
	(*	
	  | TSTP_bmc1_reachable_sk_replacement (b, c) ->
	  Format.fprintf
	  ppf "bmc1,[reachable_sk_replacement(%a,%d)]"
	  pp_clause_name c
	  b
	 *)
  | TSTP_bmc1_init_or_property_axiom ->
      Format.fprintf
	ppf
	"init_or_property,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents
  
  | TSTP_bmc1_merge_next_func -> 
      Format.fprintf
	ppf
	"bmc1_merge_next_func,@,[status(thm)],@,@[<hov 1>[%a]@]"
	(pp_any_list pp_clause_name ",")
	parents

(* Print an inference record

   An inference record is a pair of the inference rule with some useful
   information dependent on the rule and a set of parent clauses
 *)
let pp_tstp_inference_record global_subsumption_justification_fun clause ppf = function
    
    (* Must get justification for global propositional subsumption here *)
  | Global_subsumption max_clause_id, [parent] ->
      
      (match global_subsumption_justification_fun with
      | Some (gs_just_fun) ->
	  
	  (* Get justification for simplification of clause *)
	  let parents' = gs_just_fun
	      max_clause_id
	      parent
	      clause
	  in
	  Format.fprintf
	    ppf
	    "global_propositional_subsumption,@,[status(thm)],@,@[<hov 1>[%a,@,%a]@]"
	    pp_clause_name
	    parent
	    (pp_any_list pp_clause_name ",")
	    (List.filter ((!=) parent) parents')
	    
      | None ->
	  (* output without global subsumtion justification *)
	  Format.fprintf
	    ppf
	    "global_propositional_subsumption_main_parent,@,[status(thm)],@,@[<hov 1>[%a]@]"
	    pp_clause_name
	    parent
      )
	
	(*
	  
	  (* Simplified clause as first parent, then other parent clauses *)
	  Format.fprintf
	  ppf
	  "global_propositional_subsumption,@,[status(thm)],@,@[<hov 1>[%a,@,%a]@]"
	  pp_clause_name
	  parent
	  (pp_any_list pp_clause_name ",")
	  (List.filter ((!=) parent) parents')
	 *)
	
	(* Must get justification for global propositional subsumption here *)
  | Global_subsumption _, _ ->
      
      raise
	(Failure
	   "Global propositional subsumption of more than one parent clause")
	
	(* No special processing for remaining inference rules *)
  | inference_rule, parents ->
      
      Format.fprintf
	ppf
	"%a"
	(pp_inference_rule parents)
	inference_rule

(* Print source of a clause *)
let pp_tstp_source global_subsumption_justification_fun clausify_proof clause ppf = function
    
    (* Clause is from a file *)
  | TSTP_external_source (TSTP_file_source (file, name)) ->
      
      (* Rewrite source to match clausification proof? *)
      if clausify_proof then
	
	try
	  
	  (* Scan name of clause into u<n> *)
	  let fof_id = Scanf.sscanf name "u%d" (function i -> i) in
	  
	  (* Output name of fof formula *)
	  Format.fprintf
	    ppf
	    "inference(cnf_transformation,[],[f%d])"
	    fof_id
	    
	    (* Name of clause is not u<n> *)
	with Scanf.Scan_failure _ ->
	  
	  (* Print source as it is *)
	  Format.fprintf ppf "file('%s', %s)" file name
	    
      else
	
	(* Print source as it is *)
	Format.fprintf ppf "file('%s', %s)" file name
	  
	  (* Clause is from a theory *)
  | TSTP_external_source (TSTP_theory theory) ->
      
      Format.fprintf ppf "theory(%a)" pp_tstp_theory theory
	
	(* Clause is from an internal definition *)
  | TSTP_internal_source TSTP_definition ->
      
      Format.fprintf ppf "definition"
	
	(* Clause is from an internal assumption *)
  | TSTP_internal_source TSTP_assumption ->
      
      Format.fprintf ppf "assumption"
	(* Auxilary clause which was  temporaly introduced; should not occur in proofs *)

  | TSTP_internal_source TSTP_arg_filter_axiom ->
      
        Format.fprintf ppf "arg_filter_axiom"

  | TSTP_internal_source TSTP_def_merge_axiom ->
       Format.fprintf ppf "def_merge_axiom"

  | TSTP_internal_source TSTP_def_merge_nf_impl ->
       Format.fprintf ppf "def_merge_nf_impl"

  | TSTP_internal_source TSTP_prop_impl_unit ->
      Format.fprintf ppf "prop_impl_unit"

  | TSTP_internal_source TSTP_tmp ->
      
      Format.fprintf ppf "tmp"
	
	(* Clause is from an inference *)
  | TSTP_inference_record inference_record ->
      
      Format.fprintf
	ppf
	"@[<hv 10>inference(%a)@]"
	(pp_tstp_inference_record global_subsumption_justification_fun clause)
	inference_record

(* Print clause with source in TSTP format *)
let pp_clause_with_source ?(global_subsumption_justification_fun = None) ?(clausify_proof = false)  ppf clause =
  let c_type =   
    (if (is_negated_conjecture clause)
    then "negated_conjecture"
    else "plain")
  in
  Format.fprintf
    ppf
    "@[<hv 4>cnf(%a,%s,@,@[<hv 2>%a,@]@,%a ).@]@\n@."
    pp_clause_name clause
    c_type
    pp_clause_literals_tptp clause
    (pp_tstp_source global_subsumption_justification_fun clausify_proof clause)
    (get_tstp_source clause)

let pp_clause_list_with_source ?(global_subsumption_justification_fun = None) ?(clausify_proof = false)  ppf clause_list =
  List.iter (pp_clause_with_source ppf ~global_subsumption_justification_fun ~clausify_proof) clause_list

(*-------clause output with all params-----*)

type 'a fun_type =
    FInt of ('a -> int)
  | FStr of ('a -> string)
  | FFloat of ('a -> float)
  | FBool of ('a -> bool)
  | FTerm of ('a -> term)
  | FTerm_list of ('a -> (term list))
  | FSymb of ('a -> symbol)
  | FClause of ('a -> clause)
  | FClause_list of ('a -> (clause list))
(*  | FReplaced_by of ('a -> replaced_by) *)
(*|FDInt of ('a -> int param) *)

type clause_fun_type = clause fun_type
      
let pp_lib_param pp_a_fun ppf x =
  match x with
  | Def a ->
      fprintf ppf "%a"
	pp_a_fun a
  | Undef ->
      fprintf ppf "Undef"

let pp_clause_name_list ppf c_list =
  fprintf ppf "@[<hov>%a@]" (pp_any_list pp_clause_name ";") c_list

let pp_term_list ppf t_list =
  fprintf ppf "@[%a@]" (pp_any_list Term.pp_term ",") t_list

let pp_replaced_by ppf rb =
  match rb with
  | RB_subsumption c -> fprintf ppf "RB_subsumption(%a)" pp_clause_name c
  | RB_sub_typing c -> fprintf ppf "RB_sub_typing(%a)" pp_clause_name c
  | RB_splitting c_list ->fprintf ppf "RB_splitting(%a)" pp_clause_name_list c_list
  | RB_tautology_elim -> fprintf ppf "RB_tautology_elim"
  | RB_copy c ->  fprintf ppf "RB_copy(%a)" pp_clause_name c
  | RB_unflat c -> fprintf ppf "RB_unflat(%a)" pp_clause_name c
  | RB_orphan_elim c -> fprintf ppf "RB_orphan_elim(%a)" pp_clause_name c

let pp_fun f ppf a =
  try
    match f with
    | FInt (f) -> fprintf ppf "%i" (f a)
    | FStr (f) -> fprintf ppf "%s" (f a)
    | FFloat (f) -> fprintf ppf "%f" (f a)
    | FBool (f) -> fprintf ppf "%b" (f a)
    | FTerm (f) -> Term.pp_term ppf (f a)
    | FTerm_list (f) -> pp_term_list ppf (f a)
    | FSymb (f) -> Symbol.pp_symbol ppf (f a)
    | FClause (f) -> pp_clause_name ppf (f a)
    | FClause_list (f) -> pp_clause_name_list ppf (f a)
(*    | FReplaced_by (f) -> pp_replaced_by ppf (f a) *)
  with
  | Undef_param -> fprintf ppf "Undef"
  | None_opt -> fprintf ppf "None_opt"
(*
  | Res_sel_lits_undef -> fprintf ppf "Res_sel_lits_undef"
  | Inst_sel_lit_undef -> fprintf ppf "Inst_sel_lit_undef"
*)

let comp_f f1 f2 x = f1 (f2 x)

type param_out_list = (string * (clause_fun_type)) list

let param_out_list_gen =
  [
   ("name",FStr(clause_get_name));
   ("fast_key", FInt(get_fast_key));
   ("num_of_symb", FInt(num_of_symb));
   ("num_of_var", FInt(num_of_var));
   ("length", FInt(length));
(*   ("prop_solver_id", FInt(get_some_fun get_prop_solver_id)); *)
(*   ("is_dead", FBool(get_is_dead)); *)
(*   ("replaced_by", FReplaced_by(get_param_val_fun get_replaced_by)); *)
(*   ("in_unsat_core", FBool(in_unsat_core)); *)
  (* ("in_prop_solver", FBool(in_prop_solver)); *)
   ("is_negated_conjecture", FBool(is_negated_conjecture));
   ("conjecture_distance", FInt(get_conjecture_distance));
   ("is_ground", FBool(is_ground));
   ("is_horn", FBool(is_horn));
   ("is_epr", FBool(is_epr));
   ("is_eq_axiom", FBool(is_eq_axiom));
   ("has_eq_lit", FBool(has_eq_lit));
   ("has_conj_symb", FBool(has_conj_symb));
   ("has_non_prolific_conj_symb", FBool(has_non_prolific_conj_symb));
   ("get_max_atom_input_occur", FSymb(get_param_val_fun get_max_atom_input_occur));
 ]

let param_out_list_bmc1 =
  [
   ("has_bound_constant", FBool(has_bound_constant));
   ("has_next_state", FBool(has_next_state));
   ("has_reachable_state", FBool(has_reachable_state));
   ("get_min_defined_symb", FInt(get_param_val_fun get_min_defined_symb));
 ]

(*
let param_out_list_ps =
  [
   ("ps_in_active", FBool(get_ps_in_active));
   ("ps_in_subset_subsumption_index", FBool(get_ps_in_subset_subsumption_index));
   ("ps_in_subsumption_index", FBool(get_ps_in_subsumption_index));
   ("ps_in_passive_queue", FBool(get_ps_in_passive_queue));
   ("ps_sel_max", FBool(get_ps_sel_max));
   ("ps_simplifying", FBool(get_ps_simplifying));
   
   (* non bool proof search param *)
   ("ps_when_born", FInt(get_ps_when_born));
   ("inst_children", FClause_list(get_inst_children));
 ]
*)

(*
let param_out_list_res =
  [("res_sel_lits", FTerm_list (get_res_sel_lits));
 ]

let param_out_list_inst =
  [ ("inst_get_sel_lit", FTerm (inst_get_sel_lit));
    ("inst_activity", FInt(inst_get_activity));
    (*	("dismatching:", FDismatching(get_inst_dismatching)); *) (* TODO: add dismatching output*)
  ]
*)
let param_out_list_all =
  param_out_list_gen@param_out_list_bmc1(*@param_out_list_ps@param_out_list_res@param_out_list_inst*)

let pp_clause_params param_out_list ppf c =
  let param_name p = (get_pair_first p) in
  let param_fun p = (get_pair_second p) in
  let max_param_length =
    let max_pair =
      list_find_max_element
	(fun p1 p2 -> Pervasives.compare (String.length (param_name p1)) (String.length (param_name p2)))
	param_out_list
    in
    String.length (param_name max_pair)
  in
  let val_dist = max_param_length + 5 in
  
  let param_name_padded p =
    (space_padding_str_sep '.' val_dist ((tptp_safe_str ((param_name p)^":")))) in
  
  let pp_param ppf p =
    fprintf ppf "@[<v>%s %a @,@]"
      (param_name_padded p)
      (pp_fun (param_fun p))
      c
  in
  let pp_param_list ppf list = 
    List.iter (pp_param ppf) list
  in	
  fprintf ppf "@[<v>%a@]"
    pp_param_list param_out_list

(*----------------copy/clear clause--------------------------*)

let copy_clause c =
(*  let new_fast_key = !clause_global_counter in
  incr_clause_counter ();
*)

  
  dbg_env D_copy 
    (fun () -> 
     (
      dbg D_copy (lazy "");
      Format.printf "@[%a @]@.@[%a @]@."
        (*(pp_clause_with_source ?global_subsumption_justification_fun:None ?clausify_proof:None) clause*)
        pp_clause_tptp c
        (pp_clause_params param_out_list_all) c
     )
    );
 
  let tstp_source = tstp_source_copy c in

  let new_clause = create_clause_raw tstp_source (get_lits c) in 
(*  set_ps_simplifying (get_ps_simplifying c) new_clause; *)
  assign_ps_when_born (get_ps_when_born c) new_clause; 
  inherit_conjecture c new_clause; 

  new_clause

  

let refresh_clause clause = 
(*  let ps_param = create_ps_param () in *)
(*  clause.proof_search_param  <- Def(ps_param);*)
  let new_clause = copy_clause clause in 
  (* replace with assert *)    
  (*assign_is_dead false new_clause; *)
  (*	(if  (get_is_dead clause) 
    then 
    (	
    Format.printf "@[%a @]@.@[%a @]@."
    (*(pp_clause_with_source ?global_subsumption_justification_fun:None ?clausify_proof:None) clause*)
    pp_clause clause
    (pp_clause_params param_out_list_all) clause;
    )
    else ());*)
(*  assert (not (get_is_dead clause));  *)
  assign_ps_when_born 0 new_clause; 
  new_clause 
   

(*
let copy_clause c =
  let new_fast_key = !clause_global_counter in
  incr_clause_counter ();
  
  let ps_param = create_ps_param () in
  let new_c =
    { c with
      fast_key = new_fast_key;
      proof_search_param = Def(ps_param)
    }
  in
  set_ps_simplifying (get_ps_simplifying c) new_c;
  assign_ps_when_born (get_ps_when_born c) new_c;
  
(*
  (if (c.fast_key = 557) 
  then 
  Format.printf "@[%a @]@.@[%a @]@."
  (*(pp_clause_with_source ?global_subsumption_justification_fun:None ?clausify_proof:None) clause*)
  pp_clause c
  (pp_clause_params param_out_list_all) c
  );
 *)
  new_c
*)
(*
  (* clears tstp_source of the clause should not be used after that     *)
(* unless it was recoreded in propositional solver for proof purposes *)
(* improve to replacing creating ps_param, may be define as Def/Undef *)
  let clear_clause c = 
  (*(if (c.fast_key = 557) 
    then 
    Format.printf "@[%a @]@.@[%a @]@."
    (*(pp_clause_with_source ?global_subsumption_justification_fun:None ?clausify_proof:None) clause*)
    pp_clause c
    (pp_clause_params param_out_list_all) c
    );
   *)
  if not (is_solver_protected c) 
  then
  (
  c.tstp_source <- Undef;
  c.replaced_by <- Undef;
  c.proof_search_param <- Undef (* (create_ps_param ()) *)
  )
  else ()	
 *)  

(*----------------Replaced by-------------------------------------*)

(* returns clause list with which c was replaced *)
(* returns Undef if the clause should be kept as it is *)

let get_replaced_by_clauses cc c =
  try
    let ccp_param = Context.find c cc in 
    match ccp_param.ccp_replaced_by with 
    | Def(RB_subsumption by_clause) -> 
      (*if (lits_equal by_clause c) 
	then 
	Undef
	else	
	( 
	Format.printf "\n Clause:\n %a\n" pp_clause c;
	Format.printf "\n Subsumed by\n: %a\n" pp_clause by_clause;
       *)
      (
       (*
	 Format.printf "\n Clause:\n %a\n" pp_clause c;
	 Format.printf "\n Replaced_by RB_subsumption \n: %a\n" pp_clause by_clause;
	*)
       Def([by_clause])
      )
  | Def(RB_sub_typing by_clause) ->
      (*
	Format.printf "\n Clause:\n %a\n" pp_clause c;
	Format.printf "\n Replaced_by  RB_sub_typing \n: %a\n" pp_clause by_clause;
       *)
      Def([by_clause])
	
  | Def(RB_unflat by_clause) ->
      (*
	Format.printf "\n Clause:\n %a\n" pp_clause c;
	Format.printf "\n Replaced_by  RB_unflat \n: %a\n" pp_clause by_clause;
       *)
      Def([by_clause])

  | Def(RB_splitting by_clause_list) ->
      (*
	Format.printf "\n Clause:\n %a\n" pp_clause c;
	Format.printf "\n Replaced_by RB_splitting  \n: %a\n" pp_clause_list_tptp by_clause_list;
       *)
      Def(by_clause_list)
  | Def(RB_copy by_clause) ->
      (*
	Format.printf "\n Clause:\n %a\n" pp_clause c;
	Format.printf "\n Replaced_by  RB_copy \n: %a\n" pp_clause by_clause;
       *)
      Def([by_clause])
        
  | Def(RB_tautology_elim) -> Def([])
  | Def(RB_orphan_elim _) -> Undef (* do not replace clause if it is dead because of orphan elimination *)
  | Undef -> Undef
  with 
    Not_found -> Undef

 

(* add assert of non-cyclicity check *)
let get_replaced_by_rec cc current_replace_set clause_list =
  let rec f visited to_process keep_as_is =
    match to_process with
    | h:: tl ->
	(
	 if (BCSet.mem h visited) 
	 then
	   f visited tl keep_as_is
	 else
	   begin
	     let new_visited = BCSet.add h visited in 
	     match get_replaced_by_clauses cc h with
	     | Def rep_c_by_list -> 
		 let new_to_process = rep_c_by_list@tl in
		 f new_visited new_to_process keep_as_is
	     | Undef -> 	
		 (* let new_keep_as_is = h::keep_as_is in *)
		 let new_h = (refresh_clause h) in
		 (*				Format.printf "Replaced_by: @, %a\n @." pp_clause_tptp new_h;
          	   Format.print_flush ();
		  *)
		 let new_keep_as_is = BCSet.add new_h keep_as_is in
		 f new_visited tl new_keep_as_is
	   end					 							
	)
    |	[] -> keep_as_is
  in
  f BCSet.empty clause_list current_replace_set

(* replaces dead clauses with replaced *)
let context_replace_by cc current_replace_set c =
  if (context_mem cc c) 
  then
    (
   (* let found_c =  (context_find cc c) in *)
    (*	Format.print_flush ();
      Format.printf "Init Clause: @, %a\n @." pp_clause_tptp found_c;
      Format.print_flush ();
     *)
     let replaced_by = get_replaced_by_rec cc.cc current_replace_set [c] 
     in 
     incr_int_stat 1 simp_replaced_by;
(*			
  Format.printf "\n Final Replaced by:\n %a\n@." pp_clause_list_tptp (BSet.elements replaced_by);
  Format.print_flush ();
 *)	
     replaced_by
    )
  else
(*    (BSet.add (refresh_clause c) current_replace_set) *)
    (BCSet.add c current_replace_set) 
      
let context_replace_by_clist cc clist = 
  let replace_set = 
    List.fold_left (fun rest c ->  (context_replace_by cc rest c)) BCSet.empty clist in
  BCSet.elements replace_set

(* tsar: anti-skolemization code here *)

(* get all the skolem constants in the clause *)
let get_all_skolem_constants clause =
  (* is term is a skolem constant add it to the set *)
  let add_const_term set term =
    if (Term.is_skolem_const term)
    then
      Symbol.Set.add (Term.get_top_symb term) set
    else
      set
  in

  (* for the literal: go through all the args of its atom *)
  let add_const_of_literal set literal =
    let atom = Term.get_atom literal in
    Term.arg_fold_left add_const_term set (Term.get_args atom)
  in

  (* check the sK in all the literals of the clause *)
  List.fold_left add_const_of_literal Symbol.Set.empty (get_literals clause)

(* get list out of set *)
let set_to_list set =
  let f elt list = list @ [elt] in
  Symbol.Set.fold f set []

(* get list of state skolem consts out of all consts *)
let get_state_skolem_const symbols =
  (* check whether const is a state const *)
  let f symbol = Symbol.is_state_type_symb (Symbol.get_val_type_def symbol) in
  (* filter all state consts *)
  List.filter f symbols


let has_symb symb clause = 
  let lits = get_lits clause in
  List.exists (fun lit -> (symb == Term.lit_get_top_symb lit)) lits

(*---------------------*)

let assign_is_essential_input_symb input_clauses =
  cl_iter (iter_sym (Symbol.assign_is_essential_input true)) input_clauses

let unassign_is_essential_input_symb input_clauses =
  cl_iter (iter_sym (Symbol.assign_is_essential_input false)) input_clauses

(*---------------------*)

let remove_bc_duplicates cl_list = 
  let bcset = BCSet.of_list cl_list in
  BCSet.elements bcset

(*------ a bit out dated  ----------*)


let out_clauses_param cl =
  let out_cl c =
    out_str ("Clause: "
	     ^(to_string c)
	     ^" has conj symb: "
	     ^ (string_of_bool (has_conj_symb c ))
	     ^" has non-prolific conj symb: "
	     ^(string_of_bool (has_non_prolific_conj_symb c ))
	     ^" has bound constant: "
	     ^(string_of_bool (has_bound_constant c ))
		 
	     ^"\n")
  in   
  out_str ("\n\n ------------------------------\n\n");
  cl_iter out_cl cl;
  out_str ("\n\n ------------------------------\n\n")

(*-------------*)
let out_mem () = 
  (
   print_objsize "bc_clause_db_weak" bc_clause_db_weak;
   print_objsize "bc_clause_db" bc_clause_db;
  )


(*
  [
  ("",);
  ("",);
  ("",);
  ("",);
  ("",);
  ("",);
  ]
 *)
