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


(* to generate mli use "ocamlc -I obj/ -i src/bmc1Common.ml > src/bmc1Common.mli" *)

open Lib
open Logic_interface
open Options

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_model_selected
  | D_model_rejected

let dbg_gr_to_str = function
  | D_model_selected -> "model_selected"
  | D_model_rejected -> "model_rejected"

let dbg_groups =
  [
    D_model_selected;
 ]

let module_name = "bmc1_common"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(* k-induction algorithm stage *)
type k_induction_stage = IndBase | IndStep


(* flip the k_induction stage *)
let k_induction_stage_flip stage =
  match stage with 
  | IndBase -> IndStep
  | IndStep -> IndBase


(* print stage *)
let stage_to_string stage =
  match stage with
  | IndBase -> "BASE"
  | IndStep -> "STEP"

(* phase of a reasoning *)
type mc_phase = {
  mutable mc_cur_bound : int;
  mutable mc_alg_stage: k_induction_stage;
  mutable mc_deadlock_stay_base: bool;
}

(* print phase *)
let phase_to_string phase =
  "stage "^(stage_to_string phase.mc_alg_stage)^" bound "^(string_of_int phase.mc_cur_bound)

(* initial phase *)
let get_initial_phase () =
  {
    mc_cur_bound = 0;
    mc_alg_stage = IndBase;
    mc_deadlock_stay_base = false;
  }

type bmc_handlers = {
  mc_task_name: string;
  mc_update_phase: mc_phase -> unit;
  mc_after_sat: mc_phase -> unit;
  mc_after_unsat: mc_phase -> unit;
  mc_get_next_bound_axioms: mc_phase -> clause list * term list;
}

(* print the clauses with given prefix *)
let print_clauses prefix clauses =
  Lib.out_str ("\nClauses "^prefix^": "^(string_of_int (List.length clauses))^"\n"^(Clause.clause_list_to_string clauses)^"\n")

(* name of current MC task *)
let current_task_name () =
  if !current_options.bmc1_deadlock
  then "deadlock"
  else if !current_options.bmc1_k_induction
  then "k-induction"
  else if !current_options.bmc1_property_lemmas
  then "BMC1 with property lemmas"
  else "BMC1"

(*--------- Additional axioms detection -------------*)

(* Is it necessary to add $$init(S) -> ... axioms *)
let need_init_predicate () =
  (* every BMC mode but AIG require init *)
  (val_of_override !current_options.bmc1_incremental) &&
  not !current_options.aig_mode

(* Is it necessary to add $$property(S) <- ... axioms *)
let need_property_from_predicate () =
  (* every BMC mode but AIG require this *)
  (val_of_override !current_options.bmc1_incremental) &&
  not !current_options.aig_mode

(* Is it necessary to add $$property(S) <-> ... axioms *)
let need_property_predicate () =
  need_property_from_predicate ()
    && (!current_options.bmc1_property_lemmas
        || !current_options.bmc1_k_induction)

(* Is it necessary to add $$Equal(S,S') -> ... axioms *)
let need_equal_to_predicate () =
  !current_options.bmc1_non_equiv_states && !current_options.bmc1_deadlock

(* Is it necessary to add $$Equal(S,S') <- ... axioms *)
let need_equal_from_predicate () =
  !current_options.bmc1_non_equiv_states && !current_options.bmc1_k_induction

(* Is it necessary to add $$deadlock(S) -> ... axioms *)
let need_deadlock_predicate () =
  !current_options.bmc1_deadlock

(*--------- Symbol names and name patterns ------------*)

(* Type of addresses *)
let address_type = Symbol.symb_ver_address_type

(* Type of states *)
let state_type = Symbol.symb_ver_state_type

(* Type of bitindexes *)
let bitindex_type = Symbol.symb_ver_bit_index_type

(* Name of addressDiff symbol *)
let address_diff_symbol_name = "$$addressDiff"

(* Name of addressDiff symbol *)
let address_val_symbol_name = "$$addressVal"

(* Name of address symbol *)
let address_symbol_name = "$$address"

(* Name of base guard (k-induction) *)
let base_guard_symbol = "$$iProver_base"

(* Name of full relation guard (multi-pred) *)
let full_rel_guard_symbol = "$$iProver_full_rel"

(* Format of symbol for active bound *)
let bound_symbol_format = format_of_string "$$iProver_bound%d"

(* Format of symbol for bitindex *)
let bitindex_symbol_format = format_of_string "bitindex%d"

(* Format of state symbol *)
let state_symbol_format = format_of_string "$$constB%d"

(********** Generic functions **********)

(*
(* Get n-th variable recursively *)
  let rec var_n' accum = function

(* Terminate and return accumulated variable *)
  | 0 -> accum

(* Fail for negaive variable numbers *)
  | i when i < 0 -> failwith ("Bmc1Axioms.var_n: variable number must be >= 0")

(* Recurse to get next variable *)
  | i -> var_n' (Var.get_next_var accum) (pred i)
 *)

(* Get n-th variable *)
let var_n vtype n = Var.create vtype n
(*	var_n' (Var.get_first_var ()) n*)

(* Get n-th variable term *)
let term_xn vtype n =
  add_var_term (var_n vtype n)

(* Create term for variable X0 *)
let term_x0 vtype =  (term_xn vtype 0)

(* Create term for variable X1 *)
let term_x1 vtype =  (term_xn vtype 1)

(* Create term for variable X2 *)
let term_x2 vtype = (term_xn vtype 2)

(* Create typed equation *)
let create_typed_equation stype lhs rhs = add_typed_equality_sym stype lhs rhs
    (*
      (* Add or retrieve type term from term database *)
      let stype_term =
      TermDB.add_ref
      (Term.create_fun_term stype [])
      term_db
      in

      (* Add or retrieve equation from term database *)
      TermDB.add_ref
      (Term.create_fun_term
      Symbol.symb_typed_equality
      [stype_term; lhs; rhs])
      term_db
     *)

(*
(* Create term *)
  let create_constant_term symbol_name symbol_type =

  (* Type of symbol *)
  let symbol_stype = Symbol.create_stype [] symbol_type in

  (* Add symbol to symbol database *)
  let symbol =
  SymbolDB.add_ref
  (Symbol.create_from_str_type symbol_name symbol_stype)
  symbol_db
  in

  (* Add term to term database *)
  let term =
  TermDB.add_ref
  (Term.create_fun_term symbol [])
  term_db
  in

  (* Return creted term *)
  term
 *)



let create_constant_term const_name const_type_symb =
  let const_stype = Symbol.create_stype [] const_type_symb in
  let const = create_symbol const_name const_stype in
  add_fun_term const []

(* Create skolem term with parameter *)
let create_skolem_term (symbol_format : ('a -> 'b, 'c, 'd, 'e, 'e, 'b) format6) symbol_type (name_param: 'a) =

  (* Name of skolem symbol *)
  let skolem_symbol_name = Format.sprintf symbol_format name_param in

  (* Create term *)
  create_constant_term skolem_symbol_name symbol_type

(* Create atom with arguments *)
let create_atom ?(is_special=false) symbol_name arg_types args =

  (* Create stype of symbol *)
  let symbol_stype =
    Symbol.create_stype arg_types Symbol.symb_bool_type
  in

  (* Add or retrieve symbol from symbol database *)
  let symbol = create_symbol symbol_name symbol_stype
  in
  Symbol.set_is_special_symb is_special symbol;
  (* Create atom and add to term database *)
  let atom = add_fun_term symbol args
  in

  (* Return created atom *)
  atom

let create_atom_symb symb args =
  let atom = add_fun_term symb args in
  atom

(* get list of argument types of x for predicate P(S,x) *)
let get_arg_types_list p =
  (* get the list of all types *)
  let args, value = Symbol.get_stype_args_val_def p in
  (* remove the state var *)
  let types = List.tl args in
  (* return that list *)
  types

(* get list of distinct var terms by given list of types *)
let get_arg_var_list_of_types types =
  (* create new (i-th) var term of a given type *)
  let get_ith_var vars i vtype = vars @ [(term_xn vtype i)] in
  (* index for vars *)
  let var_index = ref (1) in
  (* get next var of a given type *)
  let get_next_var vars vtype =
    (* inc var index so the var would be new *)
    var_index := (succ !var_index);
    (* return the var of that index *)
    get_ith_var vars !var_index vtype
  in
  (* create list of vars *)
  let arg_list = List.fold_left get_next_var [] types in
  (* return that list *)
  arg_list

(* get list of var terms x for predicate P(S,x) *)
let get_arg_var_list p =
  get_arg_var_list_of_types (get_arg_types_list p)


(********** Creation of terms and atoms **********)
(* TODO: move cone_exclude_symbs *)

let cone_exclude_symbs = ref (SSet.of_list [Symbol.symb_ver_next_state; Symbol.symb_ver_init; Symbol.symb_ver_equal])

let add_cone_ex_symb symb = 
  cone_exclude_symbs:=SSet.add symb !cone_exclude_symbs

(*---------------------------*)

(* Create term for state, i.e. constB{n} *)
let create_state_term n =
  create_skolem_term state_symbol_format state_type n

(* Create atom for active bound, i.e. $$iProver_bound{bound} *)
let create_bound_atom n =
  let atom = create_skolem_term bound_symbol_format Symbol.symb_bool_type n in 
(* excl. from cone*)
  let pred = Term.get_top_symb atom in 
  add_cone_ex_symb pred;
  atom

(* Create atoms $$iProver_bound{bound} up to [ubound], in [accum] *)
let rec create_bound_atom_list accum ubound = function

    (* Terminate on upper bound and return list in ascending order *)
  | bound when bound >= ubound -> List.rev accum

	(* Create atom for bound, add to list and recurse for next bound *)
  | bound ->

      create_bound_atom_list
	((create_bound_atom bound) :: accum)
	ubound
	(succ bound)

(* Create guard to be added to Step clause *)
let create_step_guard () =
  (* create corresponding atom $$iProver_base *)
  let step_guard_atom = create_constant_term base_guard_symbol Symbol.symb_bool_type in

(* excl. from cone*)
  let pred = Term.get_top_symb step_guard_atom in 
  add_cone_ex_symb pred;

  (* return that atom *)
  step_guard_atom

(* Create guard to be added to Base clause *)
let create_base_guard () =
  (* negate step atom for a guard *)
  add_compl_lit (create_step_guard ())

(* create assumption for the base stage *)
let create_base_assumption() = create_step_guard ()
(* create assumption for the step stage *)
let create_step_assumption() = create_base_guard ()

(* create assumption for the full relation *)
let create_full_r_assumption () =
  (* create corresponding atom $$iProver_full_rel *)
  let full_r_assumption_atom = create_constant_term full_rel_guard_symbol Symbol.symb_bool_type in

(* excl. from cone*)
  let pred = Term.get_top_symb full_r_assumption_atom in 
  add_cone_ex_symb pred;

  (* return that atom *)
  full_r_assumption_atom


(* create assumption for the reduced relation *)
let create_short_r_assumption () =
  (* negate full r atom for an assumption *)
  add_compl_lit (create_full_r_assumption ())

(* create guard to be added to short relation clause *)
let create_short_r_guard () = create_full_r_assumption ()
(* create guard to be added to full relation clause *)
let create_full_r_guard () = create_short_r_assumption ()


(* Create term for bitindex, i.e. bitindex{n} *)
let create_bitindex_term n =
  create_skolem_term bitindex_symbol_format bitindex_type n

(* Create atom for bitvector, i.e. b000(X0) *)
let create_bitvector_atom bitvector_symbol_name bitindex_term =
  create_atom
    bitvector_symbol_name
    [ bitindex_type ]
    [ bitindex_term ]

(*---------------------------------------------*)
(* Methods to generate $next(i,S,S') predicate *)
(*---------------------------------------------*)

(* UCM support *)


(* all the constants Cj that participate in the problem *)
let next_state_consts_ref = ref TSet.empty

(* return those consts *)
let get_next_state_consts () = !next_state_consts_ref

(* Create next state atom for two states, i.e. nextState(constB{p}, constB{q}) *)
let create_next_atom rel_ind state_p state_q =
  create_atom_symb Symbol.symb_ver_next_state [rel_ind; state_p; state_q]

(* aux method to create a relational index const *)
let rel_index_const () =
  if !current_options.bmc1_ucm
  then (
    let index = FiniteDomain.get_new_const Symbol.symb_ver_relation_index_type in
    (* save it in the set *)
    next_state_consts_ref := TSet.add index !next_state_consts_ref;
    (* return index *)
    index
  )
  else
    FiniteDomain.get_first_const Symbol.symb_ver_relation_index_type

(* aux method to get a relational index var *)
let rel_index_var () = term_x0 Symbol.symb_ver_relation_index_type

(* Create path atom for two states, i.e. nextState(constB{p}, constB{q}) *)
(* WARNING: constant is incremented automatically, so create a new rel for a new *)
(* usage unless you KNOW what you're doing *)
let create_auto_path_atom state_p state_q =
  create_next_atom (rel_index_const ()) state_p state_q

(*---------------------------------------------*)
(* Methods to generate $init(i,S) predicate *)
(*---------------------------------------------*)

(* Create initial state atom for given state, i.e. $$init(state) *)
let create_init_atom rel_ind state =
  create_atom_symb Symbol.symb_ver_init [rel_ind; state]

(* Create init atom for two states, i.e. $$init(state) *)
(* WARNING: constant is incremented automatically, so create a new rel for a new *)
(* usage unless you KNOW what you're doing *)
let create_auto_init_atom state =
  create_init_atom (rel_index_const ()) state

(*---------------------------------------------*)

(* Create property atom for given state, i.e. $$property(state) *)
let create_property_atom state =
  create_atom_symb Symbol.symb_ver_property [state]

(* Create atom for equal states, i.e. $$Equal(state, state') *)
let create_equal_state_atom state state' =
  create_atom_symb Symbol.symb_ver_equal [state; state']

(* Create atom for eligible state, i.e. $$eligibleDeadlock(state) *)
let create_eligible_atom state =
  create_atom_symb Symbol.symb_ver_eligible [state]

(* Create atom for deadlock condition, i.e. $$deadlock(state) *)
let create_deadlock_atom state =
  create_atom_symb Symbol.symb_ver_deadlock [state]

(* Create addressDiff atom for given arguments *)
let create_address_diff_atom arg1 arg2 arg3 =
  create_atom ~is_special:true
    address_diff_symbol_name
    [ address_type; address_type; bitindex_type ]
    [ arg1; arg2; arg3 ]

(* Create addressVal atom for given arguments *)
let create_address_val_atom arg1 arg2 =
  create_atom ~is_special:true
    address_val_symbol_name 
    [ address_type; bitindex_type ]
    [ arg1; arg2 ]

(* Create sort atom for address, i.e. address(state) *)
let create_address_atom address =
  create_atom ~is_special:true
    address_symbol_name
    [ address_type ]
    [ address ]

(********** Path axioms **********)

(* Create path atom $$nextState(b, b-1) *)
let create_path_atom b =

  (* Create state term for state *)
  let state_term_b = create_state_term b in

  (* Create state term for preceding state *)
  let state_term_pred_b = create_state_term (pred b) in

  (* Create path axiom for states *)
  let path_atom_b =
    create_next_atom (rel_index_var ()) state_term_b state_term_pred_b
  in

  (* return that atom *)
  path_atom_b

(* Create path axiom {$$nextState(b, b-1)|fullP} *)
let create_path_axiom b =
  (* Create path axiom for states *)
  let path_atom_b = create_path_atom b in

  (* if predicate split is active then guard this with current state *)

  (* Create guard for full relation *)
  let guard = create_full_r_guard () in

  (* add guard if necessary *)
  let path_lits =
    if !current_options.bmc1_ucm
    then [ path_atom_b; guard ]
    else [ path_atom_b ]
  in

  (* Create unit clause of atom *)
  let path_axiom_b =
    let tstp_source =
      Clause.tstp_source_axiom_bmc1
	(Clause.TSTP_bmc1_path_axiom b)
    in
    create_clause tstp_source path_lits
  in

  (* Return path axiom for bound *)
  path_axiom_b


(*********** Property axioms **************)

(* Create property state axiom $$property(b) *)
let create_property_axiom b =

  (* Create state term for state *)
  let state_term_b = create_state_term b in

  (* Create property state literal for state, i.e. $$property(b) *)
  let create_property_predicate state_term =
    create_atom_symb Symbol.symb_ver_property [state_term]
  in
  let property_lit_b = create_property_predicate state_term_b in

  (* FOR NOW: leave the tstp source as for reachable state *)
  let tstp_source =
    Clause.tstp_source_axiom_bmc1
      (Clause.TSTP_bmc1_reachable_state_on_bound_axiom b)
  in
  (* Create unit clause of atom *)
  let property_axiom_b =
    create_clause tstp_source [ property_lit_b ]
  in

  (* Return property axiom for bound *)
  property_axiom_b

(* Create property state axiom ~$$property(b) *)
let create_neg_property_axiom b =

  (* Create state term for state *)
  let state_term_b = create_state_term b in

  (* Create property state literal for state, i.e. ~$$property(b) *)
  let create_property_predicate state_term =
    create_atom_symb Symbol.symb_ver_property [state_term]
  in
  let property_lit_b = add_compl_lit (create_property_predicate state_term_b) in

  (* FOR NOW: leave the tstp source as for reachable state *)
  let tstp_source =
    Clause.tstp_source_axiom_bmc1
      (Clause.TSTP_bmc1_reachable_state_on_bound_axiom b)
  in
  (* Create unit clause of atom *)
  let property_axiom_b =
    create_clause tstp_source [ property_lit_b ]
  in

  (* Return property axiom for bound *)
  property_axiom_b

(*********** Init axioms **************)

(* Create init state atom $$init(b) *)
let create_init_atom_b b =
  (* Create state term for state *)
  let state_term_b = create_state_term b in
  let init_atom_b = create_init_atom (rel_index_var ()) state_term_b in
  (* return that atom *)
  init_atom_b

(* Create init state axiom $$init(b) | ~$$iProver_bound{b} *)
let create_guarded_init_axiom b =
  (* Create init state literal for state, i.e. $$init(b) *)
  let init_lit_b = create_init_atom_b b in

  (* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
  let bound_literal = add_compl_lit (create_bound_atom b) in

  (* $$init(b) | ~$$iProver_bound{b} *)
  let init_axiom_lits =
    if !current_options.bmc1_ucm
    then (* need ~full_rel as well *)
      [ bound_literal; init_lit_b; (create_full_r_guard ()) ]
    else
      [ bound_literal; init_lit_b ]
  in

  (* FOR NOW: leave the tstp source as for reachable state *)
  let tstp_source =
    Clause.tstp_source_axiom_bmc1
      (Clause.TSTP_bmc1_reachable_state_on_bound_axiom b)
  in
  (* Create clause of atom *)
  let init_axiom_b =
    create_clause tstp_source init_axiom_lits
  in

  (* Return init axiom for bound *)
  init_axiom_b

(* Create negative init state axiom ~$$init(b) *)
let create_neg_init_axiom b =
  (* Create init state literal for state, i.e. ~$$init(b) *)
  let init_atom_b = create_init_atom_b b in
  let init_lit_b = add_compl_lit init_atom_b in

  (* FOR NOW: leave the tstp source as for reachable state *)
  let tstp_source =
    Clause.tstp_source_axiom_bmc1
      (Clause.TSTP_bmc1_reachable_state_on_bound_axiom b)
  in
  (* Create clause of atom *)
  let neg_init_axiom_b =
    create_clause tstp_source [init_lit_b]
  in

  (* Return init axiom for bound *)
  neg_init_axiom_b

(********** Equal state axioms **********)

(* Create non-equal state axiom {~$$Equal(b, b') *)
let create_non_equal_state_axiom b b' =

  (* Create state term for b and b' *)
  let state = create_state_term b in
  let state' = create_state_term b' in

  (* Create non-equal literal for states *)
  let equal_atom = create_equal_state_atom state state' in
  let non_equal_lit = add_compl_lit equal_atom in

  (* Create TSTP source FIXME!! for now *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom b') in

  (* Create unit clause of literal *)
  let nequal_axiom = create_clause tstp_source [ non_equal_lit ] in

  (* Return than axiom *)
  nequal_axiom

(*---------------- Model-related methods ---------------*)

(* return a set of ground terms that represent a model, *)
(* given by a set of clauses with selected literals on. *)
(* Ignore those clauses on which use_clause function is false. *)

let get_model_lits inst_pre_model (* all_clauses *) ~use_clause ~apply_grounding =
  (* get grounded selected lit from the clause *)
  let get_gr_lits clause pme lit_set =
    if use_clause clause
    then (
      (* get selected lit *)
(*      let sel_lit = Clause.inst_get_sel_lit clause in *)
        let sel_lit = Instantiation_env.inst_pme_get_sel_lit pme in

      let lit = 
        if apply_grounding 
        then 
          let gr_lit = add_term_db (Term.get_grounding_lit sel_lit) in
          dbg D_model_selected (lazy ("gr: "^(Term.to_string gr_lit)
                                      ^", clause: "^(Clause.to_string clause)
                                      ^", sel: "^(Term.to_string sel_lit)));
          gr_lit 
        else 
          (
           dbg D_model_selected (lazy (
                                 ", clause: "^(Clause.to_string clause)
                                 ^", sel: "^(Term.to_string sel_lit)));     
          sel_lit 
          )
      in


      TSet.add lit lit_set
    )
    else (
      dbg D_model_rejected (lazy ("clause: "^(Clause.to_string clause)));
      lit_set
    )
  in
  (* get selected lits *)
(*  let sel_lit_set = context_fold ~non_dead:false all_clauses get_gr_lits TSet.empty in *)

  let sel_lit_set = BCMap.fold get_gr_lits inst_pre_model TSet.empty in 

  (* return that literals *)
  sel_lit_set
