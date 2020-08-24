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
open Logic_interface
open Options
open Bmc1Common

(***** my code ****)


(* create $$constB0 *)
let state_term_b0 () = create_state_term 0

(* replace given const with a given var in clause *)
let replace_const_with_var clause const var =
  Clause.replace_subterm term_db_ref const var (get_lits clause)


(* check whether a clause contains given const *)
let has_const clause const =
  (* return true if const is a sub-term of a given term *)
  let has_const_in_term term = Term.is_subterm const term in
  List.exists has_const_in_term (Clause.get_lits clause) 


(* get all the clauses with B0 *)
let get_B0_clauses clauses =
  let state_term_b0 = state_term_b0() in
  let has_const_B0 clause = has_const clause state_term_b0 in
  (* split all clauses using previously defined helper *)
  let with_B0, without_B0 = List.partition has_const_B0 clauses in
  (* return those that contain B0 *)
  with_B0, without_B0

(* get var that does not exists in the clause *)
let get_fresh_state_var clause =
  (* it is enough to get the 1st var, as init clause have a single state var *)
  Var.get_first_var state_type

(* tsar *)
let add_init_to_clause clause =
  (* define the necessary const *)
  let const_b0 = state_term_b0() in
  (* define fresh var *)
  let var = add_var_term (get_fresh_state_var clause) in
  (* declare Init(var) ??? MULTIPRED!!! *)
  let init_atom = create_auto_init_atom var in
  (* make negated literal *)
  let init_lit = add_compl_lit init_atom in
  (* replace const with the var in the clause *)
  let literals = replace_const_with_var clause const_b0 var in
  (* make new clause *)
  let tstp_source = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, [clause])  in
  (* all literals *)
  let new_clause_literals = init_lit :: literals in
  (* create new axiom *)
  let axiom_with_init = create_clause tstp_source new_clause_literals in

  (* return newly created clause *)
  axiom_with_init


(* add ~init(v) and replace constB0 with v in all clauses *)
let add_init_to_clauses clauses =
  List.rev_map add_init_to_clause clauses

(* add init statement *)
let add_init_predicate clauses =
  (* find all B0 Clauses *)
  let with_B0, without_B0 = get_B0_clauses clauses in

  (* print them for now *)
  (**)
  (* print_clauses "with B0" with_B0; *)
  (**)

  (* transform B0 clauses *)
  let init_clauses = add_init_to_clauses with_B0 in
  if val_of_override !current_options.bmc1_verbose
  then print_clauses "with init" init_clauses;

  (* merge new list with the rest *)
  List.rev_append init_clauses without_B0









(*------- skolem constant extraction -----------*)

exception Skolem_Duplicated

(* return None if CLAUSE doesn't contain state_type const, and Some CONST otherwise *)
let get_skolem_state_const_op clause =
  (* get the skolem state const of the state const CONST *)
  let get_ssc_of_const value const =
    try
      (match value with
      | None -> Some const
      | Some sK ->
        if sK == const
        then value
        else raise Skolem_Duplicated
      )
    with
    Skolem_Duplicated ->
      failwith "bmc1InitTarget: two different skolem state const in negated conjecture"
  in

  (* for the term: check whether it is a const of a state_type *)
  let get_ssc_of_term value term =
    (* test whether the term is of a state type *)
    let is_state_type_term term =
      let symbol = Term.get_top_symb term in
      (Symbol.get_val_type_def symbol) == state_type
    in

    (* state_type skolem constant? *)
    if (Term.is_skolem_const term) && (is_state_type_term term)
    then
      get_ssc_of_const value term
    else
      value
  in

  (* for the literal: go through all the args of its atom *)
  let get_ssc_of_literal value literal =
    let atom = Term.get_atom literal in
    Term.arg_fold_left get_ssc_of_term value (Term.get_args atom)
  in

  (* check the sK in all the literals of the clause *)
  List.fold_left get_ssc_of_literal None (Clause.get_literals clause)


(* return true if the CLAUSE contains a state_type const *)
let has_skolem_state_const clause =
  match (get_skolem_state_const_op clause) with
  	| None -> false
    | _ -> true

(* return the state_type const of a CLAUSE *)
let get_skolem_state_const clause =
  try
    match (get_skolem_state_const_op clause) with
    	| Some sk -> sk
      | _ -> raise Skolem_Duplicated
  with Skolem_Duplicated ->
    failwith "No skolem state const found in a clause"

(* remove reachableState(sK) from clauses; clauses are assumed to contain sK *)
let remove_reachable_state_sk clauses =
  (* return true if clause = reachableState(sK) *)
  let is_reachable_state clause =
    match get_lits clause with
    | [Term.Fun(symb, _, _)] ->
      symb == Symbol.symb_ver_reachable_state
    | _ -> false
  in

  (* separate reachableState() from others *)
  let with_reachable_state, others = List.partition is_reachable_state clauses in

  (* return the rest *)
  others

(* choose the way to create a clause that share type with original one *)
let clause_constructor clause =
(*
  let constructor =
    if 0 = Clause.get_conjecture_distance clause
    then Clause.create_neg_conjecture
    else Clause.create_clause
  (* add the necessary term_db_ref here *)
  in 
*)
  Clause.create_clause term_db_ref ~is_negated_conjecture:(Clause.is_negated_conjecture clause)

(* get lits of all state skolem constants in a clause *)
let get_all_state_sk clause =
  Clause.get_state_skolem_const (Clause.set_to_list (Clause.get_all_skolem_constants clause))

(* add [~]$$property(sK) to a clause with state sK; do nothing if there is no such const *)
let add_property_to_clause positive clause =
  (* create new clause with sK *)
  let create_clause_with_property const_symb clause positive =
    (* make const term *)
    let const = add_fun_term const_symb [] in
    (* declare $$property(sK) *)
    let property_atom = create_property_atom const in
    (* choose proper polarity of $$property(sK) *)
    let property_lit =
      if positive
      then property_atom
      else add_compl_lit property_atom
    in
    (* create TSTP *)
    let tstp_source = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, [clause]) in
    (* get new clause literals *)
    let new_clause_literals = property_lit :: (Clause.get_literals clause) in
    (* choose which clause to do *)
    let constructor = clause_constructor clause in
    (* return fresh clause *)
    constructor tstp_source new_clause_literals
  in
  (* get the state sk list *)
  let state_sk_consts = get_all_state_sk clause in
  (* get the state skolem const from a non-empty list *)
  let get_state_sk_const consts =
    (* list should be a singleton *)
    assert (1 = (List.length consts));
    List.hd consts
  in
  (* add property only if list is non-empty *)
  if list_is_empty state_sk_consts
  then clause
  else create_clause_with_property (get_state_sk_const state_sk_consts) clause positive


(* get all the clauses with skolem state const *)
let get_sk_clauses clauses =
  (* split all clauses depending on whether they got a skolem state const *)
  let with_state_sk, without_state_sk = List.partition has_skolem_state_const clauses in

  (* return those that contain skolem state const *)
  with_state_sk, without_state_sk


(* print all clauses together with their constants *)
let print_all_clauses_with_const clauses =
  let print_symbol symbol out = out^(Symbol.to_string symbol)^"," in
  let print_set set =
    let semi_set = Symbol.Set.fold print_symbol set "{" in
    semi_set^"}"
  in
  let print_clause clause =
    out_str ("Clause: "^(Clause.to_string clause)^"\n constants: "^(print_set (Clause.get_all_skolem_constants clause))^"\n")
  in
  List.iter print_clause clauses


(* get a list of types from a set of skolem constant symbols *)
let get_types_by_constants set_of_consts =
  let get_type const accum = (Symbol.get_val_type_def const) :: accum in
  Symbol.Set.fold get_type set_of_consts []

(* get a list of constants from a set of skolem constant symbols *)
let get_args_by_constants set_of_consts =
  let get_const const accum = (add_fun_term const []) :: accum in
  Symbol.Set.fold get_const set_of_consts []

(* create a set of split literals for clauses that are negated *)
let create_split_literals clauses =
  (* choose a literal for clause *)
  let choose_lit clause =
    (* get all literals *)
    let literals = Clause.get_literals clause in
    if (List.length literals) = 1
    then
      (* just take the only literal *)
      List.hd literals
    else
      (* all skolem constants in the clause *)
      let skolem_consts = Clause.get_all_skolem_constants clause in
      (* argument types of a split symbol *)
      let type_list = get_types_by_constants skolem_consts in
      (* generate new split symbol *)
      let split_symbol = SymbolDB.create_new_split_symb symbol_db_ref
	       (Symbol.create_stype type_list Symbol.symb_bool_type)
      in
      (* get arguments for a split term *)
      let split_args = get_args_by_constants skolem_consts in
      (* create split atom itself *)
      let split_atom = add_fun_term split_symbol split_args in
      (* return atom *)
      split_atom
  in
  (* negate the chosen literal *)
  let split_term clause = add_compl_lit (choose_lit clause) in

  (* now replace every clause with a new literal. NB! keep an order so we do the *)
  List.map split_term clauses


(* create split axiom by given original clauses and newly created split terms *)
let create_split_axioms split_literals clauses =
  (* generate tstp by clause TODO: add a proper TSTP *)
  let gen_tstp clause = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, [clause]) in
  (* create a single split axiom *)
  let gen_split_axiom tstp_source split_lit other_lit =
    (* generate an axiom ~split(sK)|~L_i *)
    let split_clause = create_clause tstp_source [split_lit ; (add_compl_lit other_lit)] in
    (* return that clause *)
    split_clause
  in
  (* clause folder *)
  let clause_folder tstp_source split_lit accum other_lit =
    (gen_split_axiom tstp_source split_lit other_lit) :: accum in
  let split_axioms_for_clause accum split_lit clause =
    let tstp_source = gen_tstp clause in
    List.fold_left (clause_folder tstp_source split_lit) accum (Clause.get_literals clause) in
  let split_axioms_for_clause accum split_lit clause =
    if 1 = List.length (Clause.get_literals clause)
    then accum (* nothing to do *)
    else split_axioms_for_clause accum (add_compl_lit split_lit) clause
  in
  List.fold_left2 split_axioms_for_clause [] split_literals clauses

(* anti-skolemise given clause replacing all consts from SKOLEM_CONSTS *)
let anti_skolemise_clause_consts clause skolem_consts =
  (* create a variable of a given type *)
  let get_var var_type n = Var.create var_type n in
  (* index for vars *)
  let var_index = ref (-1) in
  (* get next var of a given type *)
  let get_next_var var_type =
    (* inc var index so the var would be new *)
    var_index := (succ !var_index);
    (* return the var of that index *)
    get_var var_type !var_index
  in
  (* get fresh var of the type of a given const *)
  let get_fresh_var const = get_next_var (Symbol.get_val_type_def const) in
  (* fold function: replace all constants in the list with fresh vars *)
  let replace_const_with_var const literals =
    let var = add_var_term (get_fresh_var const) in
    let const_term = add_fun_term const [] in
    Clause.replace_subterm term_db_ref const_term var literals
  in
  (* replace all terms in all literals in clause *)
  let literals = Symbol.Set.fold replace_const_with_var skolem_consts (Clause.get_lits clause) in
  (* prepare TSTP source TODO: proper TSTP *)
  let tstp_source = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, [clause]) in
  (* choose clause c'tor wrt the neg_conj value *)
  let constructor = clause_constructor clause in
  (* return fresh clause *)
  constructor tstp_source literals

let anti_skolemise_clause clause =
  (* get all sK consts from clause *)
  let skolem_consts = Clause.get_all_skolem_constants clause in
  anti_skolemise_clause_consts clause skolem_consts

(* replace existing state SK with var, leaving all other constants intact *)
let replace_state_sk_with_var' clause =
  (* get skolem clause *)
  let sk = (get_skolem_state_const clause) in
  (* create state_type var *)
  let var_term = term_x0 state_type in
  (* replace sk with var in literals of a clause *)
  let literals = replace_const_with_var clause sk var_term in
  (* prepare TSTP source TODO: proper TSTP *)
  let tstp_source = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, [clause]) in
  (* choose clause c'tor wrt the neg_conj value *)
  let constructor = clause_constructor clause in
  (* return fresh clause *)
  constructor tstp_source literals

(* replace state SK with var, leaving all other constants intact *)
let replace_state_sk_with_var clause =
  if has_skolem_state_const clause
  then replace_state_sk_with_var' clause
  else clause

(* get all skolem constants in all clauses *)
let get_all_sk clauses =
  (* add all sk cfrom a clause to accum *)
  let add_sk_from_clause accum clause = Symbol.Set.union accum (Clause.get_all_skolem_constants clause) in
  (* apply to all clauses *)
  List.fold_left add_sk_from_clause Symbol.Set.empty clauses

(* *)
let get_all_extra_clauses clauses sk_consts =
  let need_clause set clause = not (Symbol.Set.is_empty (Symbol.Set.inter set (Clause.get_all_skolem_constants clause))) in
  let rec get_clauses set clauses =
    let update_set set clauses = Symbol.Set.union set (get_all_sk clauses) in
    let needed, unneeded = List.partition (need_clause set) clauses in
    let set' = update_set set needed in
    if set' == set  (* no new symbols *)
    then needed
    else (* new symbols are found in needed axioms *)
      needed @ (get_clauses set' unneeded)
  in
  get_clauses sk_consts clauses


(* implement \psi -> $$property by \neg\psi given in clauses *)
let add_pos_property_to_clauses clauses =
  (* print all clauses with sk *)
  (**)
  (* out_str "axioms in \\neg\\psi:\n";    *)
  (* print_all_clauses_with_const clauses; *)
  (**)

  (* add $$property to all axioms in clauses *)
  let axioms_with_property = List.rev_map (add_property_to_clause (*positive=*)true) clauses in
  (**)
  (* print_clauses "with $$property" axioms_with_property; *)
  (**)
  (* anti-skolemize those clauses *)
  let anti_sk_clauses = List.rev_map replace_state_sk_with_var axioms_with_property in
  (* print if verbose *)
  if val_of_override !current_options.bmc1_verbose
  then print_clauses "part of $$property(S) predicate" anti_sk_clauses;

  (* return those clauses *)
  anti_sk_clauses

(* implement $$property -> \psi by \neg\psi given in non-empty clauses *)
let add_neg_property_to_clauses' clauses =
  assert (list_non_empty clauses);

  (* check whether all axioms have at most one state skolem const *)
  let check_state_sk_clause clause =
    assert ((List.length (get_all_state_sk clause)) < 2)
  in
  List.iter check_state_sk_clause clauses;

  (* create a list of representatives of negated clauses *)
  let cnf_lits = create_split_literals clauses in
  (* the main clause consists of all those literals. We add a literal ~$$property(sK) here *)
  (* because all other parts of \psi would be fired either directly or via split symbols.*)
  (* This is the only place ~$$property(sK) is added. *)
  let tstp_source = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, [(List.hd clauses)]) in
  let split_axiom = add_property_to_clause (*positive=*)false (create_clause tstp_source cnf_lits) in

  (* split the axioms of \neg\psi to get \psi *)
  let split_axioms = create_split_axioms cnf_lits clauses in
  (**)
  (* print_clauses "after split" split_axioms; *)
  (**)
  (* anti-skolemize split clauses *)
  let anti_sk_split_clauses = List.map anti_skolemise_clause split_axioms in
  let anti_sk_clauses = (anti_skolemise_clause split_axiom) :: anti_sk_split_clauses in
  if val_of_override !current_options.bmc1_verbose
  then print_clauses "part of $$property(S) predicate" anti_sk_clauses;

  (* return those clauses *)
  anti_sk_clauses

(* implement $$property -> \psi by \neg\psi given in (possibly empty) clauses *)
let add_neg_property_to_clauses clauses =
  if list_non_empty clauses
  then add_neg_property_to_clauses' clauses
  else []

(* add $$property to clauses *)
let add_property_to_clauses normal_clauses neg_conjectures =
  (* return true iff clause contains skolem const *)
  let has_sk clause = not (Symbol.Set.is_empty (Clause.get_all_skolem_constants clause)) in

  (* figure out all axioms with skolem const: *)

  (* get all axioms with sk from neg conjecture *)
  let nc_sk', nc_free = List.partition has_sk neg_conjectures in
  (* remove $$reachableState(sK) from them *)
  let nc_sk = remove_reachable_state_sk nc_sk' in
  (* print_clauses "all with sk from neg conj" nc_sk; *)

  (* get all axioms with sk from normal clauses *)
  let ax_sk', ax_free' = List.partition has_sk normal_clauses in
  (* print_clauses "all with sk from normal" ax_sk'; *)
  (* out of them, keep only those that share consts with nc_sk *)
  let ax_sk = get_all_extra_clauses ax_sk' (get_all_sk nc_sk) in
  (* print_clauses "all those who share consts with neg_conj" ax_sk; *)
  (* FORNOW: assert that all of them share consts *)
  assert ((List.length ax_sk') = (List.length ax_sk));
  (* TODO: add the rest to "free" ones *)
  let ax_free = ax_free' in

  (* here are all the axioms with sK *)
  let all_sk = nc_sk @ ax_sk in

  (* make axioms \psi -> $$property *)
  let pos_property_axioms = add_pos_property_to_clauses all_sk in
  (* make axioms $$property -> \psi if necessary *)
  let neg_property_axioms =
    if need_property_predicate ()
    then add_neg_property_to_clauses all_sk
    else []
  in
  (* all property axioms *)
  let property_axioms = pos_property_axioms @ neg_property_axioms in

  (* filter to distinguish neg conjectire *)
  let is_neg_conjecture clause = (0 = Clause.get_conjecture_distance clause) in
  (* split all new axioms into neg_conj and normal *)
  let nc_new, ax_new = List.partition is_neg_conjecture property_axioms in

  (* return new axioms together with the rest of other *)
  (ax_new @ ax_free), (nc_new @ nc_free)

(* main function: we need to add $$property() and $$init() axioms to set of axioms *)
let bmc1_add_init_and_property () =
  (* all axioms *)
  let normal_clauses' = !Parser_types.parsed_clauses in
  (* negated conjecture *)
  let neg_conjectures' = !Parser_types.neg_conjectures in

  (* update property parts *)
  let normal_clauses, updated_conjectures =
    if need_property_from_predicate () (* at least the weak one *)
    then add_property_to_clauses normal_clauses' neg_conjectures'
    else normal_clauses', neg_conjectures'
  in

  (* update init parts *)
  let updated_clauses =
    if need_init_predicate ()
    then add_init_predicate normal_clauses
    else normal_clauses
  in

  (* save updated list *)
  Parser_types.parsed_clauses := updated_clauses;
  Parser_types.neg_conjectures := updated_conjectures
