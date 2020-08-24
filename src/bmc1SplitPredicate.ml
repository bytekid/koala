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
open Cone_symb

let dbg_flag = false

type dbg_gr =
  | D_trace
  | D_next_unsat
  | D_sel_lit
  | D_tr_set
  | D_aig_cones
  | D_aig_cones_full
  | D_cone
  | D_cone_full
  | D_cone_symb
  | D_cone_symb_full
  | D_lemmas
  | D_model
  | D_tr_from_model

let dbg_gr_to_str = function
  | D_trace
  | D_next_unsat  ->  "next_in_unsat"
  | D_sel_lit -> "sel_lit"
  | D_tr_set -> "tr_set"
  | D_aig_cones -> "aig_cones"
  | D_aig_cones_full -> "aig_cones_full"
  | D_cone -> "cone"
  | D_cone_full -> "cone_full"
  | D_cone_symb -> "cone_symb"
  | D_cone_symb_full -> "cone_symb_full"
  | D_lemmas -> "lemmas"
  | D_model -> "model"
  | D_tr_from_model -> "tr_from_model"

let dbg_groups =
  [
   D_trace;
(*   D_tr_set; *)
(*   D_aig_cones; *)
(*   D_aig_cones_full; *)
   (* D_cone;  	   *)
   (* D_cone_symb; *)
   (* D_model; *)
   D_tr_from_model;
   (* D_sel_lit;*)
 ]

let module_name = "bmc1SplitPredicate"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- end debug -----*)


(* atoms those literals already participated in unsat core *)
let unsat_core_participated_atoms = ref TSet.empty

(* symbols whose literals already participated in unsat core *)
let unsat_core_participated_symbols = ref SSet.empty

(*----------*)
let prep_cone_clauses_map = ref PairIntMap.empty

let prep_cone_flag = true

let get_prep_cone_clauses cone depth = 
  let get_cone_clauses cone depth = 
    let cone_set = (Cone_symb.get_cone_clauses cone ~depth) in
    let cone_clauses = CSet.elements cone_set in
    dbg D_cone_symb_full  (lazy ("cone:\n"^(Clause.clause_list_to_string cone_clauses)));
    dbg D_cone_symb  (lazy ("cone depth: "^(string_of_int depth)^" max_cone_depth:"
			    ^(string_of_int (Cone_symb.get_cone_max_depth cone))^"\n"));
    dbg D_cone_symb  (lazy ("cone size: "^(string_of_int (List.length cone_clauses))^"\n"));  
    cone_clauses
  in
  if prep_cone_flag && (depth > 0)
  then
    let cone_id = Cone_symb.get_cone_id cone in 
    let key = (cone_id, depth) in
    try 
      let stored_clauses = PairIntMap.find key !prep_cone_clauses_map in 
      dbg D_cone_symb 
      (lazy ("prep cone: stored clauses: "^"cone_id: "^(string_of_int cone_id)^" cone depth: "^(string_of_int depth)));
      stored_clauses
    with
      Not_found -> 
	let cone_clauses =  get_cone_clauses cone depth in
(*	List.iter (fun c -> Clause.assign_is_dead false c) cone_clauses;  *)

(* TODO: fix *)
        out_warning ("bmc1SplitPredicate: Preprocess.preprocess fix side atoms");
        let prep_state = Preprocess.prep_create_state ~clause_list:cone_clauses ~extra_side_atoms:[] in      
        Preprocess.preprocess_sim ~before_eq_axioms:false prep_state;
	let prep_cone_clauses = Preprocess.prep_get_clauses prep_state in  
	dbg D_cone_symb  (lazy ("preprocessed cone size: "^(string_of_int (List.length prep_cone_clauses))^"\n"));
	dbg D_cone_symb_full (lazy ("preprocessed cone: "^(Clause.clause_list_to_string prep_cone_clauses)^"\n"));
	prep_cone_clauses_map := PairIntMap.add key prep_cone_clauses !prep_cone_clauses_map;
	prep_cone_clauses  
  else
    begin
      let cone_clauses =  get_cone_clauses cone depth in
      cone_clauses
    end

(*----------*)

(* Generate $$nextState axioms from given unsat core clauses *)

(* get set of all predicates of the form $$nextState(Cj,s,s') *)
(* and set of clauses without those from clauses *)
let get_next_predicates_from_clauses clauses =
  (* set of terms $$next(Cj,s,s') *)
  let found_predicates = ref TSet.empty in
  (* set of clauses from input (=that doesn't contain positive $$next) *)
  let problem_clauses = ref [] in
  (* return true it lit is a positive $next; add th e"good" lits to a set *)
  let mark_lit lit =
    (* need only positive lits that unifs with appropriate splits *)
    let pos = not (Term.is_neg_lit lit) in
    if (pos && Term.is_next_state_lit lit)
    then
    (
      (* don't collect artificial literals $$nextState(Cj,s,s) *)
      let args = Term.arg_to_list (Term.get_args lit) in
      assert (3 = List.length args);
      if not ((List.nth args 1) = (List.nth args 2))
      then (* collect the literal *)
        found_predicates := TSet.add lit !found_predicates;
      (* found lit; report *)
      true
    )
    (* not a positive $next lit *)
    else false
  in
  (* get positive $next lits from clause; save it if there are none *)
  let process_clause clause =
    try (* if the lit is found, it's already in a set *)
      ignore (Clause.find mark_lit clause)
    with Not_found -> (* no $next, save a clause *)
      problem_clauses := clause::!problem_clauses
  in
  (* apply to all clauses *)
  List.iter process_clause clauses;
  (* make a reduced version of problem by lifting the UC axioms *)
  let reduce_problem () =
    (* set from unsat cores *)
    let uc_set = CSet.of_list !problem_clauses in
    (* filter those clauses that were obtained by pred_elim or similar *)
    let filter_pred_elim clause =
      let tstp_source = Clause.get_tstp_source clause in
      match tstp_source with
      | Clause.TSTP_inference_record ((Clause.Resolution_lifted _), _)
      | Clause.TSTP_inference_record ((Clause.Resolution _), _) 
      | Clause.TSTP_inference_record ((Clause.Global_subsumption _), _)
      | Clause.TSTP_inference_record (Clause.Unflattening, _) ->     

        (* out_str ("Filter out clause "^(Clause.to_string clause)); *)
        true
      | _ ->
        (* out_str ("Keep clause "^(Clause.to_string clause)); *)
        false
    in
    (* get all the parents *)
    let parents = TstpProof.get_parents_filter filter_pred_elim !problem_clauses in
    (* make set of parents *)
    let parents_set = CSet.of_list parents in
    (* get the difference *)
    let orig_set = CSet.diff parents_set uc_set in
    (* return list of those clauses *)
    CSet.elements orig_set
  in
  (* return the sets and problem clauses *)
  !found_predicates, (reduce_problem ())

(*--------------------------------------*)
(* UMC relation and assumptions support *)
(*--------------------------------------*)

(* all the predicates in the form $$next(Cj,s,s') in the current relation *)
let current_next_rel_pred_ref = ref TSet.empty
(* all the Cj from $$next(Cj,s,s') in the current relation *)
let current_next_rel_const_ref = ref TSet.empty
(* all the Cj from $$init(Cj,s) in the current relation *)
let current_init_rel_const_ref = ref TSet.empty

(* all the predicates in the form $$next(Cj,s,s') that ever been in the relation *)
let total_next_rel_pred_ref = ref TSet.empty
(* all the predicates in the form $$next(Cj,s,s') that ever been in the relation *)
let total_init_rel_const_ref = ref TSet.empty

(* aux set that contains all state constants that are NOT in the current TR *)
let bound_states_ref = ref TSet.empty

(* print current and total transition relation size *)
let print_transition_relation_size () =
  let cur_size = string_of_int (TSet.cardinal !current_next_rel_pred_ref) in
  let tot_size = string_of_int (TSet.cardinal !total_next_rel_pred_ref) in
  dbg D_trace (lazy ("TR size: current "^cur_size^", total "^tot_size))

(* true if reduced TR is ground *)
let is_ground_tr () =
  (* right now it is values 1 and 3 of a flag *)
  (!current_options.bmc1_ucm_reduced_relation_type mod 2) = 1

(* initialise with bounds from 0 to b-2 *)
let init_bound_set bound =
  (* create bound const *)
  let get_const b = create_state_term (pred b) in
  (* create all bounds in [0,b-1) *)
  let rec fill_bounds b =
    if b = 0
    then TSet.empty
    else TSet.add (get_const b) (fill_bounds (pred b))
  in
  dbg D_tr_set (lazy ("Init states between 0 and "^(string_of_int bound)));
  (* save that set *)
  bound_states_ref := fill_bounds bound

(* clear current relation *)
let clear_current_rel_proper bound =
  current_next_rel_pred_ref := TSet.empty;
  current_next_rel_const_ref := TSet.empty;
  current_init_rel_const_ref := TSet.empty;
  init_bound_set bound;
  ()

(* do NOT clear TR if we use ground N *)
let clear_current_rel bound =
  if not (is_ground_tr ())
  then clear_current_rel_proper bound

(*--------------------------------------*)
(* reduced relations support            *)
(*--------------------------------------*)

(* helper: get Cj by N(Cj,_,_) or I(Cj,_) *)
let get_index_const term =
  (* get arguments *)
  let args = Term.arg_to_list (Term.get_args term) in
  (* take the first arg *)
  let i_const = List.nth args 0 in
  (* return it *)
  i_const

(*--------------------------------------*)
(* reduced init relation support        *)
(*--------------------------------------*)

(* create a clauses {$$init(Cj,s_N),full_rel,~bound_N} *)
(* using prepared set of Cj and N *)
let create_short_init_rel bound =
  (* create TSTS -- for now *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom bound) in
  (* create guards *)
  let bound_guard = add_compl_lit (create_bound_atom bound) in
  let short_guard = create_short_r_guard () in
  let guards = [short_guard; bound_guard] in
  (* create s_N *)
  let state = create_state_term bound in
  (* create axiom for c_j *)
  let create_axiom const =
    (* create atom *)
    let init_atom = create_init_atom const state in
    (* create clause *)
    let clause = create_clause tstp_source (init_atom::guards) in
    (* return that clause *)
    clause
  in
  (* create folder *)
  let folder const accum = (create_axiom const)::accum in
  (* create the clauses depending on the flag value *)
  let clauses =
    match !current_options.bmc1_ucm_init_mode with
    | 0 -> [create_axiom (rel_index_var ())]
    | 1 -> TSet.fold folder !total_init_rel_const_ref []
    | 2 -> TSet.fold folder !current_init_rel_const_ref []
    | _ -> failwith "Option --bmc1_ucm_init_mode can have only values 0, 1 or 2"
  in
  (* return created clauses *)
  clauses

(* fill in the const set by a set of clauses *)
let populate_init_set clauses =
  (* return true if clause contains full_rel guard *)
  let with_full_rel clause =
    let guard = create_full_r_guard () in
    (* return true if list of lits contain guard *)
    let rec has_guard lits =
      match lits with
      | [] -> false
      | hd::tl ->
        if hd == guard
        then true
        else has_guard tl
    in
    (* try to find guard in lits *)
    has_guard (Clause.get_lits clause)
  in
  (* add a const from a clause (if exists) to accum *)
  let extract_init_const_from_clause accum clause =
    (* add const to set if pred is init predicate *)
    let get_const set pred =
      if (Term.get_top_symb pred) == Symbol.symb_ver_init
      then TSet.add (get_index_const pred) set
      else set
    in
    (* apply to all literals *)
    Clause.fold get_const accum clause
  in
  (* keep only clauses with full_rel *)
  let full_rel_clauses = List.filter with_full_rel clauses in
  (* apply concept extraction to all clauses from UC *)
  let init_const_set = List.fold_left extract_init_const_from_clause TSet.empty full_rel_clauses in
  (* setup init const-related refs *)
  current_init_rel_const_ref := init_const_set;
  total_init_rel_const_ref := TSet.union init_const_set !total_init_rel_const_ref;
  (* that's it *)
  ()

(* aggregate that fills in the Cj constants from UC and add new init clauses to the others *)
let add_new_init_clauses source_clauses bound other_clauses =
  populate_init_set source_clauses;
  let init_clauses = create_short_init_rel bound in
  List.rev_append init_clauses other_clauses

(*--------------------------------------*)
(* reduced transition relation support  *)
(*--------------------------------------*)

(* check whether UCs contain new N transitions *)
let has_new_next_segments unsat_cores =
  let folder cl uc = List.rev_append (UnsatCore.get_clauses uc) cl in
  let clauses = List.fold_left folder [] unsat_cores in
  let used_tr,_ = get_next_predicates_from_clauses clauses in
  let new_tr = TSet.diff used_tr !current_next_rel_pred_ref in
  (* new elements in TR means set is not empty *)
  not (TSet.is_empty new_tr)

(* helper: get s' by N(Cj,_,s') *)
let get_final_state_const term =
  (* get arguments *)
  let args = Term.arg_to_list (Term.get_args term) in
  (* sanity check *)
  assert (3 = List.length args);
  (* take the last arg *)
  let s_const = List.nth args 2 in
  (* return it *)
  s_const

(* helper: get set of all Cj for which N(Cj,_,b') *)
(* are in the TR where b' is the maximal bound *)
(* smaller than given one *)
let get_last_bound_consts max_bound =
  (* folder to get the set of N(_,_,state) *)
  let get_max_next state term set =
    if (get_final_state_const term) == state
    then TSet.add term set
    else set
  in
  (* get all N(_,_,state) from registered ones *)
  let get_all_next state =
    TSet.fold (get_max_next state) !current_next_rel_pred_ref TSet.empty
  in
  (* get set of N(_,_,state) for maximal state *)
  let rec get_set_max_next bound =
    match bound with
    | -1 -> failwith "Empty short relation in UCM"
    | b ->
      (* create state for bound *)
      let state = create_state_term b in
      (* get the set of N(_,_,b) *)
      let set = get_all_next state in
      (* return the non-empty set *)
      if TSet.is_empty set
      then get_set_max_next (pred bound)
      else set
  in
  (* get the set of maximal bounds *)
  let bset = get_set_max_next max_bound in
  (* folder that extract Cj *)
  let index_const_folder term accum =
    TSet.add (get_index_const term) accum
  in
  (* fold that set *)
  TSet.fold index_const_folder bset TSet.empty

(* register predicate N(Cj,s,s') to participate in the current relation *)
let register_next_predicate term =
  (* get Cj of term *)
  let const = get_index_const term in
  (* register term in current relation *)
  current_next_rel_pred_ref := TSet.add term !current_next_rel_pred_ref;
  (* register term in total relation *)
  total_next_rel_pred_ref := TSet.add term !total_next_rel_pred_ref;
  (* register Cj in current set *)
  current_next_rel_const_ref := TSet.add const !current_next_rel_const_ref;
  (* remove the final state of the transition from the set *)
  let final = get_final_state_const term in
  dbg D_tr_set (lazy ("Remove state "^(Term.to_string final)));
  bound_states_ref := TSet.remove final !bound_states_ref;
  (* that's it *)
  ()

(* get clause corresponding to N(Cj,s,s') predicate wrt flags *)
let create_tr_clause predicate bound =
  (* first we register predicate that is going to be used in the TR *)
  register_next_predicate predicate;
  (* create TSTP *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom bound) in
  (* determine which literals will be in the clause *)
  let lits =
    if is_ground_tr ()
    then [predicate]
    else (
      (* create bound guard: the clause live during this bound only *)
      let bound_guard = add_compl_lit (create_bound_atom bound) in
      (* create non-full unsat core guard *)
      let short_r_guard = create_short_r_guard () in
      (* all of them are the literals of a new clause *)
      [ predicate; short_r_guard; bound_guard ]
    )
  in
  (* create the clause *)
  let clause = create_clause tstp_source lits in
  (* return that clause *)
  clause

(*--------------------------------------*)
(* UMC unsat_no_assumptions support     *)
(*--------------------------------------*)

(* return true if there is no path between init and ~p in TR *)
let no_path_in_tr () =
  (* there is no path if some states between init and p are not in the N *)
  not (TSet.is_empty !bound_states_ref)

(*--------------------------------------*)
(* UMC negative assumptions support     *)
(*--------------------------------------*)

(* get ~N(Cj,X,Y) for all Cj not in current relation *)
let get_default_grounded_assumptions need_neg =
  (* get set of Cj not is current relation *)
  let non_current_consts = TSet.diff (get_next_state_consts ()) !current_next_rel_const_ref in
  (* create ~N(Cj,X,Y) out of Cj *)
  let get_neg_pred const =
    (* get 2 vars *)
    let v_x = term_x0 state_type in
    let v_y = term_x1 state_type in
    (* create predicate *)
    let atom = create_next_atom const v_x v_y in
    (* return negated one if requested *)
    if need_neg
    then add_compl_lit atom
    else atom
  in
  (* folder that adds ground lit of const to accum *)
  let folder const accum =
    try
      let pred = get_neg_pred const in
      let ground_lit = add_term_db (Term.get_grounding_lit pred) in
      ground_lit :: accum
    with (* if no grounding available -- nothing to do *)
    | Term.Grounding_undef ->
      accum
  in
  (* fold the whole thing *)
  TSet.fold folder non_current_consts []

(* get ~N(Cj,X,Y) for all Cj not in current relation *)
let get_grounded_neg_assumptions () =
  get_default_grounded_assumptions true

(* get N(Cj,X,Y) for all Cj not in current relation *)
let get_grounded_pos_assumptions () =
  get_default_grounded_assumptions false


(* get ~N(Cj,s,s') s.t. they had been in rel but not in current one *)
let get_negated_prev_rel () =
  (* folder *)
  let folder pred accum = (add_compl_lit pred) :: accum in
  let non_current_preds = TSet.diff !total_next_rel_pred_ref !current_next_rel_pred_ref in
  (* fold the whole thing *)
  TSet.fold folder non_current_preds []

(* get all ~N(Cj,_,_) assumptions *)
let get_negative_assumptions () =
  let neg_prev = get_negated_prev_rel () in
  let grounded = get_grounded_neg_assumptions () in
  let total = List.rev_append grounded neg_prev in
  (* return both sets *)
  total

(*--------------------------------------*)
(* support for chain addition           *)
(*--------------------------------------*)

(* create an axiom {$$next(c,b,{b-1})} *)
let create_pure_path_axiom next_const bound =
  (* create path atom for a given bound *)
  let create_path_atom b =
    let state_term_b = create_state_term b in
    let state_term_pred_b = create_state_term (pred b) in
    create_next_atom next_const state_term_b state_term_pred_b
  in
  let path_atom_b = create_path_atom bound in
  (* create a clause with such bound *)
  create_tr_clause path_atom_b bound

(* add a new constant to the model *)
let add_new_next_const next_const bound =
  (* get a list of next statements for a given bound *)
  let rec add_next_for_bound b accum =
    if b = 0
    then accum
    else add_next_for_bound (pred b) ((create_pure_path_axiom next_const b)::accum)
  in
  add_next_for_bound bound []

(* get all Cj used in $$nextState(Cj,s,s') from predicates *)
let next_constants_from_unsat_predicates predicates =
  (* get a literal Cj from atom $$next(Cj,s,s') *)
  let fetch_next_predicate atom result =
    TSet.add (get_index_const atom) result
  in
  (* apply to all predicates *)
  TSet.fold fetch_next_predicate predicates TSet.empty

(* make (unconditional) step from given bound using known constants *)
let create_next_clauses_for_bound constants bound =
  (* create a single axiom for bound *)
  let step_folder lit accum = (create_pure_path_axiom lit bound)::accum in
  (* apply to all constants *)
  TSet.fold step_folder constants []

(* create chained TR from the unsat core wrt bound, making a step if necessary *)
let get_chained_next_predicates unsat_core_clauses bound =
  (* all the split predicates *)
  let next_constants_from_unsat clauses =
    (* get all the next predicates *)
    let next_predicates,_ = get_next_predicates_from_clauses clauses in
    next_constants_from_unsat_predicates next_predicates
  in
  (* create a concept chain if a concept is not there yet *)
  let add_chain next_const accum =
    if TSet.mem next_const !current_next_rel_const_ref
    then accum
    else List.rev_append (add_new_next_const next_const bound) accum
  in
  (* body of the method *)
  let uc_constants = next_constants_from_unsat unsat_core_clauses in
  (* all consts from the UC  *)
  let next_clauses = TSet.fold add_chain uc_constants [] in
  (* add init clauses to them *)
  let clauses = add_new_init_clauses unsat_core_clauses bound next_clauses in
  (* return clauses *)
  clauses

exception No_path_in_tr

(* get {$$nextState(Cj,s,s')} clauses out of predicates from unsat core *)
let get_next_predicates unsat_core_clauses bound =
  (* create an axiom out of a given predicate *)
  let path_axiom predicate accum =
    (create_tr_clause predicate bound) :: accum
  in
  (* get all the next predicates *)
  let next_predicates, reduced_problem = get_next_predicates_from_clauses unsat_core_clauses in
  (* apply to all predicates *)
  let next_clauses = TSet.fold path_axiom next_predicates [] in
  (* check whether there is path from s_0 to s_{b-2} in the current TR *)
  (* if so, raise exception *)
  if (no_path_in_tr ())
  then raise No_path_in_tr;
  (* add init clauses to them *)
  let clauses = add_new_init_clauses unsat_core_clauses bound next_clauses in
  (* return clauses *)
  clauses, reduced_problem

let current_sat_next_tr_ref = ref TSet.empty

let prepare_model_tr () =
  current_sat_next_tr_ref := TSet.empty

let no_changes_in_next set =
  let union = TSet.union set !current_sat_next_tr_ref in
  TSet.equal union !current_sat_next_tr_ref

(* get {$$nextState(Cj,s,s')} clauses out of predicates from unsat core *)
let get_tr_predicates model bound =
  (* create map between state consts bN-> b{N-1} *)
  let rec create_bounds_map map b =
    if b = 0
    then
      map
    else (
      let state_term_b = create_state_term b in
      let state_term_pred_b = create_state_term (pred b) in
      create_bounds_map (TMap.add state_term_b state_term_pred_b map) (pred b)
    )
  in
  (* such a map for all known bounds *)
  let bounds_map = create_bounds_map TMap.empty bound in
  (* for a given atom $$next(Cj,b,b') return true if b = bN and b' = b{N-1} *)
  let is_normal_next_atom next_atom =
    let lits = Term.arg_to_list (Term.get_args next_atom) in
    let b = List.nth lits 1 in
    let b' = List.nth lits 2 in
    if (TMap.mem b bounds_map) && b' = (TMap.find b bounds_map)
    then
      true
    else (
      out_str ("Ignore abnornal next: "^(Term.to_string next_atom));
      false
    )
  in
  (* get all literals of the form ~$next or ~$init that are selected in the model *)
  let get_next_tr_lits model =

    (* get all the selected literals in the active clauses *)
    let sel_lit_set = get_model_lits model ~use_clause:(fun c -> true) ~apply_grounding:false in

    (* get all the selected literals *)
    let sel_lits = TSet.elements sel_lit_set in
    (* filter ~$init ~$next lits *)
    let is_next_lit lit =
      let symb = Term.get_top_symb (Term.get_atom lit) in
      (Term.is_neg_lit lit) && (symb = Symbol.symb_ver_next_state)
    in
    dbg D_tr_from_model (lazy ("All selected lits:\n"^(Term.term_list_to_string sel_lits)));
    (* get next consts *)
    let neg_next_lits = List.filter is_next_lit sel_lits in
    let next_lits = List.map add_compl_lit neg_next_lits in
    next_lits
  in
  (* make next chains *)
  let get_next_chain next_const_set =
    (* create an atom $$next(c,b,{b-1}) *)
    let create_pure_path_atom next_const b =
      let state_term_b = create_state_term b in
      let state_term_pred_b = create_state_term (pred b) in
      create_next_atom next_const state_term_b state_term_pred_b
    in
    (* add a new constant to the model *)
    let chain_for_next_const next_const max_bound =
      (* get a list of next statements for a given bound *)
      let rec add_next_for_bound b accum =
        if b = 0
        then accum
        else add_next_for_bound (pred b) ((create_pure_path_atom next_const b)::accum)
      in
      add_next_for_bound max_bound []
    in
    (* create a concept chain if a concept is not there yet *)
    let add_chain next_const accum =
      (* if TSet.mem next_const !current_next_rel_const_ref *)
      (* then accum                                         *)
      (* else                                               *)
        List.rev_append (chain_for_next_const next_const bound) accum
    in
    (* all consts from the model  *)
    let next_atoms = TSet.fold add_chain next_const_set [] in
    (* return atoms *)
    next_atoms
  in
  (* get all the TR predicates *)
  let next_tr_lits = get_next_tr_lits model in
  (* separate ground and non-round ones *)
  let ground_lits, other_lits = List.partition Term.is_ground next_tr_lits in
  (* keep only normal ground ones *)
  let normal_ground_lits = List.filter is_normal_next_atom ground_lits in
  (* get consts out of non-ground lits *)
  let next_consts = List.map get_index_const other_lits in
  let next_const_set = TSet.of_list next_consts in
  (* get chains corresponding to those consts *)
  let next_tr_chain_atoms = get_next_chain next_const_set in
  (* add ground ones *)
  let all_next_atoms = List.rev_append normal_ground_lits next_tr_chain_atoms in
  let next_atoms_set = TSet.of_list all_next_atoms in
  (* TODO: factor out *)
  next_atoms_set

let get_tr_from_model model next_atoms_set bound =
  (* create a clause from given literal, using global bound *)
  (* TODO: unify with create_tr_clause *)
  let create_short_tr_clause predicate =
    (* create TSTP *)
    let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom bound) in
    (* determine which literals will be in the clause *)
    let lits =
      (* create bound guard: the clause live during this bound only *)
      let bound_guard = add_compl_lit (create_bound_atom bound) in
      (* create non-full unsat core guard *)
      let short_r_guard = create_short_r_guard () in
      (* all of them are the literals of a new clause *)
      [ predicate; short_r_guard; bound_guard ]
    in
    (* create the clause *)
    let clause = create_clause tstp_source lits in
    (* return that clause *)
    clause
  in
  (* create an axiom out of a given negated predicate *)
  let path_axiom predicate accum  =
    (create_short_tr_clause predicate) :: accum
  in
  current_sat_next_tr_ref := TSet.union next_atoms_set !current_sat_next_tr_ref;
  (* universal init atom $init(X,const_bN) *)
  let init_lit = create_init_atom (rel_index_var ()) (create_state_term bound) in
  (* apply to all predicates *)
  let tr_clauses = TSet.fold path_axiom (TSet.add init_lit next_atoms_set) [] in
  dbg D_tr_from_model (lazy ("Reduced TR clauses:\n"^(Clause.clause_list_to_string tr_clauses)));
  (* return clauses *)
  tr_clauses

(* general method to choose between chained and non-chained versions *)
let get_next_clauses_from_unsat_core unsat_core_clauses bound =
  (* options 2 and 3 are chained *)
  (* if (!current_options.bmc1_ucm_reduced_relation_type > 1)  *)
  (* then get_chained_next_predicates unsat_core_clauses bound *)
  (* else  *)
    get_next_predicates unsat_core_clauses bound


(* extend next bound *)
let extend_one_bound_full bound =
  (* use the same TSTP FORNOW *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom bound) in
  let next_lit = Bmc1Common.create_path_atom bound in
  let short_guard = create_short_r_guard () in
  let bound_guard = add_compl_lit (create_bound_atom bound) in
  let next_clause = create_clause tstp_source [next_lit; short_guard; bound_guard] in
  (* add full init *)
  let init_lit = Bmc1Common.create_init_atom_b bound in
  let init_clause = create_clause tstp_source [init_lit; short_guard; bound_guard] in
  (* return both clauses *)
  [init_clause; next_clause]

(* extend next bound using consts from the unsat core *)
let extend_one_bound_consts all_uc bound =
  (* determine the set of consts *)
  let consts =
    if all_uc
    then !current_next_rel_const_ref
    else get_last_bound_consts bound
  in
  (* we don't need to add init clauses here, as *)
  (* they were added via get_next_clauses_from_unsat_core *)
  create_next_clauses_for_bound consts bound

let extend_one_bound bound =
  let new_clauses_for_bound =
    (* check it we performing chain extention *)
    if !current_options.bmc1_ucm_reduced_relation_type = 3
    then (* reduced relation with all consts *)
      extend_one_bound_consts true bound
    else (* get extend axioms corresponding to the extend mode *)
      match !current_options.bmc1_ucm_extend_mode with
      | 0 -> (* full bound *)
        extend_one_bound_full bound
      | 1 -> (* short value with all consts *)
        extend_one_bound_consts true bound
      | 2 -> (* short value with last bound consts *)
        extend_one_bound_consts false bound
      | _ -> failwith "--bmc1_ucm_extend_mode can only have 0, 1 or 2 values"
  in
  (* return total clauses *)
  new_clauses_for_bound


(*--------------------------------------*)
(* UMC used symbols and atoms           *)
(*--------------------------------------*)

(* clear saved assumptions *)
let clear_saved_assumptions () =
  unsat_core_participated_atoms := TSet.empty;
  unsat_core_participated_symbols := SSet.empty

(* remember assumptions from unsat cores *)
let add_used_assumptions assumptions =
  let folder accum lit = TSet.add (Term.get_atom lit) accum in
  unsat_core_participated_atoms := List.fold_left folder !unsat_core_participated_atoms assumptions;
  let symb_folder atom accum = SSet.add (Term.get_top_symb atom) accum in
  unsat_core_participated_symbols := TSet.fold symb_folder !unsat_core_participated_atoms !unsat_core_participated_symbols

(*--------------------------------------*)
(* recover from SAT: fix the model and increase the relations with full Rs *)
(*--------------------------------------*)

let get_terminating_symb_set () = 
  (* calculate the set of consts used in transition *)
  let all_consts = TSet.union !current_next_rel_const_ref !current_init_rel_const_ref in

  (* get the set of symbols that terminate cone calculation *)
  let terminating_symb_set = AigClausifier.get_remainder all_consts in
  dbg D_cone_full (lazy ("terminating_symb_set: "^(list_to_string Symbol.to_string (SSet.elements terminating_symb_set) ",")^"\n"));
  terminating_symb_set
  
let clause_has_pred_from pred_set clause = 
  let all_preds = Clause.find_all_pred ~is_relevant_pred:(fun _ _-> true) clause in 
  (SSet.exists  (fun pred -> SSet.mem pred pred_set) all_preds)


(* return true if clause is used to generate model *)
let use_clause_for_model terminating_symb_set clause =
(*
  (* only active clauses are useful *)
  if not (Clause.get_ps_in_active clause)
  then false
  (* use all clauses if use cones *)
  else 
*)
(*
    if (!current_options.bmc1_ucm_cone_mode != BMC1_Ucm_Cone_Mode_None)
    then true
  (* skip clauses without $$next *)
    else  
*)
(* KK *)
   (* if not (Clause.has_next_state clause)
  then   false 
  else *) 
(
    dbg D_model (lazy (" active_clause "^(Clause.to_string clause)
		      (*  ^" sel lit "^(Term.to_string (Clause.inst_get_sel_lit clause))*)));
 true

(*
    let exists_aig_input_symb clause =
      Clause.exists AigClausifier.aig_is_input_pred clause
    in
    (* useful are clauses with an input var *)
    exists_aig_input_symb clause

*)

(*
 let exists_aig_input_or_latch_symb clause = 
   Clause.exists 
     (fun lit -> 
       (AigClausifier.aig_is_input_pred lit) ||  (AigClausifier.aig_is_latch_pred lit) 
		 ) clause 
 in   
 (*if ( SSet.mem (Term.get_top_symb (Term.get_atom (Clause.inst_get_sel_lit clause))) !AigClausifier.input_vars_ref *)
 if (exists_aig_input_or_latch_symb clause)
 then true
 else false
*)


(*----KK *)
(*
    if 
      (
       (clause_has_pred_from terminating_symb_set clause) 
     (* ||
       (clause_has_pred_from !cone_exclude_symbs clause)
*)
       )
    then false
    else
 
      ( (* KK for cone tests *)
	dbg D_model (lazy (" active_clause "^(Clause.to_string clause)
			   ^" sel lit "^(Term.to_string (Clause.inst_get_sel_lit clause))));
	true*)
(*
    (* return true if the negation of lit is a NEXT from the short model *)
    let is_in_next_rel lit =
      TSet.mem (add_compl_lit lit) !current_next_rel_pred_ref
    in
    (* walker *)
    let rec has_rel_in_list lits =
      match lits with
      | [] -> false
      | hd::tl ->
        if is_in_next_rel hd
        then true
        else has_rel_in_list tl
    in
    (* check all literals of a clause *)
    has_rel_in_list (Clause.get_lits clause)
*)
    )

(* get all the selected literals from the model *)
let get_model_literals model =

  let terminating_symb_set = get_terminating_symb_set () in

  let use_clause clause = use_clause_for_model terminating_symb_set clause in

  (* get grounded selected lits *)

  let sel_lit_set = get_model_lits model ~use_clause ~apply_grounding:true in

  (* remove previously chosen ~full_rel *)
  let sel_lit_set' = TSet.remove (create_short_r_assumption ()) sel_lit_set in
  (* return those literals separated using path_rel *)
  let (_, non_tr_lits') = TSet.partition Term.is_next_state_lit sel_lit_set' in
  (* remove literals which atoms participated in the unsat core from model *)
  let lit_non_participated_p lit =
    let atom = Term.get_atom lit in
    let symb = Term.get_top_symb atom in
    if (!current_options.bmc1_ucm_relax_model > 2)
    then (* 3 and 4 are looking for symbols *)
      not (SSet.mem symb !unsat_core_participated_symbols)
    else (* 1 and 2 are looking for atoms *)
      not (TSet.mem atom !unsat_core_participated_atoms)
  in
  let non_tr_lits =
    if (!current_options.bmc1_ucm_relax_model > 0)
    (* relax model by filtering out appropriate literals *)
    then TSet.filter lit_non_participated_p non_tr_lits'
    else non_tr_lits'
  in
  (* make list out of set *)
  let set_folder lit accum = lit::accum in
  let result = TSet.fold set_folder non_tr_lits [] in
  result

(*--------------------------*)
(* get lemma out of unsat core *)
(*--------------------------*)
let create_ground_lemma_from_uc unsat_core =
  let assumptions = UnsatCore.get_assumptions unsat_core in
  let uc_clauses = UnsatCore.get_clauses unsat_core in

  (* split assumptions into constants and predicates. *)
  (* All assumptions from pred list will be in lemma (negated) *)
  let is_real_assumption term = Term.is_const_term (Term.get_atom term) in
  let const_assumptions, pred_assumptions = List.partition is_real_assumption assumptions in

  (* create the list of negated consts. They are [~]full_rel and iProver_boundN (positive) *)
  let guard_list = List.rev_map add_compl_lit const_assumptions in
  let guard_set' = TSet.of_list guard_list in
  (* in some cases [~]full_rel is not there *)
  (* (e.g., when we have both guards in a problem) *)
  (* so add both of the to be sure *)
  let fg = create_full_r_guard () in
  let sg = create_short_r_guard () in
  let guard_set = TSet.add fg (TSet.add sg guard_set') in

  (* get list of $init(Cj,s) and $next(Cj,s,s') from the list of clauses *)
  (* where they appear positively in clauses (probably with guard_list) *)
  let get_init_next_pred clauses =
    let is_init_or_next_predicate term =
      let symb = Term.get_top_symb term in
      (symb == Symbol.symb_ver_next_state)
      || (symb == Symbol.symb_ver_init)
    in
    (* add $init/$next predicate from a clause to set if *)
    (* the clause correspond to a pattern above *)
    let add_pred_to_set set clause =
      (* make a set of clause args *)
      let arg_set = TSet.of_list (Clause.get_lits clause) in
      (* remove all guards *)
      let essential_set = TSet.diff arg_set guard_set in
      (* check that the set is a singleton $init of $next atom *)
      if ((TSet.cardinal essential_set) = 1)
         && (TSet.exists is_init_or_next_predicate essential_set)
      then (* add that atom to the set *)
        let pred = TSet.choose essential_set in
        TSet.add pred set
      else (* nothing to add *)
        set
    in
    (* get all the predicates from clauses *)
    let gathering = List.fold_left add_pred_to_set TSet.empty clauses in
    (* return the list of predicates *)
    TSet.elements gathering
  in

  (* function to check whether the clause is {[~]($$property($$constBn))} *)
  let is_property_unit_clause clause =
    (* return true for the unit clause *)
    let is_unit_clause cl = (Clause.length cl) = 1 in
    (* get the 1st literal of the clause *)
    let first_lit cl =
      let lits = Clause.get_lits cl in
      List.hd lits
    in
    (* return true if atom is $$property *)
    let is_prop_atom lit =
      let atom = Term.get_atom lit in
      let symb = Term.get_top_symb atom in
      symb == Symbol.symb_ver_property
    in
    (* body of a checker *)
    if is_unit_clause clause
    then is_prop_atom (first_lit clause)
    else false
  in

  (* split all UC clauses into property unit ones and others *)
  let prop_clauses, other_clauses = List.partition is_property_unit_clause uc_clauses in

  (* collect the set of [~]property(s_n) that present in the UC *)
  let prop_predicates =
    (* folder to add $property literal to the list of them *)
    let extract_property_lit clause = (List.hd (Clause.get_lits clause)) in
    let prop_lits = List.rev_map extract_property_lit prop_clauses in
    dbg D_lemmas (lazy ("$$property literals to add: "^(Term.term_list_to_string prop_lits)));
    prop_lits
  in

  (* extract init and next predicates from non-property clauses *)
  let init_next_predicates = get_init_next_pred other_clauses in

  (* put all predicates together *)
  let lemma_preds_direct = List.rev_append pred_assumptions
    (List.rev_append init_next_predicates prop_predicates)
  in
  (* negate predicates *)
  let lemma_preds = List.rev_map add_compl_lit lemma_preds_direct in
  dbg D_lemmas (lazy ("lemma literals: "^(Term.term_list_to_string lemma_preds)));

  (* create ground lemma *)
  let ground_lemma =
    (* Create TSTP source FIXME!! for now *)
    let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom 0) in
    let lemma_importance = get_bc_imp_inh_shift !current_options BCI_bmc1_lemma in
    create_clause tstp_source ~bc_imp_inh:lemma_importance lemma_preds
  in
  ground_lemma

let create_lemma_from_uc unsat_core =
  (* get ground lemma first *)
  let ground_lemma = create_ground_lemma_from_uc unsat_core in
  (* out_str ("ground lemma: "^(Clause.to_string ground_lemma)); *)
  (* anti-skolemize lemma *)
  (* get all state constants *)
  let state_consts =
    (* get all state consts in the term *)
    let rec get_state_consts_term accum term =
      match Term.get_atom term with
      | Term.Fun(sym, args, _) ->
        if (Symbol.get_val_type_def sym) == state_type
        then (* found it *)
          SSet.add sym accum
        else (* go through args recursively *)
          List.fold_left get_state_consts_term accum (Term.arg_to_list args)
      | _ -> accum
    in
    (* get all state terms in clause *)
    let get_state_consts_clause clause = Clause.fold get_state_consts_term SSet.empty clause in
    (* take all consts from the ground lemma *)
    get_state_consts_clause ground_lemma
  in
  (*   out_str ("symbol: "(Symbol.to_string const));    *)
  (*   (* test whether the term is of a state type *)   *)
  (*   let is_state_type_term symbol =                  *)
  (*     (Symbol.get_val_type_def symbol) == state_type *)
  (*   in                                               *)
  (*   is_state_type_term const                         *)
  (* in                                                 *)
  let lemma = Bmc1InitTarget.anti_skolemise_clause_consts ground_lemma state_consts in
  (* out_str ("lemma: "^(Clause.to_string lemma)); *)

  let lemma_importance = get_bc_imp_inh_shift !current_options BCI_bmc1_lemma in
  Clause.assign_bc_imp_inh lemma lemma_importance;
  lemma

(* return true if lemma is larger than the given limit *)
let too_long_lemma lemma =
  (Clause.length lemma) > !current_options.bmc1_ucm_max_lemma_size

(* get lemma by UNSAT core. Rerurn list of 1 or 0 lemmas *)
let get_lemma_by_uc unsat_core =
  (* get lemma *)
  let lemma = create_lemma_from_uc unsat_core in
  (* check length *)
  if (too_long_lemma lemma)
  then []
  else (
    out_str ("lemma created: "^(Clause.to_string lemma));
    [lemma]
  )

(*--------------------------*)
(* reduce problem wrt unsat core *)
(*--------------------------*)

(* keep full_rel for the symb version of cones *)
let full_rel_ref = ref (create_full_rel ())
let full_rel_clauses_ref = ref []
let full_cone = ref None

(* internal func to use with symb cones *)
let is_relevant_symb symb =
	(not (symb == Symbol.symb_ver_next_state)) && (not (SSet.mem symb !cone_exclude_symbs))

(* set full_rel using given set of clauses *)
let set_full_rel clauses =
  (* TODO!! switch always ON for now*)
  (* if (!current_options.bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_Symb) *)
  (* then                                                                                                   *)
    let is_relevant_symb symb = (not (symb == Symbol.symb_ver_next_state)) in
    (full_rel_clauses_ref := clauses;
(*
     dbg_env D_cone 
       (fun () -> 
	 dbg D_cone (lazy ("-----input clauses ---------\n "));
	 out_str (Clause.clause_list_to_string clauses);
	 dbg D_cone (lazy ("-----end input clauses ---------\n "));
       );
*)
    full_rel_ref := create_full_rel_cl_list ~is_relevant_symb clauses;
    (* build cone while we're here *)
    let depth_0_symb_set = SSet.of_list [Symbol.symb_ver_property] in
    let cone = Cone_symb.compute_cone !full_rel_ref ~terminating_symb_set:SSet.empty ~depth_0_symb_set in
    full_cone := Some cone;
    dbg D_cone_symb (lazy ("Cone depth: "^(string_of_int (Cone_symb.get_cone_max_depth cone))));
    )

(* get the cone using the symb dependencies *)
let get_cone_symb () =

(*
  (* calculate the set of consts used in transition *)
  let all_consts = TSet.union !current_next_rel_const_ref !current_init_rel_const_ref in

  (* get the set of symbols that terminate cone calculation *)
  let terminating_symb_set = AigClausifier.get_remainder all_consts in
*)

  let terminating_symb_set = get_terminating_symb_set () in
  
  (* starting point *)
  let start = SSet.of_list [Symbol.symb_ver_property] in

  let get_filtered_cluases exclude_cl_symbs clauses =
    let f clause = 
      let all_preds =
	Clause.find_all_pred ~is_relevant_pred:(fun _ _-> true) clause in 
      not
	(
	 (SSet.exists (fun pred -> SSet.mem pred exclude_cl_symbs) all_preds)
	   &&
	 (SSet.mem Symbol.symb_ver_next_state all_preds)	 
        
	)
    in
    let new_clauses = List.filter f clauses in 
    new_clauses
  in
  let filtered_clauses = get_filtered_cluases terminating_symb_set !full_rel_clauses_ref in

  
  let new_full_rel =  create_full_rel_cl_list ~is_relevant_symb filtered_clauses in

  (* create cone symbol *)
  let cone_symb = compute_cone new_full_rel ~terminating_symb_set ~depth_0_symb_set:start in
  let depth = -1 in

(*
  let cone_clauses = CSet.elements (Cone_symb.get_cone_clauses cone_symb ~depth) in

  dbg_env D_cone_symb
    (fun () -> 

      dbg D_cone_symb (lazy ("  \n"));
      dbg D_cone_symb (lazy ("---- start cone ---- \n"));

      dbg D_cone_symb_full (lazy ("!cone_exclude_symbs: "^(list_to_string Symbol.to_string (SSet.elements !cone_exclude_symbs) ",")^"\n"));

      dbg D_cone_symb (lazy ("size of terminating_symb_set: "^(string_of_int (SSet.cardinal terminating_symb_set))));


      dbg_env D_cone_symb_full (fun () ->  Cone_symb.out_cone ~symbs:true  ~clauses:true ~stats:true cone_symb);

      dbg_env D_cone_symb (fun () ->  Cone_symb.out_cone ~symbs:false  ~clauses:false ~stats:true cone_symb);

      dbg D_cone_symb (lazy ("---- end cone ------ \n"));
    );
*)

  (* get cone's clauses *)
(*
  let prep_cone_clauses = Preprocess.preprocess ~is_eq_problem:false cone_clauses in
  dbg D_cone (lazy ("preprocessed clauses: "^(string_of_int (List.length prep_cone_clauses))^"\n"));

  let new_is_relevant_symb symb =
    (is_relevant_symb symb) && (not (SSet.mem symb terminating_symb_set)) in

  let new_full_rel = create_full_rel_cl_list ~is_relevant_symb:new_is_relevant_symb prep_cone_clauses in
  let new_cone =  compute_cone new_full_rel ~reach_bound:0 ~terminating_symb_set ~depth_0_symb_set:start in
  let new_cone_clauses = CSet.elements new_cone.cone_clauses in
  dbg D_cone (lazy ("new cone clauses: "^(string_of_int (List.length new_cone_clauses))^"\n"));
  *)

  (* return clauses *)
 (* new_cone_clauses *)
(*
  filtered_clauses (* Without cones !!!*)
*)

  


(*  let copy_cone = List.map Clause.copy_clause cone in *)
  let prep_cone_clauses = get_prep_cone_clauses cone_symb depth in
  prep_cone_clauses

(*
  cone_clauses
*)

let get_reduced_problem () =
  (* get cone for property *)
  let prop_cone = AigClausifier.get_property_cone () in

  dbg D_aig_cones (lazy ("---------------prop_cones:\n\n"));
  dbg D_aig_cones (lazy ("prop_cone:\n"^(Clause.clause_list_to_string prop_cone)));

  (* add cone for a single const cj into accum *)

  let add_latch_cone cj accum =
    let cone = AigClausifier.get_latch_cone cj in

    dbg D_aig_cones (lazy ("\n\ncone for "^(Term.to_string cj)^":\n"^(Clause.clause_list_to_string cone)));

    CSet.union (CSet.of_list cone) accum
  in

  (* calculate the set of consts used in transition *)
  let all_consts = TSet.union !current_next_rel_const_ref !current_init_rel_const_ref in
  (* gather cones for all cj on the reduces TR *)

  (* gather cones for all cj on the reduces TR *)
  let problem_cone_set = TSet.fold add_latch_cone all_consts (CSet.of_list prop_cone) in

  let problem_cone = CSet.elements problem_cone_set in
  dbg D_aig_cones (lazy ("\n\ncone_size: "^(string_of_int (List.length problem_cone)^"\n")));
  dbg D_aig_cones (lazy ("\n\nfull cone: "^(Clause.clause_list_to_string problem_cone)));


(*
  let prep_cone = Preprocess.preprocess ~is_eq_problem:false problem_cone in
  dbg D_cone (lazy ("preprocessed clauses: "^(string_of_int (List.length prep_cone))^"\n"));

  prep_cone
*)

  (* return that cone *)
  problem_cone 

(* get problem cone corresponding to a set of used TR*)
let get_aig_pass_cone () =
  let all_consts = !current_next_rel_const_ref in

 (* use -1 as depth to force checking all reachable latches*)
  let cone = AigClausifier.get_cone all_consts (-1) in
 
(*  let cone = AigClausifier.get_cone all_consts bound in *)

  dbg D_aig_cones (lazy ("\n\n"));

  dbg D_aig_cones_full  (lazy ("full cone:\n"^(Clause.clause_list_to_string cone)));

  dbg D_aig_cones  (lazy ("full cone size: "^(string_of_int (List.length cone))^"\n"));

(* TODO: check where clauses are came from and why some are dead!!!*)

(*  List.iter (fun c -> Clause.assign_is_dead false c) cone; 

(*  let copy_cone = List.map Clause.copy_clause cone in *)
  let prep_cone = Preprocess.preprocess ~is_eq_problem:false (* copy_cone*) cone in
  
  dbg D_aig_cones  (lazy ("preprocessed cone size: "^(string_of_int (List.length prep_cone))^"\n"));
  dbg D_aig_cones_full (lazy ("preprocessed cone: "^(Clause.clause_list_to_string prep_cone)^"\n"));
  prep_cone
*)

  cone

(* get problem cone corresponding to given depth *)
let get_aig_restricted_cone depth =
  (* use empty set for Cj to ensure all latches *)
  let cone = AigClausifier.get_cone TSet.empty depth in
  dbg D_aig_cones_full (lazy ("full cone:\n"^(Clause.clause_list_to_string cone)));
  cone

let get_symb_restricted_cone depth =
  let cone =
    match !full_cone with
    | Some c -> c
    | None -> failwith "Symb cone not initialised"
  in  
(*
  let cone_set = (Cone_symb.get_cone_clauses cone ~depth) in
  let cone_clauses = CSet.elements cone_set in
  
  dbg D_cone_symb_full  (lazy ("cone:\n"^(Clause.clause_list_to_string cone_clauses)));
  dbg D_cone_symb  (lazy ("cone depth: "^(string_of_int depth)^" max_cone_depth:"^(string_of_int (Cone_symb.get_cone_max_depth cone))^"\n"));
  dbg D_cone_symb  (lazy ("cone size: "^(string_of_int (List.length cone_clauses))^"\n"));  
*)

  let prep_cone_clauses = get_prep_cone_clauses cone depth in
  prep_cone_clauses

(*
  cone_clauses
*)

(*-------------------------------------------*)
(* restricted depth cone interface           *)
(*-------------------------------------------*)

(* get cone restricted by given depth depending on a method *)
let get_restricted_cone_proper depth =
  (* out_str ("CONE for dept "^(string_of_int depth)^" is requested"); *)
  match !current_options.bmc1_ucm_layered_model with
  | BMC1_Ucm_Cone_Mode_None -> failwith "Don't use _None value of restricted cone"
  | BMC1_Ucm_Cone_Mode_AIG -> get_aig_restricted_cone depth
  | BMC1_Ucm_Cone_Mode_Symb -> get_symb_restricted_cone depth
  | BMC1_Ucm_Cone_Mode_UC -> failwith "Don't use _UC value of restricted cone"

(* cache for the cones of a certain depth *)
let depth_to_cone_map = ref IntMap.empty

let get_restricted_cone depth =
  if depth < 0
  then get_restricted_cone_proper depth
  else
    try
      IntMap.find depth !depth_to_cone_map
    with Not_found ->
      let cone = get_restricted_cone_proper depth in
      depth_to_cone_map := IntMap.add depth cone !depth_to_cone_map;
      cone


(* check whether the given depth reach maximal for the problem *)
let max_depth_reached depth =
  (* negative depth means unlimited cone, so max is reached *)
  if depth < 0 then true else
  match !current_options.bmc1_ucm_layered_model with
  | BMC1_Ucm_Cone_Mode_None -> true
  | BMC1_Ucm_Cone_Mode_UC -> failwith "Don't use _UC value of restricted cone"
  | BMC1_Ucm_Cone_Mode_AIG -> AigOptimiser.pass_problem_depth depth
  | BMC1_Ucm_Cone_Mode_Symb ->
    let cone =
      match !full_cone with
      | Some c -> c
      | None -> failwith "Symb cone not initialised"
    in
      (Cone_symb.get_cone_max_depth cone) <= depth
