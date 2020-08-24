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
open Statistics
open Logic_interface
open Bmc1Common


(* Clauses to be instantiated for each bound *)
let bound_instantiate_axioms = ref []

(* in next state pre-instantiation strategy separated next state clauses *)
let next_state_clauses = ref []

(* in state  pre-instantiation strategy separated state clauses *)
let state_clauses = ref []

(* Skolem constants occurring in  [$$reachableState(sK)] clauses *)
let reach_bound_skolem_constants = ref []

(* clauses which contain reach_bound_skolem_constants/ used in state pre-inst *)
let has_reach_bound_skolem_constants = ref []

(*------------------------------------------------------*)
(* bound-related assumptions *)
(*------------------------------------------------------*)

(* Assumptions for previous bounds *)
let invalid_bound_assumptions = ref []

(* last bound for which assumptions before that are fileld in *)
let last_valid_bound = ref 0

(* get list [$$iProver_bound{b}, ~$$iProver_bound{b-1}, ..., ~$$iProver_bound{0}] *)
(* NB: here we assume that bound grown monotonically *)
let get_current_bound_assumptions bound =
  (* generate single positive bound assumption *)
  let get_pos_assumption b = create_bound_atom b in
  (* generate single negative bound assumption *)
  let get_neg_assumption b = add_compl_lit (get_pos_assumption b) in
  (* update invalid bound assumptions with !bound(b) *)
  let update_invalid_bound_assumptions bound =
    (* generate unconditionally ~$$iProver_bound{b} for b in [low,high) *)
    let rec gen_assumptions accum low high =
      if low = high
      then (* nothing to do *)
        accum
      else (* add ~low to the accum *)
        gen_assumptions ((get_neg_assumption low)::accum) (succ low) high
    in
    (* unconditionally update all *)
    let update_assumptions b =
      (* generate those for missing elements in invalid_bound_assumptions *)
      let new_assumptions = gen_assumptions !invalid_bound_assumptions !last_valid_bound b in
      (* copy those back to the list *)
      invalid_bound_assumptions := new_assumptions;
      (* update the last bound *)
      last_valid_bound := b
    in
    (* do those only if necessary *)
    if ( bound > !last_valid_bound )
    then update_assumptions bound
  in

  (* main body *)

  (* update assumptions for smaller bounds if necessary *)
  update_invalid_bound_assumptions bound;
  (* return all those and a positive one *)
  (get_pos_assumption bound) :: !invalid_bound_assumptions



(*------------------------------------------------------*)
(********** Path axioms **********)

(* Create path axioms for all bounds down to [lbound] *)
let rec create_path_axioms accum lbound = function

    (* No more axioms if state is less than lower bound *)
  | b when b <= lbound -> accum

  | b ->
      (* Create path axiom for bound *)
      let path_axiom_b = create_path_axiom b in

      (* Add path axioms for lesser states *)
      create_path_axioms (path_axiom_b :: accum) lbound (pred b)

let pre_instantiate_next_state_clause state_p state_q clause =
  let lits = Clause.get_literals clause in
  (* TSAR: TODO: partition *)
  let next_list, rest_lits =
    List.partition Term.is_next_state_lit lits in
  let next_cl_lit =
    match next_list
    with
      [lit] -> lit
    | _ -> failwith "bmc1Axioms: exactly one next atom is expected"
  in
  (* next_cl_lit = ~$$nextState(VarCurr,VarNext) *)
  let next_cl_atom = Term.get_atom next_cl_lit in

  (* Create state term for state *)
  let state_term_p = create_state_term state_p in

  (* Create state term for preceding state *)
  let state_term_q = create_state_term state_q in

  (* nex_gr_atom = $$nextState($$constBq,$$constBp) *)
  (* TsarFIXME!! What to do *)
  let next_gr_atom = create_auto_path_atom state_term_p state_term_q in
  let tstp_source =
    Clause.tstp_source_axiom_bmc1
      (Clause.TSTP_bmc1_path_axiom state_q)
  in
  let next_gr_cl =
    create_clause tstp_source [next_gr_atom ]
  in
  try
    let mgu = Unif.unify_bterms (1, next_gr_atom) (2, next_cl_atom) in
    let tstp_source =
      Clause.tstp_source_resolution
	[clause; next_gr_cl] [next_cl_lit; next_gr_atom]
    in
    let resolved =
      create_clause tstp_source
	(Clause.normalise_blitlist_list term_db_ref mgu [(2, rest_lits)])
    in
    resolved
  with
    Unif.Unification_failed ->
      failwith "bmc1Axioms: next_state atoms should be unifyable"

(* pre_instantiate for all bounds down to [lbound] *)
let rec pre_instantiate_next_state_clause_lu accum clause lbound = function
    (* No more axioms if state is less than lower bound *)
  | b when b <= lbound -> accum
  | b ->
      let pre_inst_cl = pre_instantiate_next_state_clause (pred b) b clause in
      pre_instantiate_next_state_clause_lu (pre_inst_cl:: accum) clause lbound (pred b)

let pre_instantiate_all_next_state_clauses lbound ubound =
  List.fold_left
    (fun rest cl ->
      let pre_inst_cls =
	pre_instantiate_next_state_clause_lu [] cl lbound ubound in
      pre_inst_cls@rest
    )
    [] !next_state_clauses

(*-----KK: incr grounding --------------*)

(* change grounding map in prop_solver_exchnage when we extend bounds *)

let change_gr_by_map_state state_term = 
  let cur_gr_by_map = Prop_solver_exchange.get_gr_by_map () in
  let new_gr_by_map = SMap.add Symbol.symb_ver_state_type state_term cur_gr_by_map in 
  Prop_solver_exchange.change_gr_by_map new_gr_by_map



(*------- reachable state pre-instantiation vesion -----------*)

(* separte clauses containing $$reachableState *)
(* we assume that all such occurrrences are of the form $$reachableState(sK) *)
(* then sparate clauses containing sK constants; these will be replaced by bounds at each iteration *)

exception Reach_Not_Supported

(* also removes $$reachableState *)

let separate_reach_constants clauses =
  let has_reachable_state clause =
    (List.exists Term.is_reachable_state_lit (Clause.get_literals clause)) in

  let (reach_clauses, no_reach_cl) = List.partition has_reachable_state clauses in
  try
    let extract_reach_sk cl =
      (match (Clause.get_skolem_bound_clause cl)
      with
      | Some sK -> sK
      | None -> raise Reach_Not_Supported
      )
    in
    let reach_sk_constants = List.map extract_reach_sk reach_clauses in
    reach_bound_skolem_constants := reach_sk_constants;
    (reach_clauses, no_reach_cl)
  with
    Reach_Not_Supported ->
      failwith
	"bmc1Axioms: reachable clauses are supported only of
	the form $$reachableState(sK)"

(*------this extra is not used yet---------------------*)

let has_bound_sk_constant_cl cl =
  (* assume the size of reach_bound_skolem_constants is small, usually 1 *)
  let has_bound_sk_constant_lit lit =
    (List.exists
       (fun sk -> Term.is_subterm sk lit) !reach_bound_skolem_constants)
  in
  Clause.exists has_bound_sk_constant_lit cl

(*
  let separate_reachable_state_clauses clauses =
(* Clause.has_next_state is not assigned at this point so need to explicitely search for next state *)

  let (_reach_clauses, no_reach_cl) = separate_reach_constants clauses in

  let (has_bound_sk_constant, no_bound_sk_no_reach) =
  List.partition has_bound_sk_constant_cl no_reach_cl
  in
  has_reach_bound_skolem_constants:= has_bound_sk_constant;
(* debug *)
(*
  out_str "\n\n----- separated has_bound_sk_constant ---------------\n";
  out_str ((Clause.clause_list_to_tptp has_bound_sk_constant)^"\n\n");
  out_str "\n--------------------\n";
 *)
(* debug *)
  no_reach_cl
 *)

(* pre_inst_reachable_state_clauses is applied to all clauses (in iprover.ml), after adding all other axioms *)

let pre_inst_reachable_state_clauses b clauses =

  (* $$constBb *)
  let state_term_b = create_state_term b in

  (* Create literal for current bound, i.e. ~$$iProver_bound{b} *)
  let bound_literal = add_compl_lit (create_bound_atom b) in
  let pre_inst_reachable_cl cl sk_term =
    let cl_to_replace =
      begin
	try
	  (* out_str "TSTP_bmc1_reachable_sk_replacement Has SK \n ";
	     (Format.printf "%a@." (TstpProof.pp_clause_with_source false) cl);*)
	  match (Clause.get_tstp_source cl) with
	  | Clause.TSTP_inference_record (Clause.TSTP_bmc1_reachable_sk_replacement (_old_bound) ,[parent_cl]) ->
	      (* if this clause got already sK replaced on an old bound, then get the parent and replace in the parent *)
	      (*			out_str ("TSTP_bmc1_reachable_sk_replacement Parent: "^(Clause.to_string parent_cl)^"\n");*)
	      Some (parent_cl)
	  | _ ->
	      if (has_bound_sk_constant_cl cl)
	      then
		(
		 if (not (Clause.is_ground cl))
		 then (* if clause is not ground more cre should be take since state preinstantiation modifies the clause and history gets also modified *)
		   failwith ("pre_inst_reachable_state_clauses only works with ground clauses")
		 else
		   Some (cl)
		)
	      else None
	with _ -> failwith (" History was not defined for: "^(Clause.to_string cl)^"\n ")

      end
    in
    let final_cl =
      (match cl_to_replace with
      | Some cl ->
	  begin
	    let repl_cl_lits =
	      Clause.replace_subterm term_db_ref sk_term state_term_b (get_lits cl) in
	    let tstp_source =
	      Clause.TSTP_inference_record (Clause.TSTP_bmc1_reachable_sk_replacement (b) ,[cl])
	    in
	    let pre_inst_cl =
	      create_clause	tstp_source  (bound_literal:: (repl_cl_lits))
	    in
	    (* out_str ("\n\n Replaced:  "^(Clause.to_string pre_inst_cl)^"\n");
	       out_str ("Replaced history: \n");
	       (Format.printf "%a@." (TstpProof.pp_clause_with_source false) pre_inst_cl);
	     *)
	    Prop_solver_exchange.add_clause_to_solver pre_inst_cl;
	    pre_inst_cl
	  end
      | None -> cl
      )
    in
    final_cl
  in
  let pre_inst_all_sk_consts_cl cl =
    List.fold_left
      (fun rest sk ->
	(
	 (pre_inst_reachable_cl cl sk):: rest
	)
      )
      [] !reach_bound_skolem_constants
  in
  let pre_instantiated_all_cl =
    List.fold_left
      (fun rest cl ->
	(
	 (pre_inst_all_sk_consts_cl cl)@rest
	)
      )
      [] clauses
  in
  (*	out_str ("\n\n pre_instantiated_all_cl \n\n "^(Clause.clause_list_to_string pre_instantiated_all_cl) ^"\n\n");*)
  pre_instantiated_all_cl

(********** Clock pattern **********)

(* Get sign of clock in given state *)
let sign_of_clock_pattern state pattern =
  (List.nth pattern (state mod List.length pattern)) = 1

(* Create axiom for given clock in given state *)
let create_clock_axiom state clock pattern =

  (* Create term for state *)
  let state_term = create_state_term state in

  (* Create atom for clock *)
  let clock_atom =
    add_fun_term clock [ state_term ]
  in

  (* Create literal for clock *)
  let clock_literal =

    (* Sign of clock in state *)
    if sign_of_clock_pattern state pattern then

      (* Clock literal is positive *)
      clock_atom

    else

      (* Clock literal is negative *)
      add_compl_lit clock_atom

  in
  let tstp_source =
    Clause.tstp_source_axiom_bmc1
      (Clause.TSTP_bmc1_clock_axiom (state, clock, pattern))
  in
  (* Create clock axiom *)
  let clock_axiom =
    create_clause tstp_source  [ clock_literal ]
  in

  (* Return clock axiom *)
  clock_axiom

(* Create axiom for given clock in given state *)
let create_clock_axioms state clock pattern accum =

  (* Create clock axiom *)
  let clock_axiom = create_clock_axiom state clock pattern in

  (* Return clock axiom in accumulator *)
  clock_axiom :: accum

(* Create clock axioms for all clocks in state *)
let create_all_clock_axioms state =

  (* Iterate clocks *)
  Symbol.Map.fold
    (create_clock_axioms state)
    !Parser_types.clock_map
    [ ]

(* Create clock axioms for all clock and all states up to bound *)
let rec create_all_clock_axioms_for_states accum bound_i ubound =

  (* Reached upper bound? *)
  if bound_i > ubound then

    (* Return clock axioms *)
    accum

  else

    (* Add clock axioms for next states *)
    create_all_clock_axioms_for_states
      ((create_all_clock_axioms bound_i) @ accum)
      (succ bound_i)
      ubound

(********** Address axioms (TODO) **********)

(* This is untested and unfinished. Currently, address axioms are
   extracted from the problem and instantiated, see below *)

(*

(* Create address domain axioms

   ~address(A1) | ~address(A2) | ~addressDiff(A1, A2, B) | A1 = A2 |
   address_val(A1, B) | address_val(A2, B)

   ~address(A1) | ~address(A2) | ~addressDiff(A1, A2, B) | A1 = A2 |
   ~address_val(A1, B) | ~address_val(A2, B)

 *)
  let create_address_domain_axiom () =

(* Common literals of both axioms:

   ~address(A1) | ~address(A2) | ~addressDiff(A1, A2, B) | A1 = A2
 *)
  let axiom_head =
  [ create_compl_lit (create_address_atom term_x0);
  create_compl_lit (create_address_atom term_x1);
  create_compl_lit (create_address_diff_atom term_x0 term_x1 term_x2);
  create_typed_equation address_type term_x0 term_x1 ]
  in

(* Atom address_val(A1,B) *)
  let address_val_1_atom =
  create_address_val_atom term_x0 term_x2
  in

(* Atom address_val(A2,B) *)
  let address_val_2_atom =
  create_address_val_atom term_x1 term_x2
  in

(* First axiom:

   address_val(A1, B) | address_val(A1, B) | { axiom_head }
 *)
  let address_domain_axiom_1 =
  address_val_1_atom ::
  address_val_2_atom ::
  axiom_head
  in

(* Second axiom:

   ~address_val(A1, B) | ~address_val(A1, B) | { axiom_head }
 *)
  let address_domain_axiom_2 =
  (create_compl_lit address_val_1_atom) ::
  (create_compl_lit address_val_2_atom) ::
  axiom_head
  in

(* Return the two address_domain axioms *)
  [ address_domain_axiom_1; address_domain_axiom_2 ]

(* Accumulate atoms addressDiff(A1,A2,bitindex{n}) from n to 0 *)
  let rec create_address_diff_disjunction accum = function

(* Terminate after all atoms have been generated *)
  | i when i < 0 -> accum

(* Create axiom for current i *)
  | i ->

(* Create atom addressDiff(X0,X1,bitindex{i}) *)
  let address_diff_disjunct =
  create_address_diff_atom term_x0 term_x1 (create_bitindex_term i)
  in

(* Recursively create remaining atoms *)
  create_address_diff_disjunction
  (address_diff_disjunct :: accum)
  (pred i)

(* Create address_diff axiom with the maximal bit width of all
   addresses:

   cnf(address_diff, axiom, addressDiff(A1, A2, bitindex0) | ... |
   addressDiff(A1, A2, bitindex { N -1 })).

 *)
  let create_address_domain_axiom address_max_width =

(* Create literals for axiom *)
  let address_domain_axiom_literals =
  create_address_diff_disjunction [ ] address_max_width
  in

(* Create axiom *)
  let address_domain_axiom =
  Clause.normalise term_db (Clause.create address_domain_axiom_literals)
  in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom address_domain_axiom; *)
  Clause.assign_tstp_source_axiom_bmc1 address_domain_axiom;

(* Return axiom *)
  address_domain_axiom

(* Return address definition for given constant bit vector b000 as

   b000(X0) <=> addressVal(b000_address_term, X0)

   clausified to

   b000(X0) | ~addressVal(b000_address_term, X0)
   ~b000(X0) | addressVal(b000_address_term, X0)

   and sort axiom

   address(b000_address_term)

   TODO: optimise clausification, might be sufficient to generate
   first clause only in some cases

 *)
  let create_constant_address_definition accum bitvector_symbol =

(* Get name of bit vector symbol *)
  let bitvector_name = Symbol.get_name bitvector_symbol in

(* Create address term for constant bit vector: b000_address_term *)
  let address_term =
  create_skolem_term constant_address_term_format address_type bitvector_name
  in

(* Create atom for address: addressVal(b000_address_term, X0) *)
  let address_val_atom =
  create_address_val_atom address_term term_x0
  in

(* Create atom for bitvector with variable: b000(X0) *)
  let bitvector_atom =
  create_bitvector_atom bitvector_name term_x0
  in

(* Create atom for address term: address(b000_address_term) *)
  let address_atom =
  create_address_atom address_term
  in

(* Create first axiom *)
  let constant_address_definition_1 =
  Clause.normalise
  term_db
  (Clause.create
  [ create_compl_lit bitvector_atom; address_val_atom ])
  in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom constant_address_definition_1; *)
  Clause.assign_tstp_source_axiom_bmc1 constant_address_definition_1;

(* Create second axiom *)
  let constant_address_definition_2 =
  Clause.normalise
  term_db
  (Clause.create
  [ bitvector_atom; create_compl_lit address_val_atom ])
  in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom constant_address_definition_2; *)
  Clause.assign_tstp_source_axiom_bmc1 constant_address_definition_2;

(* Create third axiom *)
  let constant_address_definition_3 =
  Clause.normalise
  term_db
  (Clause.create [ address_atom ])
  in

(* Assign clause history as axiom *)
(* Clause.assign_axiom_history Clause.BMC1_Axiom constant_address_definition_3; *)
  Clause.assign_tstp_source_axiom_bmc1 constant_address_definition_3;

(* Return clauses in accumulator *)
  constant_address_definition_1 ::
  constant_address_definition_2 ::
  constant_address_definition_3 ::
  accum
 *)

(********** Instantiate clauses for bound **********)

(* Is the term or one if its subterms to be instantiated for each bound? *)
let rec is_bound_term = function

    (* No instantiation for variables *)
  | Term.Var _ -> false

	(* Symbol is a state constant *)
  | Term.Fun (symb, args, _)
    when Symbol.Map.mem symb !Parser_types.state_constant_map ->

      (* Only instantiate the state constant for bound 1 *)
      Symbol.Map.find symb !Parser_types.state_constant_map = 1

	(* Symbol has a base name *)
  | Term.Fun (symb, args, _)
    when Symbol.Map.mem symb !Parser_types.address_base_name_map ->

      (* Get base name of symbol *)
      let base_name =
	Symbol.Map.find symb !Parser_types.address_base_name_map
      in

      (

       try

	 (* Only instantiate if base name of symbol has a "1"
	    appended? *)
	 String.sub
	   (Symbol.get_name symb)
	   (String.length base_name)
	   ((String.length (Symbol.get_name symb)) -
	      (String.length base_name))
	   = "1"

       with Invalid_argument _ ->

	 failwith
	   (Format.sprintf
	      ("Bmc1Axioms.is_bound_term: name of symbol %s " ^^
	       "and base name %s do not match")
	      (Symbol.get_name symb)
	      base_name)

      )

	(* Check if term has a subterm to be instantiated *)
  | Term.Fun (_, args, _) ->

      (* Is one of the subterms a term to be instantiated? *)
      List.exists (fun b -> b) (Term.arg_map_list is_bound_term args)

(* Is the clause to be instantiated at each bound? *)
let is_bound_clause clause =
  List.exists
    (fun b -> b)
    (List.map is_bound_term (Clause.get_literals clause))

(* Instantiate term for current bound *)
let rec bound_instantiate_term bound = function

    (* No instantiation for variables *)
  | Term.Var _ as t -> t

	(* Symbol is a state constant *)
  | Term.Fun (symb, args, _) as t
    when Symbol.Map.mem symb !Parser_types.state_constant_map ->

      if

	(* Only replace state constant for bound 1 *)
	Symbol.Map.find symb !Parser_types.state_constant_map = 1

      then

	(* Replace term with state term for current bound *)
	create_state_term bound

      else

	(* Keep state constant for bounds other than 1*)
	t

	  (* Symbol has a base name *)
  | Term.Fun (symb, args, _) as t
    when Symbol.Map.mem symb !Parser_types.address_base_name_map ->

      (* Get base name of symbol *)
      let base_name =
	Symbol.Map.find symb !Parser_types.address_base_name_map
      in

      if

	(
	 try

	   (* Base name of symbol has "1" appended? *)
	   String.sub
	     (Symbol.get_name symb)
	     (String.length base_name)
	     ((String.length (Symbol.get_name symb)) -
		(String.length base_name))
	     = "1"

	 with Invalid_argument _ ->

	   failwith
	     (Format.sprintf
		("Bmc1Axioms.bound_instantiate_term: name of symbol %s " ^^
		 "and base name %s do not match")
		(Symbol.get_name symb)
		base_name)

	)

      then

	(* Append bound to base name *)
	let term_bound_name = base_name ^ (string_of_int bound) in

	(* Replace term with term for current bound *)
	create_constant_term term_bound_name address_type

      else

	(* Keep term for bounds other than 1 *)
	t

	  (* Instantiate withing functional term *)
  | Term.Fun (symb, args, _) ->

      (* Instantiate arguments of term *)
      let args' =
	Term.arg_map_list (bound_instantiate_term bound) args
      in

      (* Return term with instantiated arguments *)
      add_fun_term symb	args'


(* Instantiate clause for current bound *)
let bound_instantiate_clause bound clause =

  (* Get literals of clause *)
  let clause_literals =
    Clause.get_literals clause
  in

  (* Instantiate terms in literals for current bound *)
  let clause_literals' =
    List.map (bound_instantiate_term bound) clause_literals
  in
  let tstp_source =
    (Clause.TSTP_inference_record (Clause.TSTP_bmc1_instantiated_clause (bound), [clause]))
  in
  (* Create new clause of instantiated literals *)
  let instantiated_clause =

    create_clause	tstp_source	clause_literals'
  in

  (* Return instantiated clause *)
  instantiated_clause

(* Instantiate clauses for current bound *)
let instantiate_bound_axioms bound clauses =

  (* Instantiate each clause *)
  List.map
    (bound_instantiate_clause bound)
    clauses

(* Return two list of clauses, the first containing the clauses to be
   instantiated at each bound, the second the clauses valid for each
   bound *)
let separate_bound_axioms clauses =
  List.partition is_bound_clause clauses

(* separate clauses containing $$nextState, used in next state preinstantiation strategy *)
(* first are the nextState clauses *)
let separate_next_state_clauses clauses =
  (* Clause.has_next_state is not assigned at this point so need to explicitely search for next state *)

  let has_next_state clause =
    (List.exists Term.is_next_state_lit (Clause.get_literals clause)) in
  List.partition has_next_state clauses


(*--------- state pre-instantiation --------------------*)
(* separate clauses containing state vars for state pre-instantiation *)
let separate_state_clauses clauses =
  let is_state_var t =
    match t with
    | Term.Fun _ -> false
    | Term.Var (v, _) -> ((Var.get_type v) == Symbol.symb_ver_state_type)
  in
  let has_state_var clause =
    let res = (List.exists (Term.exists is_state_var) (Clause.get_literals clause))
    in
    (*out_str ((Clause.to_string clause)^" has state: "^(string_of_bool res)); *)
    res
  in
  List.partition has_state_var clauses

(* clause is eligible for preinstantiation if it contains only occurrences of the same state var *)
(* for some reason Next(B1, B2) got splitted sP(B1,B2) which resulted in clauses with two state vars even when Next is eliminated....*)
exception Not_Elig
let pre_instantiate_state_var_eligible clause =
  let test_elig prev lit =
    let f prev curr_v =
      if (Var.get_type curr_v) == Symbol.symb_ver_state_type
      then
	(match prev with
	| Some(prev_var) ->
	    (if prev_var == curr_v
	    then prev
	    else raise Not_Elig)
	| None -> Some(curr_v)
	)
      else
	prev
    in
    Term.fold_left_var f prev lit
  in
  try
    let _ = Clause.fold test_elig None clause in
    true
  with
  | Not_Elig -> false

let pre_instantiate_state_var_clauses bound clauses =
  let state_term = create_state_term bound in
  let var_map = SMap.add Symbol.symb_ver_state_type state_term SMap.empty in
  let f c =
    if pre_instantiate_state_var_eligible c
    then
      if (Clause.is_ground c)
      then
	( Prop_solver_exchange.add_clause_to_solver c;
	  c
	 )
      else
	begin
	  let lits = Clause.get_literals c in
	  let new_lits = List.map (Subst.replace_vars None var_map) lits in
          let tstp_source = Clause.tstp_source_instantiation c [] in
	  let new_clause = create_clause tstp_source  new_lits in
	  Prop_solver_exchange.add_clause_to_solver new_clause;
	  new_clause
	end
    else
      c
  in
  List.map f clauses

let pre_instantiate_state_var_clauses_range lower_bound upper_bound clauses =
  assert (lower_bound <= upper_bound);
  let rec f inst_cls l u =
    if u < l
    then inst_cls
    else
      let new_inst_cl = (pre_instantiate_state_var_clauses l clauses)@inst_cls in
      let new_l = l +1 in
      f new_inst_cl new_l u
  in f [] lower_bound upper_bound

(********** Utility functions **********)

(* Formatter for output, None if uninitialised. Use
   get_bmc1_dump_formatter as access function *)
let bmc1_dump_formatter = ref None

(* Return a formatter for writing into the file given in the option
   -- bmc1_dump_file *)
let get_bmc1_dump_formatter () =

  match !bmc1_dump_formatter with

    (* Return formatter if initialised *)
  | Some f -> f

	(* Formatter is not initialised *)
  | None ->

      (* Filename from options *)
      let dump_filename =

	(* Get value of option *)
	match val_of_override !current_options.bmc1_dump_file with

	  (* Default is stdout *)
	| None -> "-"

	      (* Use filename if non-default *)
	| Some f -> f

      in

      (* Formatter of channel of opened file *)
      let new_bmc1_dump_formatter =

	try

	  (* Open formatter writing into file *)
	  formatter_of_filename false dump_filename

	with

	  (* Catch errors when opening *)
	| Sys_error _ ->
	    failwith
	      (Format.sprintf
		 "Could not open file %s for output"
		 dump_filename)

      in

      (* Save formatter *)
      bmc1_dump_formatter := Some new_bmc1_dump_formatter;

      (* Return formatter *)
      new_bmc1_dump_formatter

(********** Top functions **********)

(* Return clauses with assumptions for given bound *)

let get_bound_assumptions bound =

  (* Get atom iProver_bound{n} *)
  let bound_literal = create_bound_atom bound in
  let tstp_source = Clause.tstp_source_assumption	in
  let assumption =
    create_clause tstp_source  [ bound_literal ] in
  (* Return unit clause containing positive bound atom *)
  [ assumption ]

(* reachable state pre-instantiation *)

(* First version (currently implemented) *)
(* replace *)
(*  $$reachableState(sK)                                             *)
(* ~$$reachableState(X) -> X = $$constB0 \/..\/X = $$constBn         *)
(* by  replace sK = $$constB0 \/..\/ sK = $$constBn                  *)

(*Second version (not fully implemented)*)

(* 1) find clauses of the type [$$reachbleState(sK)], *)
(*    and collect all such sK constants (usually 1)  *)
(* 2) separate all clauses containing these sK constants *)
(* 3) with each bound replace sK in 2) with the bound term and add to the clauses set *)
(* !!! reachable state pre - instantiation
   Does not work at the moment because transitional addresses can occur in
   2) then they are not unrolled since the clauses are separated *)

(*let _= out_warning "!!!!: pre_instantiate_next_state_flag add to options!!!\n"*)

(* Create clock axioms in the range [from_bound, to_bound] *)
let get_clock_axioms from_bound to_bound =
  create_all_clock_axioms_for_states [] from_bound to_bound

(* Instantiate axioms for next bound

   TODO: iterate all bounds between cur_bound and next_bound if
   increases are in greater steps *)
let get_bound_axioms_instantiated next_bound =
  instantiate_bound_axioms next_bound !bound_instantiate_axioms

(* tsar: create {$$init(b0)|~iProver0} and {~$$property(b0)} predicates *)
let get_init_property_axioms () =
  (* create property axiom *)
  let property_axiom = create_neg_property_axiom 0 in
  (* create init axiom *)
  let init_axiom = create_guarded_init_axiom 0 in
  (* deadlock doesn't need property axiom *)
  let axioms =
    if !current_options.bmc1_deadlock
    then [init_axiom]
    else [init_axiom; property_axiom]
  in
  (* return these axioms *)
  axioms

(*-----------------------------------------*)
(* Axioms for bound 0 *)
(*-----------------------------------------*)
let init_bound all_clauses =

(* moved to bmc1_loop.ml

  let state_term_0 = create_state_term 0 in
  change_gr_by_map_state state_term_0;
*)
  (* Separate axioms to be instantiated for each bound *)
  let bound_instantiate_axioms_of_clauses, clauses' =
    separate_bound_axioms all_clauses
  in
  if val_of_override !current_options.bmc1_verbose
  then out_str ("\n \n bound_instantiate_axioms_of_clauses: \n "
		^(Clause.clause_list_to_string bound_instantiate_axioms_of_clauses)^"\n\n");
  let clauses'' =
    if !current_options.bmc1_pre_inst_next_state
    then
      (let cl_next_state, cl_rest = separate_next_state_clauses clauses' in
      next_state_clauses:= cl_next_state;
      cl_rest
      )
    else clauses'
  in
  (* !current_options.bmc1_pre_inst_state moved to iprover.ml *)
  let clauses =
    if !current_options.bmc1_pre_inst_reach_state
    then
      let (reach, no_reach) = separate_reach_constants clauses''
      in

      out_str "\n\n----- Reach clauses  ---------------\n";
      out_str ((Clause.clause_list_to_tptp reach)^"\n\n");
      out_str "\n--------------------\n";

      no_reach
	(*      separate_reachable_state_clauses clauses'' *)
    else
      clauses''
  in
  (* Create clock axiom *)
  let clock_axioms = get_clock_axioms 0 0 in

  (* tsar: create $$init(b0) and ~$$property(b0) predicates *)
  let init_property_axioms = get_init_property_axioms() in

  (* Return created path axioms and reachable state axiom *)
  let bound_axioms =
    init_property_axioms @ clock_axioms
  in

  (* Save axioms to be instantiated *)
  bound_instantiate_axioms := bound_instantiate_axioms_of_clauses;

  (* Output only in verbose mode *)
  if val_of_override !current_options.bmc1_verbose then

    (

     (* Output axioms to be instantiated for each bound *)
     Format.printf
       "%s axioms to be instantiated at bounds@." (current_task_name());

     List.iter
       (fun c -> Format.printf "%s@." (Clause.to_string c))
       !bound_instantiate_axioms;

     (* Output created axioms for bound *)
     Format.printf
       "%s axioms for initial bound 0@." (current_task_name());

     List.iter
       (function c -> Format.printf "%s@." (Clause.to_string c))
       bound_axioms;

     (* Output other axioms for bound *)
     (* Format.printf                                               *)
     (*   "@.other axioms for initial bound 0@.";                   *)

     (* List.iter                                                   *)
     (*   (function c -> Format.printf "%s@." (Clause.to_string c)) *)
     (*   clauses;                                                  *)

    Format.printf "@."

    );

  (* Return created axioms for bound *)
  bound_axioms, clauses

(*-------------------------------------------------*)
(* Increment bound from given bound *)
(*-------------------------------------------------*)
let increment_bound cur_bound next_bound lemmas =

  (*currently only next_bound should be cur_bound + 1 *)
  assert (next_bound - cur_bound = 1);

(* moved to bmc1_loop.ml
  let next_state_term = create_state_term next_bound in
  change_gr_by_map_state next_state_term;
*)

  (* change grounding of state type to next_bound *)

  (*
    let next_bound_state_term = create_state_term next_bound in
    out_str ("state term: "^(Term.to_string next_bound_state_term)^("\n"));
    Prop_solver_exchange.assign_new_grounding Symbol.symb_ver_state_type next_bound_state_term;
   *)

  (* tsar: add init and property axioms *)
  (* clause {$$init(next) | ~bound(next)} *)
  let init_clause = create_guarded_init_axiom next_bound in
  (* if necessary, add {$$property(next)} *)
  let init_property_axioms =
    if lemmas && (next_bound > 0)
    then [init_clause; (create_property_axiom next_bound)]
    else if (next_bound > 0)
    then [init_clause]
    else []
  in

  (* Create path axioms for all states between next bound and current
     bound *)
  let path_axioms' =
    if !current_options.bmc1_pre_inst_next_state
    then
      pre_instantiate_all_next_state_clauses cur_bound next_bound
    else
      create_path_axioms [] cur_bound next_bound
  in
  (* do not create path axioms for the initial state *)
  let path_axioms =
    if next_bound > 0
    then path_axioms'
    else []
  in
  (* !current_options.bmc1_pre_inst_state is moved to iprover.ml *)
  (* Create clock axioms up to next bound *)
  let clock_axioms = get_clock_axioms (succ cur_bound) next_bound in

  (* Instantiate axioms for next bound *)
  let bound_axioms_instantiated = get_bound_axioms_instantiated next_bound in

  (* Assume assumption literal for next_bound to be true in solver *)
  let assumptions = get_current_bound_assumptions next_bound in

  (* Return created path axioms and reachable state axiom *)
  let bound_axioms =
    init_property_axioms @
    path_axioms @
    clock_axioms @
    bound_axioms_instantiated
  in

  (* Return created axioms for bound *)
  bound_axioms, assumptions

(* create {~$$Equal(S,S')} and for all state predicates P set of *)
(* {$$Equal_P(S,S'), P(S,C), P(S',C)} and {$$Equal_P(S,S'), ~P(S,C), ~P(S',C)} *)
let list_non_equal_axioms state state' =
  (* create state vars *)
  let s = create_state_term state in
  let s' = create_state_term state' in
  (* the 1st clause *)
  let neq_clause = create_non_equal_state_axiom state state' in
  (* the list of non-equal *)
  let neq_list = Bmc1Equal.bmc1_create_not_equal_definition s s' in
  (* return all axioms *)
  neq_clause :: neq_list

(* create a list of axioms {~$$Equal(bi, b)} for i = 0..b-1 *)
let create_different_consts_axiom bound =
  (* add {~$$Equal(b,b')} to the accumulator until b < b' *)
  let rec different_const_folder b b' =
    assert (b <= b');
    if b < b'
    then (list_non_equal_axioms b b') @ (different_const_folder (succ b) b')
    else []
    in
  (* create all axioms if necessary *)
  if !current_options.bmc1_non_equiv_states
  then different_const_folder 0 bound
  else []


(**)
(* process k-induction bound increment *)
(**)

(* for base stage: just switch on the init; *)
let process_k_induction_base_stage bound =
  (* create negated property axiom {$$init(b),~$$iProver_bound(b)} *)
  let init_axiom = create_guarded_init_axiom bound in
  (* create literal to switch on the base guard *)
  let base_assumption = create_base_assumption () in
  (* assumptions here are init, last bound and all previous bounds negated *)
  let assumptions = base_assumption :: (get_current_bound_assumptions bound) in
  (* return axioms and assumptions *)
  [init_axiom], assumptions

(* for step stage: create axioms {$$property(constB{b})}, *)
(* {$$nextState(b,b-1)}, {$$init(b), ~$$iProver_bound(b)}, *)
(* {~$$Equal(x,b)} for x < b *)
(* Make assumptions ~$$init, ~bound(0..b-1), bound(b) *)
let process_k_induction_step_stage bound =
  (* make sure bound is no-zero *)
  assert (bound > 0);
  (* create an axiom $$property(constB{b}) *)
  let property_axiom = create_property_axiom bound in
  (* create a path axiom $$nextState(b,b-1) *)
  let path_axiom = create_path_axiom bound in
  (* create non-equal axioms for bound *)
  let nequal_axioms = create_different_consts_axiom bound in
  (* put all axioms together *)
  let axioms = [ property_axiom; path_axiom ] @ nequal_axioms in

  (* create literal to switch off the base guard *)
  let step_assumption = create_step_assumption() in
  (* assumptions here are init, last bound and all previous bounds negated *)
  let assumptions = step_assumption :: (get_current_bound_assumptions bound) in
  (* return axioms and assumptions *)
  axioms, assumptions

(**)
(* get additional axioms for k-induction wrt the stage and bound *)
(**)
let process_k_induction_stage phase =
  (* get the bound *)
  let bound = phase.mc_cur_bound in
  (* create path axioms and assumptions wrt the stage *)
  (* the assumption list is updated by these functions *)
  let path_axioms, assumptions =
    match phase.mc_alg_stage with
    | IndBase -> process_k_induction_base_stage bound
    | IndStep -> process_k_induction_step_stage bound
  in

  (* Create clock axioms for bound *)
  let clock_axioms = get_clock_axioms bound bound in

  (* Instantiate axioms for bound *)
  let bound_axioms_instantiated = get_bound_axioms_instantiated bound in

  (* FIXME!! do not do anything else ATM *)
  let bound_axioms =
    path_axioms @
    clock_axioms @
    bound_axioms_instantiated
  in

  (* Return created axioms for bound *)
  bound_axioms, assumptions

(**)
(* process deadlock bound increment *)
(**)

(* for base stage: create axioms {$$nextState(b,b+1)}, *)
(* {~$$base, ~$eligible(b),~$$bound{b}} *)
(* Make assumptions $$base, ~bound(0..b-1), bound(b) *)
let process_deadlock_base_stage bound =
  (* Create literal to switch on the bound, $$iProver_bound{b} *)
  let bound_literal = create_bound_atom bound in
  (* create a path axiom $$nextState(b,b+1) *)
  let path_axiom = create_path_axiom (succ bound) in
  (* create base guard *)
  let base_guard = create_base_guard () in
  (* Create state term for state *)
  let state_term_b = create_state_term bound in
  (* create eligible deadlock literal ~eligible(b) *)
  let eligible_atom = create_eligible_atom state_term_b in
  let eligible_lit = add_compl_lit eligible_atom in
  (* FOR NOW!! use next() tstp *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom bound) in
  (* eligible axiom *)
  let eligible_axiom = create_clause tstp_source
    [
      base_guard;
      eligible_lit;
      (add_compl_lit bound_literal)
    ]
  in
  (* all axioms to return *)
  let axioms = [ path_axiom; eligible_axiom ] in

  (* create base assumption *)
  let base_assumption = create_base_assumption () in
  (* assumptions here are init, last bound and all previous bounds negated *)
  let assumptions = base_assumption :: (get_current_bound_assumptions bound) in
  (* return axioms and assumptions *)
  axioms, assumptions

(* for step stage: create axiom {{~next(s_N,X), Equal(s_N, X), $$base, ~$$boundN}}, *)
(* Make assumptions ~$$base, ~bound(0..b-1), bound(b) *)
let process_deadlock_step_stage bound =
  (* Create state term for state *)
  let state_term_b = create_state_term bound in
  (* create state var *)
  let x = term_x0 state_type in
  (* create ~next(b,X) *)
  (* TsarFIXME!! what to do?! *)
  let next_lit = add_compl_lit (create_auto_path_atom state_term_b x) in
  (* create Equal(b,X) *)
  let equal_lit = create_equal_state_atom state_term_b x in
  (* Create literal to switch on the bound, $$iProver_bound{b} *)
  let bound_atom = create_bound_atom bound in
  let bound_lit = add_compl_lit bound_atom in
  (* get step guard *)
  let step_guard = create_step_guard() in
  (* FOR NOW!! use next() tstp *)
  let tstp_source = Clause.tstp_source_axiom_bmc1 (Clause.TSTP_bmc1_path_axiom bound) in
  (* create the necessary axiom *)
  let axiom = create_clause tstp_source
    [ step_guard; next_lit; equal_lit; bound_lit ] in
  (* put all axioms together *)
  let axioms = [axiom] in

  (* create literal to switch off the base guard *)
  let step_assumption = create_step_assumption() in
  (* assumptions here are init, last bound and all previous bounds negated *)
  let assumptions = step_assumption :: (get_current_bound_assumptions bound) in
  (* return axioms and assumptions *)
  axioms, assumptions

(**)
(* get additional axioms for k-induction wrt the stage and bound *)
(**)
let process_deadlock_stage phase =
  (* get the bound *)
  let bound = phase.mc_cur_bound in
  (* create path axioms and assumptions wrt the stage *)
  (* the assumption list is updated by these functions *)
  let path_axioms, assumptions =
    match phase.mc_alg_stage with
    | IndBase -> process_deadlock_base_stage bound
    | IndStep -> process_deadlock_step_stage bound
  in

  (* Create clock axioms for bound *)
  let clock_axioms = get_clock_axioms bound bound in

  (* Instantiate axioms for bound *)
  let bound_axioms_instantiated = get_bound_axioms_instantiated bound in

  (* FIXME!! do not do anything else ATM *)
  let bound_axioms =
    path_axioms @
    clock_axioms @
    bound_axioms_instantiated
  in

  (* Return created axioms for bound *)
  bound_axioms, assumptions

let process_bmc_stage lemmas phase =
  let next_bound = phase.mc_cur_bound in
  increment_bound (pred next_bound) next_bound lemmas

(* different handlers *)

(* let _ = out_warning "bmc1Axioms.ml switch just k_ind STEP no base cases" *)

(* return handlers corresponding to deadlock *)
let get_handlers_deadlock () =
  let update_phase phase =
    match phase.mc_alg_stage with
    | IndBase ->
      if phase.mc_deadlock_stay_base
      then (* increase bound but keep the stage *)
      (
        phase.mc_cur_bound <- succ phase.mc_cur_bound;
        phase.mc_deadlock_stay_base <- false;
      )
      else (* just change the stage *)
        phase.mc_alg_stage <- IndStep
    | IndStep -> (* change stage to base and increase bound *)
    (
      phase.mc_cur_bound <- succ phase.mc_cur_bound;
      phase.mc_alg_stage <- IndBase; 
    )
  in
  let after_sat phase =
    match phase.mc_alg_stage with
    | IndBase ->
        out_str ("\nBMC1 deadlock: BASE is SAT at bound "^(string_of_int phase.mc_cur_bound)^": continue with STEP\n");
    | IndStep ->
        out_str ("\nBMC1 deadlock: STEP is SAT at bound "^(string_of_int phase.mc_cur_bound)^": Deadlock found\n");
        raise Exit;
  in
  let after_unsat phase =
    match phase.mc_alg_stage with
    | IndBase ->
      out_str ("\nBMC1 deadlock: BASE is UNSAT at bound "^(string_of_int phase.mc_cur_bound)^": increase bound and continue with BASE\n");
      phase.mc_deadlock_stay_base <- true;
    | IndStep ->
      out_str ("\nBMC1 deadlock: STEP is UNSAT at bound "^(string_of_int phase.mc_cur_bound)^": increase bound and continue with BASE\n");
  in
  {
    mc_task_name = "deadlock";
    mc_update_phase = update_phase;
    mc_after_sat = after_sat;
    mc_after_unsat = after_unsat;
    mc_get_next_bound_axioms = process_deadlock_stage;
  }

(* return handlers corresponding to k-induction *)
let get_handlers_k_induction () =
  let update_phase phase =
    match phase.mc_alg_stage with
    | IndBase -> (* change stage to step and increase bound *)
    (
      phase.mc_cur_bound <- succ phase.mc_cur_bound;
      phase.mc_alg_stage <- IndStep;
    )
    | IndStep -> (* change stage to base; do not increase bound *)
     ( phase.mc_alg_stage <- IndBase 
       
(* KK added for experiment *)
(*
        IndStep;
        phase.mc_cur_bound <- succ phase.mc_cur_bound;
*)
(* just for experiment changed IndBase to IndStep *)
      )

                  
  in
  let after_sat phase =
    match phase.mc_alg_stage with
    | IndBase ->
        (* base is SAT means there is no solution *)
        out_str ("\nBMC1 k-induction: BASE is SAT at bound "^(string_of_int phase.mc_cur_bound)
	   ^": Property is disproved\n");
      (* pure BMC require exit; UCM doesn't *)
      if (not !current_options.bmc1_ucm)
      then
        raise Exit
    | IndStep ->
        out_str ("\nBMC1 k-induction: STEP is SAT at bound "^(string_of_int phase.mc_cur_bound)
	   ^": continue with BASE\n");
  in
  let after_unsat phase =
    match phase.mc_alg_stage with
    | IndBase ->
      out_str ("\nBMC1 k-induction: BASE is UNSAT at bound "^(string_of_int phase.mc_cur_bound)^": increase bound and continue with STEP\n");
      (* re-run for the next bound in any case *)
    | IndStep ->
      (* step is UNSAT means we found a solution *)
      out_str ("\nBMC1 k-induction: STEP is UNSAT at bound "^(string_of_int phase.mc_cur_bound)^": Property is proved\n");
      (* pure BMC require exit; UCM doesn't *)
      if (not !current_options.bmc1_ucm)
      then
        raise Exit
  in
  {
    mc_task_name = "k-induction";
    mc_update_phase = update_phase;
    mc_after_sat = after_sat;
    mc_after_unsat = after_unsat;
    mc_get_next_bound_axioms = process_k_induction_stage;
  }

(* return handlers corresponding to property lemmas *)
let get_handlers_property_lemmas () =
  let update_phase phase = phase.mc_cur_bound <- succ phase.mc_cur_bound in
  let after_sat phase =
    out_str ("\nBMC1 with property lemmas is SAT at bound "^(string_of_int phase.mc_cur_bound)^": property disproved\n");
    (* pure BMC require exit; UCM doesn't *)
    if (not !current_options.bmc1_ucm)
    then
      raise Exit
  in
  let after_unsat phase =
    out_str ("\nBMC1 with property lemmas is UNSAT at bound "^(string_of_int phase.mc_cur_bound)^": increase bound and continue\n")
  in
  {
    mc_task_name = "BMC1 with property lemmas";
    mc_update_phase = update_phase;
    mc_after_sat = after_sat;
    mc_after_unsat = after_unsat;
    mc_get_next_bound_axioms = process_bmc_stage true;
  }

(* return handlers corresponding to pure BMC *)
let get_handlers_bmc () =
  let update_phase phase = phase.mc_cur_bound <- succ phase.mc_cur_bound in
  let after_sat phase =
    out_str ("\nBMC1 is SAT at bound "^(string_of_int phase.mc_cur_bound)^": property disproved\n");
    (* pure BMC require exit; UCM doesn't *)
    if (not !current_options.bmc1_ucm)
    then
      raise Exit
  in
  let after_unsat phase =
    out_str ("\nBMC1 is UNSAT at bound "^(string_of_int phase.mc_cur_bound)^": increase bound and continue\n")
  in
  {
    mc_task_name = "BMC1";
    mc_update_phase = update_phase;
    mc_after_sat = after_sat;
    mc_after_unsat = after_unsat;
    mc_get_next_bound_axioms = process_bmc_stage false;
  }

(* get handlers acording to flags *)
let get_mc_handlers () =
  if !current_options.bmc1_deadlock
  then
    get_handlers_deadlock ()
  else if !current_options.bmc1_k_induction
  then
    get_handlers_k_induction ()
  else if !current_options.bmc1_property_lemmas
  then
    get_handlers_property_lemmas ()
  else
    get_handlers_bmc ()



(* Create axiom for given bound of axioms for previous bound *)
let rec extrapolate_to_bound' bound accum = function

    (* Return extrapolated clauses *)
  | [] -> accum

	(* Continue with tail of list of clauses *)
  | clause :: tl ->

      (* Add extrapolated axiom to accumulator *)
      let accum' =

	(* Get source of clause *)
	match Clause.get_tstp_source clause with

	  (* Clause is a BMC1 path axiom for the previous bound *)
	| Clause.TSTP_external_source
	    (Clause.TSTP_theory
	       (Clause.TSTP_bmc1
		  (Clause.TSTP_bmc1_path_axiom b)))
	  when b = (pred bound) ->

	    (* Add path axiom for current bound *)
	    (create_path_axiom bound) :: accum

							  (* Clause is a BMC1 reachable state axiom for the previous bound *)
	| Clause.TSTP_external_source
	    (Clause.TSTP_theory
	       (Clause.TSTP_bmc1
		  (Clause.TSTP_bmc1_clock_axiom (b, clock, pattern))))
	  when b = (pred bound) ->

	    (* Add reachable state axiom for current bound *)
	    ( create_clock_axiom bound clock pattern) :: accum

							  (* Clause is a BMC1 reachable state axiom for the previous bound *)
	| Clause.TSTP_inference_record
	    (Clause.TSTP_bmc1_instantiated_clause (b), [clause])
	  when b = (pred bound) ->

	    (* Add reachable state axiom for current bound *)
	    (bound_instantiate_clause bound clause) :: accum

							(* Clause is not a BMC1 axiom *)
	| _ -> accum

      in

      (* Continue with tail of list of clauses *)
      extrapolate_to_bound' bound accum' tl

(* For all axioms that are dependent on the previous bound return a
   list of clauses for the given bound. *)
let extrapolate_to_bound bound clauses =
  extrapolate_to_bound' bound [] clauses
