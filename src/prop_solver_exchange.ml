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
open Statistics
open Options
open Logic_interface


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =  
  | D_trace
  | D_gr_term 
  | D_add_clause
  | D_selection_renew
  | D_selection_renew_lit
  | D_solve
  | D_gr_trie 
  | D_unsat_core
  | D_print_unsat_core
  | D_print_uc_time
  | D_assumptions
  | D_soft_assumptions
  | D_prop_subs
  | D_prop_subs_assert
  | D_uc
  | D_prop_lit_to_fof 
  | D_prop_impl_unit

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_gr_term -> "gr_term"
  | D_add_clause -> "add_clause"
  | D_selection_renew -> "selection_renew"
  | D_selection_renew_lit -> "selection_renew_lit"
  | D_solve -> "solve"
  | D_gr_trie -> "gr_trie"
  | D_unsat_core -> "unsat_core"
  | D_print_unsat_core -> "print"
  | D_print_uc_time -> "uc_time"
  | D_assumptions    -> "assumptions"
  | D_soft_assumptions -> "soft_assumptions"
  | D_prop_subs -> "prop_subs"
  | D_prop_subs_assert -> "prop_subs_assert"
  | D_uc -> "uc"
  | D_prop_lit_to_fof -> "prop_lit_to_fof"
  | D_prop_impl_unit -> "prop_impl_unit"

let dbg_groups_ref =
  ref
    [
     (*   D_trace; *)
      D_gr_term;   
     (*   D_add_clause;   *)
 (*    D_print_unsat_core; *)
     (* D_print_uc_time; *)
(*       D_selection_renew_lit;    *)
(*       D_selection_renew;    *)
(*     D_unsat_core; *)
(*     D_soft_assumptions; *)
(*     D_assumptions; *)
(*     D_gr_trie; *)
     (* D_solve;   *)
      (* D_prop_subs;   *)
      (* D_prop_subs_assert;   *)
(*     D_uc; *)
(*     D_prop_lit_to_fof;*)
     (* D_prop_impl_unit; *)
   ]
    
let module_name = "prop_solver_ex"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag !dbg_groups_ref group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag !dbg_groups_ref group f
  
(*----- debug -----*)


(*-----------------------*)

(* Formatter for output, None if uninitialised. Use
   get_prop_dump_formatter as access function *)
let prop_clauses_dump_formatter = ref None

(* Return a formatter for writing into the file given in the option
   -- dbg_prop_clauses_dump_file *)
let get_prop_clauses_dump_formatter () =
  
  match !prop_clauses_dump_formatter with
    
    (* Return formatter if initialised *)
  | Some f -> f
	
	(* Formatter is not initialised *)
  | None ->
      
      (* Formatter of channel of opened file *)
      let new_prop_clauses_dump_formatter =
	
	try
	  
	  (* Open formatter writing into file *)
	  formatter_of_filename
	    false
	    !current_options.dbg_dump_prop_clauses_file
	    
	with
	  
	  (* Catch errors when opening *)
	| Sys_error _ ->
	    raise (Failure
		     (Format.sprintf
			"Could not open file %s for output"
			!current_options.dbg_dump_prop_clauses_file))
	      
      in
      
      (* Save formatter *)
      prop_clauses_dump_formatter := Some new_prop_clauses_dump_formatter;
      
      (* Return formatter *)
      new_prop_clauses_dump_formatter

type prop_lit = PropSolver.lit
type prop_lit_uc = PropSolver.lit_uc


let bot_symb = Symbol.symb_bot
let bot_term = Parser_types.bot_term

(* uc extraction global time *)
let uc_total_time = ref 0.0

(* uc extraction session time *)
let uc_session_time = ref 0.0

let reset_uc_session_timer () =
  uc_session_time := 0.0


(*-------*)

(* decision variables are only implemented in C++ MiniSAT; check propSolver.ml *)
let decision_var_test_param = ref Undef

let set_decision_var_test_hook decsion_var_test_fun = 
  decision_var_test_param := Def(decsion_var_test_fun)



(* gr_by can be changed by  init_solver_exchange *)

(* gr_by_map is a map from types -> grounding term of this type *)
(* if a type is not in the gr_by_map then use default bot_term (which is of type type_types) *)
(*
let gr_by_map = ref SMap.empty
*)

type gr_map = term SMap.t

(* later change to exensible arrays and interface for old maps *)
type gr_by_maps = 
    {

     mutable gr_cur_map_id : int; 
     
(* gr_by_map is a map from types -> grounding term of this type *)
(* if a type is not in the gr_by_map then use default bot_term (which is of type type_types) *)
     mutable gr_cur_map : gr_map;
     mutable gr_map_list : gr_map list;
   }

let gr_by_maps = 
    {
     gr_cur_map_id = 0;
     gr_cur_map = SMap.empty;
     gr_map_list = [];
   }

let get_gr_by_map () = 
  gr_by_maps.gr_cur_map

let get_gr_map_id () = 
  gr_by_maps.gr_cur_map_id

(* let _ = out_warning ("commented: change_gr_by_map") *)
let change_gr_by_map gr_map =
  gr_by_maps.gr_cur_map_id <- gr_by_maps.gr_cur_map_id +1;
  gr_by_maps.gr_cur_map <- gr_map;
  gr_by_maps.gr_map_list <- gr_map::gr_by_maps.gr_map_list;
(* debug *)
 
  dbg_env D_gr_term 
    (fun () ->

      dbg D_gr_term  
	(lazy ("---------Terms for grounding-----"));
      let f stype gr_term =
	
	let num_of_occ = Symbol.get_num_input_occur (Term.get_top_symb gr_term)
	in
	dbg D_gr_term  
	  (lazy ("Term for grounding type: "
		 ^(Symbol.to_string stype)^" term: "^(Term.to_string gr_term)
		 ^" num of occ: "^(string_of_int num_of_occ)^"\n"));
      in	
      SMap.iter f (get_gr_by_map ());    
      
    )


(*		
let _ = out_warning (" dbg: get_gr_by \n\n ")
*)

let get_gr_by vtype =
  try
    SMap.find vtype (get_gr_by_map ()) 
  with
  | Not_found ->
  bot_term

let get_gr_by_var var =
  let vtype = Var.get_type var in
  get_gr_by vtype


(* context containing all groundings *)
let gr_context =  Clause.context_create ()

(*
let get_gr_by vtype =
  try
    SMap.find vtype !gr_by_map
  with
  | Not_found -> bot_term

let get_gr_by_var var =
  let vtype = Var.get_type var in
  get_gr_by vtype
*)


(* terms are assigned with groundings and simple reassigning breaks things*)

(*
  let assign_new_grounding vtype gr_term =
  assert (vtype == Term.get_term_type gr_term);
  gr_by_map := SMap.add vtype gr_term !gr_by_map

 *)

(*let gr_by          = ref bot_term*)

(*------------Parameters that can be changed by other modules-----------*)

(*let lit_activity_threshold   = ref 200*)
(*let lit_activity_flag_ref    = ref true*)
 
(* let lit_activity_threshold = ref 500 *) (*was for CASC 2012*)

 let lit_activity_threshold = ref 500 
 
(*
  let set_lit_activity_flag b =
  (lit_activity_flag_ref := b;
  lit_activity_threshold:= 200000000
  )
 *)

(*--------------------get term for grounding-----------------------*)
(* before typed version *)
(*
  let get_term_for_grounding () =
  if !answer_mode_ref then
  bot_term
  else
  begin
(* first try the  constant with max occurrence, which is in the conjecture*)
  let gr_symb =
  let f_max_sym s max_sym =
  if (
  (Symbol.is_constant s) &&
  (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym))
  then s
  else max_sym
  in
  let max_sym = SymbolDB.fold f_max_sym !symbol_db_ref bot_symb in
  max_sym
  in
(* we need to find the term in term_db corresponding to max_sym*)
(* for this we just try to add it to term_db *)
  let gr_by_term = TermDB.add_ref (Term.create_fun_term gr_symb []) term_db_ref in
  gr_by_term
  end
 *)

let init_gr_by' () =
  if !answer_mode_ref then
    ()
  else
    (* max_occ_map maps symbol type into symbol with max occurences in input*)
    let f_max_sym s max_occ_map =
      if (Symbol.is_constant s) (* is_constant is true on types; should be still ok with euqality *)
      then
	match (Symbol.get_stype_args_val s)
	with
	| Def((_arg, stype)) ->
	    begin
	      try
		let max_sym = SMap.find stype max_occ_map in
		if (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym)
		then
		  let moc_map_rem = SMap.remove stype max_occ_map in
		  SMap.add stype s moc_map_rem
		else
		  max_occ_map
	      with
	      | Not_found ->
		  SMap.add stype s max_occ_map
	    end
	| Undef ->
	    (*out_warning ("a constant symbol "^(Symbol.to_string s)^(" does not have a type \n")); *)
	    max_occ_map
      else
	max_occ_map
    in
    let max_sym_map = SymbolDB.fold f_max_sym !symbol_db_ref SMap.empty in
    
    (* from type -> symb to type -> const_term *)
    
    let f stype s gr_term_map_curr =
      let gr_by_term =
	add_fun_term s [] in
      SMap.add stype gr_by_term gr_term_map_curr
    in
    let gr_term_map =
      SMap.fold f max_sym_map SMap.empty in
(*    gr_by_map := gr_term_map *)
    change_gr_by_map gr_term_map
	
let init_gr_by () = 
  init_gr_by' () 
(*  out_warning ("init_gr_by: gr_by replaced by bot !") *)
  

let init_solver_exchange () =
  
  init_gr_by ();
  
 (* out_warning ("init_solver_exchange: gr_by replaced by bot !");*)
  
(* debug *)
 
  dbg_env D_gr_term 
    (fun () ->

      dbg D_gr_term  
	(lazy ("---------Terms for grounding-----"));
      let f stype gr_term =
	
	let num_of_occ = Symbol.get_num_input_occur (Term.get_top_symb gr_term)
	in
	dbg D_gr_term  
	  (lazy ("Term for grounding type: "
		 ^(Symbol.to_string stype)^" term: "^(Term.to_string gr_term)
		 ^" num of occ: "^(string_of_int num_of_occ)^"\n"));
      in	
      SMap.iter f (get_gr_by_map ());    

    )
    

(*--------------Init Solvers-----------------------------*)

let solver     = PropSolver.create_solver false

let solver_sim = PropSolver.create_solver true

let solver_uc  = PropSolver.create_solver_uc false


(*-------*)
let () = assign_fun_stat
    (fun () ->
      (PropSolver.num_of_solver_calls solver) +
	(PropSolver.num_of_solver_calls solver_sim))
    prop_solver_calls

let () = assign_fun_stat
    (fun () ->
      (PropSolver.num_of_fast_solver_calls solver) +
	(PropSolver.num_of_fast_solver_calls solver_sim))
    prop_fast_solver_calls


(*-------*)

let compare_uc_lit l1 l2 =
  (* compare signs *)
  let sign1 = (PropSolver.lit_sign_uc solver_uc l1) in
  let sign2 = (PropSolver.lit_sign_uc solver_uc l2) in
  if sign1 = sign2
  then (* compare vars *)
    let v1 = (PropSolver.lit_var_uc solver_uc l1) in
    let v2 = (PropSolver.lit_var_uc solver_uc l2) in
    compare v1 v2
  else (* positive larger than negative *)
    if sign1
    then 1
    else -1


module UCLitMap = Map.Make(
  struct
    type t = prop_lit_uc
    let compare = compare_uc_lit
  end)

(* global map from UC literals to Term.term *)
let uc2tMap = ref UCLitMap.empty

(* update mape with uc_lit -> term *)
let update_uc_map uc_lit term =
  uc2tMap := UCLitMap.add uc_lit term !uc2tMap

(*-------------------*)

(* Mapping from id of clauses in the satisfiability solver to their corresponding
   first - order clauses *)

type prop_uc_fof = (* puf *)
    {
     mutable puf_id_to_fof : clause IntMap.t;
     mutable puf_fof_to_id : int BCMap.t; 
(* basic clause; add clause to solver only once and use it in all proofs *)
   }

let puf = 
  {
   puf_id_to_fof = IntMap.empty;
   puf_fof_to_id = BCMap.empty;
 }

let puf_add_clause id clause = 
  puf.puf_id_to_fof <- IntMap.add id clause puf.puf_id_to_fof;
  puf.puf_fof_to_id <- BCMap.add clause id puf.puf_fof_to_id
      
(* can raise Not_found *)
let puf_get_id clause = 
  BCMap.find clause puf.puf_fof_to_id

(* can raise Not_found *)
let puf_get_clause id = 
  IntMap.find id puf.puf_id_to_fof

(* 
let solver_uc_clauses : (int, Clause.clause) Hashtbl.t = Hashtbl.create 1001
*)
(*-----------------------*)

(*------------ prop_to_fof_lit -----------*)
(* stores mapping from prop_lit -> fof_lit *)
(* used only in some cases like bin hyper res. *)
(*------------- TODO: clean --------*)

let prop_lit_to_fof_flag = true
(* SW
let _ = out_warning ("prop_lit_to_fof_flag: "^(string_of_bool prop_lit_to_fof_flag))*)

module PLMap=PropSolver.PLMap

type prop_lit_to_fof = 
    {
     mutable prop_lit_to_fof : term PLMap.t;
   }

let pltf = 
  {
   prop_lit_to_fof = PLMap.empty
 }

let pltf_add prop_lit fof_lit = 
  if prop_lit_to_fof_flag 
  then
    (
     dbg D_prop_lit_to_fof (lazy ("add: prop: "^(PropSolver.lit_to_string solver prop_lit)^" fof: "^(Term.to_string fof_lit)));
     pltf.prop_lit_to_fof <- PLMap.add prop_lit fof_lit pltf.prop_lit_to_fof
    )
  else 
    (     
    )

(* can raise Not_found *)
let pltf_get_fof_lit prop_lit = 
  assert(prop_lit_to_fof_flag);
  dbg D_prop_lit_to_fof (lazy ("get: prop: "^(PropSolver.lit_to_string solver prop_lit)));
  try    
    PLMap.find prop_lit pltf.prop_lit_to_fof
  with 
    Not_found -> 
      dbg D_prop_lit_to_fof (lazy ("get: prop: "^(PropSolver.lit_to_string solver prop_lit)^" Not_found"));
      raise Not_found

let apply_prop_lit_to_fof f = 
  pltf.prop_lit_to_fof <- PLMap.map f pltf.prop_lit_to_fof

(*-------*)

let all_impl_lits = ref TSet.empty
    

(* can raise Not_found *)
let get_next_implied_unit () = 
  let prop_lit = PropSolver.get_next_implied_unit solver in 
  let fof_lit = pltf_get_fof_lit prop_lit in 
  all_impl_lits := TSet.add fof_lit !all_impl_lits;
  fof_lit


let get_all_newly_implied_lits ~is_relevant = 
  let implied_lits_ref = ref [] in
  try 
    while true 
    do
      (
       let impl_fof_lit = get_next_implied_unit () in 
       if (is_relevant impl_fof_lit)
       then 
         (dbg D_prop_impl_unit (lazy (Term.to_string impl_fof_lit));
          implied_lits_ref := impl_fof_lit::!implied_lits_ref
         )
       else 
         ()
      )
    done; 
    !implied_lits_ref (* never happens *)
  with 
    Not_found -> 
      !implied_lits_ref


let get_all_newly_implied_unit_clauses ~is_relevant =   
  let tstp_source = Clause.tstp_source_prop_impl_unit in  
  let impl_lits = get_all_newly_implied_lits ~is_relevant in
  List.map (fun lit -> create_clause tstp_source [lit]) impl_lits

let get_all_impl_lits () = 
  let _ =  get_all_newly_implied_lits ~is_relevant:(fun _-> true) in
  !all_impl_lits

(* can raise Not_found *)
let get_next_ass_implied_unit ~solver_in = 
  let prop_lit = PropSolver.get_next_ass_implied_unit solver_in in 
  pltf_get_fof_lit prop_lit




(*-----------------------*)


(*
(*-----------------*)
(* solver assumptions are used for finite models *)
(* solver assumptions should be changed using assign_solver_assumptions below*)

(* assumptions for all solvers *)
let solver_assumptions_ref = ref []

(* Assumptions for unsat core solver *)
let solver_uc_assumptions_ref = ref []

(* assumptions only for non-simplifying  *)
let only_norm_solver_assumptions_ref = ref []

(* original assumptions *)
let only_norm_original_assumptions_ref = ref []

(* Assumptions for unsat core solver *)
let solver_uc_norm_assumptions_ref = ref []

(* assumptions only for simplifying  *)
let only_sim_solver_assumptions_ref = ref []

(* Assumptions for unsat core solver *)
let solver_uc_sim_assumptions_ref = ref []

(* only for non-simplifying*)
let answer_assumptions_ref = ref []
let answer_assumptions_uc_ref = ref []


(* soft assumptions support *)
type soft_assumptions = 
    {
     mutable sa_set  : TSet.t;
(*     mutable sa_list : term list; *)
   }
 
let soft_assumptions = 
  {
   sa_set = TSet.empty;
(*   sa_list = term list; *)
 }


let get_soft_assumptions_list () = TSet.elements soft_assumptions.sa_set

(*---------*)
let get_solver_assumptions solver =
  if (PropSolver.is_simplification solver)
  then
    ((!only_sim_solver_assumptions_ref)@(!solver_assumptions_ref))
  else
    (
     (!only_norm_solver_assumptions_ref) @
     (!answer_assumptions_ref) @
     (!solver_assumptions_ref)
    )

let get_assumptions_sat () =
  ((!only_norm_solver_assumptions_ref) @
   (!answer_assumptions_ref) @
   (!solver_assumptions_ref))
    
let get_assumptions_sim () =
  ((!only_sim_solver_assumptions_ref)
   @(!solver_assumptions_ref))

(* Return literal assumptions for unsat core solver *)
let get_solver_uc_assumptions () =
  !solver_uc_assumptions_ref @
  !solver_uc_norm_assumptions_ref @
  !solver_uc_sim_assumptions_ref @
  !answer_assumptions_uc_ref
    
(* adjoint_preds are added for all simplified claues *)
(* used in finite models *)

let adjoint_preds = ref TSet.empty

(* map from UC literals to Term.term; used in the UC creation *)

let compare_uc_lit l1 l2 =
  (* compare signs *)
  let sign1 = (PropSolver.lit_sign_uc solver_uc l1) in
  let sign2 = (PropSolver.lit_sign_uc solver_uc l2) in
  if sign1 = sign2
  then (* compare vars *)
    let v1 = (PropSolver.lit_var_uc solver_uc l1) in
    let v2 = (PropSolver.lit_var_uc solver_uc l2) in
    compare v1 v2
  else (* positive larger than negative *)
    if sign1
    then 1
    else -1


(*-------------------------*)

exception AssumptionsInconsistent
let normalise_assumptions assumptions =
  if assumptions = []
  then []
  else
    let cmp l1 l2 =
      compare (PropSolver.lit_var solver l1) (PropSolver.lit_var solver l2)
    in
    let sorted_assumptions = List.sort cmp assumptions in
    let rec elim_duplicates_compl rest lit_list =
      match lit_list with
      | [] -> rest
      | l::[] -> l:: rest
      | l1:: l2:: tl ->
	  let id1 = (PropSolver.lit_var solver l1) in
	  let id2 = (PropSolver.lit_var solver l2) in
	  if id1 = id2
	  then
	    let sign1 = (PropSolver.lit_sign solver l1) in
	    let sign2 = (PropSolver.lit_sign solver l2) in
	    if sign1 = sign2
	    then
	      elim_duplicates_compl rest (l1:: tl)
	    else
	      raise AssumptionsInconsistent
	  else
	    elim_duplicates_compl (l1:: rest) (l2:: tl)
    in
    elim_duplicates_compl [] sorted_assumptions

let normalise_assumptions_uc assumptions =
  if assumptions = []
  then []
  else
    let cmp l1 l2 =
      compare
	(PropSolver.lit_var_uc solver_uc l1)
	(PropSolver.lit_var_uc solver_uc l2)
    in
    let sorted_assumptions = List.sort cmp assumptions in
    let rec elim_duplicates_compl rest lit_list =
      match lit_list with
      | [] -> rest
      | l::[] -> l:: rest
      | l1:: l2:: tl ->
	  let id1 = (PropSolver.lit_var_uc solver_uc l1) in
	  let id2 = (PropSolver.lit_var_uc solver_uc l2) in
	  if id1 = id2
	  then
	    let sign1 = (PropSolver.lit_sign_uc solver_uc l1) in
	    let sign2 = (PropSolver.lit_sign_uc solver_uc l2) in
	    if sign1 = sign2
	    then
	      elim_duplicates_compl rest (l1:: tl)
	    else
	      raise AssumptionsInconsistent
	  else
	    elim_duplicates_compl (l1:: rest) (l2:: tl)
    in
    elim_duplicates_compl [] sorted_assumptions

(*---------------------*)


(*------ olny used in this module ---------------*)
let solve_assumptions ?(reset = false) solver assumptions =
  try
    let ass = normalise_assumptions (assumptions@(get_solver_assumptions solver)) in
    dbg D_solve (lazy 
		   ("solve_assumptions: Assumptions: "^
		    (PropSolver.lit_list_to_string solver ass)^ "\n"));     
    PropSolver.solve_assumptions ~reset: reset solver ass
  with
    AssumptionsInconsistent -> PropSolver.Unsat

let fast_solve solver assumptions =
  try
    let ass = normalise_assumptions(assumptions@(get_solver_assumptions solver)) in
    PropSolver.fast_solve solver ass
  with
    AssumptionsInconsistent -> PropSolver.FUnsat


*)

(*------------ propositional interpretation-------------------*)

type var_entry =
    { var_id : int param;
      prop_var : prop_lit param;
      prop_neg_var : prop_lit param;
      prop_var_uc : prop_lit_uc param;
      prop_neg_var_uc : prop_lit_uc param;
      (* If  truth_val = Def(Any) the we assume that sel_clauses=[] *)
      (* So if we select a lit the we should change Def(Any) *)
      mutable truth_val : PropSolver.lit_val param;
      (* list of clauses for which selection is based on this var *)
      mutable sel_clauses : (clause list);
      (* used only for output of model*)
      mutable ground_term : lit param;
(*      mutable in_solver_sim : bool; *)
      mutable pos_activity : int;
      mutable neg_activity : int;
      (* we try to change the lit value if *)
      (* activity diff is greater than change_acitivity_limit *)
      mutable change_activity_limit : int;
    }

let var_entry_to_string prop_var_entry =
  let var_solver_val_str =
    match prop_var_entry.prop_var with
    | Def(prop_var) ->
	(* need to check if solver was called at all before *)
	(match prop_var_entry.truth_val with
	| Def _ ->
	    PropSolver.lit_val_to_string (PropSolver.lit_val solver prop_var)
	| _ -> "Never checked with Solver"
	)
    | _ -> " Var is undef "
  in
  "var_id: "^(param_to_string string_of_int prop_var_entry.var_id)
  ^"; current truth_val: "
  ^(param_to_string PropSolver.lit_val_to_string prop_var_entry.truth_val)
  ^"; Solver truth val: "^(var_solver_val_str)
  ^"; \n Ground term: "^(param_to_string Term.to_string prop_var_entry.ground_term)
  ^"; Pos Activity: "^(string_of_int prop_var_entry.pos_activity)
  ^"; Neg Activity: "^(string_of_int prop_var_entry.neg_activity)

let var_entry_sel_to_string prop_var_entry =
(*  try *)
    let clause_list_str =
      let get_cl_str rest clause =
(*
	let sel_lit = Clause.inst_get_sel_lit clause in
	let sel_str = "\n Selected:  "^(Term.to_string sel_lit)^"\n" in
*)
	let clause_str = " In clause: "^(Clause.to_string clause) in
	rest^(*sel_str^*)clause_str
      in
      List.fold_left get_cl_str "" prop_var_entry.sel_clauses
    in
    (var_entry_to_string prop_var_entry)^clause_list_str
(*  with
    Clause.Inst_sel_lit_undef ->
      raise (Failure "var_entry_sel_cl_to_string: Sel_lits_undef")
*)

let empty_var_entry =
  {
   var_id = Undef;
   prop_var = Undef;
   prop_neg_var = Undef;
   prop_var_uc = Undef;
   prop_neg_var_uc = Undef;
   truth_val = Undef;
   sel_clauses = [];
   ground_term = Undef;
(*   in_solver_sim = false; *)
   pos_activity = 0;
   neg_activity = 0;
   change_activity_limit = !lit_activity_threshold
 }

let create_var_entry var_id atom =
  (* we also need to create var in solver_sim ....*)
  PropSolver.add_var_solver solver_sim var_id;
  let var_entry = 
  {
   var_id = Def(var_id);
   prop_var = Def(PropSolver.create_lit solver PropSolver.Pos var_id);
   prop_neg_var = Def(PropSolver.create_lit solver PropSolver.Neg var_id);
   prop_var_uc = Def(PropSolver.create_lit_uc
		       solver_uc
		       PropSolver.Pos
		       (var_id + (PropSolver.clauses_with_id solver_uc)));
   prop_neg_var_uc = Def(PropSolver.create_lit_uc
			   solver_uc
			   PropSolver.Neg
			   (var_id + (PropSolver.clauses_with_id solver_uc)));
   truth_val = Undef;
   sel_clauses = [];
   ground_term = Def(atom);
(*   in_solver_sim = false; *)
   pos_activity = 0;
   neg_activity = 0;
   change_activity_limit = !lit_activity_threshold
 }
  in
  (if prop_lit_to_fof_flag
  then
    (
     pltf_add (get_param_val var_entry.prop_var) atom;
     pltf_add (get_param_val var_entry.prop_neg_var) (add_compl_lit atom);
    )
  else
    ()
  );
  var_entry
    

let var_table_initsize = 10001

let var_table = TableArray.create var_table_initsize empty_var_entry

let model_to_string_gen entry_to_str =
  let init_str = "\n ------------Model-----------\n" in
  let final_str = "\n ----------END Model----------\n" in
  let main_str =
    let get_entry_str rest entry =
      rest ^ "\n---------------------------------\n"
      ^(entry_to_str entry)^"\n" in
    TableArray.fold_left get_entry_str "" var_table
  in
  init_str^main_str^final_str

let model_to_string () = model_to_string_gen var_entry_to_string

let model_sel_to_string () =
  model_to_string_gen var_entry_sel_to_string

let clear_model () =
  TableArray.iter
    (function var_entry ->
      var_entry.sel_clauses <- [];
      var_entry.pos_activity <- 0;
      var_entry.neg_activity <- 0;
      var_entry.truth_val <- Undef
    ) var_table

let clear_model_and_move_to_passive move_clause_from_active_to_passive =
  TableArray.iter
    (function var_entry ->
      List.iter move_clause_from_active_to_passive var_entry.sel_clauses;
      var_entry.sel_clauses <- [];
      var_entry.pos_activity <- 0;
      var_entry.neg_activity <- 0;
      var_entry.truth_val <- Undef
    ) var_table

(*--------------*)
let get_var_entry_truth_val ve = ve.truth_val 
let get_var_entry_truth_val_def ve =
  match ve.truth_val with
  | Def(truth_val) -> truth_val
  | Undef -> raise (Failure "get_truth_var_entry: truth_val is Undef\n")

let set_var_entry_truth_val ve tv = ve.truth_val <- tv

let get_var_entry_pos_activity ve = ve.pos_activity
let get_var_entry_neg_activity ve = ve.neg_activity

(*--------------*)

(* Create a new propositional variable that no term is assigned to *)
let get_new_dummy_prop_var () =
  
  (* Get next key in variable table *)
  let new_key = TableArray.get_next_key var_table in
  
  (* Assign empty entry for new key *)
  TableArray.assign var_table new_key empty_var_entry;
  
  (* Return new key *)
  new_key

let get_prop_key_assign atom =
  try Term.get_prop_key atom
  with Term.Prop_key_undef ->
    (let new_key = TableArray.get_next_key var_table in
    (* var_id > 0 *)
    let var_id = TableArray.key_to_int new_key + 1 in
    let var_entry = create_var_entry var_id atom in
    TableArray.assign var_table new_key var_entry;
    Term.assign_prop_key new_key atom;
   (* (if (Term.is_ground atom)
    then Term.assign_prop_gr_key new_key atom
    else ());*)
    new_key)

(*  a*)

(*
let get_prop_gr_key_assign term =
  try (Term.get_prop_gr_key term)
  with Term.Prop_gr_key_undef ->
    let gr_term =
      try Term.get_grounding term
      with
	(Term.Term_grounding_undef (t)) ->
	  (let new_gr_t = Subst.grounding term_db_ref !gr_by_map term in
	  Term.assign_grounding new_gr_t term;
	  new_gr_t)
    in 
    (*	out_str ("T: "^(Term.to_string term)^(" G ")^(Term.to_string gr_term)^"\n"); *)
    try
      let new_key = Term.get_prop_gr_key gr_term in
      Term.assign_prop_gr_key new_key term;
      new_key
    with Term.Prop_gr_key_undef ->
      let new_key = TableArray.get_next_key var_table in
      (* var_id > 0 *)
      let var_id = TableArray.key_to_int new_key + 1 in
      let var_entry = create_var_entry var_id gr_term in
      TableArray.assign var_table new_key var_entry;
      Term.assign_prop_gr_key new_key term;
      Term.assign_prop_gr_key new_key gr_term;
      Term.assign_prop_key new_key gr_term;
      new_key
*)

(*
let rec get_prop_gr_key_assign term =
  try 
    let grounding_info = Term.get_grounding_info term in 
    match grounding_info with 
    |Term.Grounding_non_gr grounding_non_gr -> 
	let curr_map_id = get_gr_map_id () in 
	if (curr_map_id = grounding_non_gr.Term.grounding_subst_id)
	then
	  get_prop_gr_key_assign grounding_non_gr.Term.grounded_term
	else
	  let new_gr_t = Subst.grounding term_db_ref (get_gr_by_map ()) term in
	  dbg D_gr_term (lazy ("T: "^(Term.to_string term)^
			       " Old G: "^(Term.to_string grounding_non_gr.Term.grounded_term)^"\n"^
			       " G: "^(Term.to_string new_gr_t)^"\n")) ;
	  grounding_non_gr.Term.grounding_subst_id <- curr_map_id;
	  grounding_non_gr.Term.grounded_term <- new_gr_t; 	  
	  get_prop_gr_key_assign grounding_non_gr.Term.grounded_term
    |Term.Grounding_gr_key prop_gr_key -> prop_gr_key
  with 
  |Term.Grounding_undef ->
      let new_grounding_info =  
	if (Term.is_ground term)
	then     
	  begin
	    let new_key = TableArray.get_next_key var_table in
	    (* var_id > 0 *)
	    let var_id = TableArray.key_to_int new_key + 1 in
	    let var_entry = create_var_entry var_id term in
	    TableArray.assign var_table new_key var_entry;
	    (* Term.assign_prop_gr_key prop_key term;c*)   	       	    	    
	    Term.Grounding_gr_key new_key
	  end
	else
	  begin
	    let new_gr_t = Subst.grounding term_db_ref (get_gr_by_map ()) term in
	    dbg D_gr_term (lazy ("T: "^(Term.to_string term)^
				 " G: "^(Term.to_string new_gr_t)^"\n")) ;
	    let curr_map_id = get_gr_map_id () in 
	    let grounding_non_gr = 
	      {
	       Term.grounding_subst_id = curr_map_id;
	       Term.grounded_term = new_gr_t; 
	     } in
	    Term.Grounding_non_gr grounding_non_gr 
	  end
      in
      Term.assign_grounding_info new_grounding_info term;
      get_prop_gr_key_assign term
*)

let rec get_prop_gr_key_assign term =
  if (Term.is_ground term) 
  then 
    get_prop_key_assign term
  else    
    begin
      try 
	let grounding = Term.get_grounding term in 
	let curr_map_id = get_gr_map_id () in 
	if (curr_map_id = grounding.Term.grounding_subst_id)
	then
	  get_prop_key_assign grounding.Term.grounded_term
	else
	  begin
	    let new_gr_t = Subst.grounding term_db_ref (get_gr_by_map ()) term in
	    dbg D_gr_term (lazy ("T: "^(Term.to_string term)^
				 " Old G: "^(Term.to_string grounding.Term.grounded_term)^
				 " G: "^(Term.to_string new_gr_t)^" MID: "^(string_of_int curr_map_id)^"\n")) ;
	    grounding.Term.grounding_subst_id <- curr_map_id;
	    grounding.Term.grounded_term <- new_gr_t; 	  
	    get_prop_key_assign grounding.Term.grounded_term
	  end
      with
      |Term.Grounding_undef ->

	  let new_gr_t = Subst.grounding term_db_ref (get_gr_by_map ()) term in
	  let curr_map_id = get_gr_map_id () in 

	  dbg D_gr_term (lazy ("T: "^(Term.to_string term)^
			       " G: "^(Term.to_string new_gr_t)^
			       " MID: "^(string_of_int curr_map_id)^"\n")) ;
	  let new_grounding =  
	
	    {
	     Term.grounding_subst_id = curr_map_id;
	     Term.grounded_term = new_gr_t; 
	   } 	      
	  in
	  Term.assign_grounding new_grounding term;
	  get_prop_key_assign new_gr_t
    end	

(* adds literal without grounding to propositional solver and to var_table *)
let get_prop_lit_assign lit =
  let atom = Term.get_atom lit in
  let atom_prop_key = get_prop_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var
    else
      prop_var_entry.prop_var
  in
  match def_lit with
  | Def(lit) -> lit
  | _ -> raise (Failure "Instantiation get_prop_lit_assign: lit is undefined")

(* adds literal without grounding to propositional solver and to var_table *)
let get_prop_lit_uc_assign lit =
  let atom = Term.get_atom lit in
  let atom_prop_key = get_prop_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var_uc
    else
      prop_var_entry.prop_var_uc
  in
  let uc_lit = 
    match def_lit with
    | Def(lit) -> lit
    | _ -> raise (Failure "Instantiation get_prop_lit_uc_assign: lit is undefined")
  in
  (* map known literal to original one *)
  update_uc_map uc_lit lit;
  (* return that lit *)
  uc_lit

(*returns prop literal;  assume that prop key is def. *)
let get_prop_lit lit =
  let atom = Term.get_atom lit in
  let atom_prop_key = Term.get_prop_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var
    else
      prop_var_entry.prop_var
  in
  match def_lit with
  | Def(lit) -> lit
  | _ -> raise (Failure "Instantiation get_prop_lit: lit is undefined")

(*returns prop literal;  assume that prop key is def. *)
let get_prop_lit_uc lit =
  let atom = Term.get_atom lit in
  let atom_prop_key = Term.get_prop_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var_uc
    else
      prop_var_entry.prop_var_uc
  in
  let uc_lit =
    match def_lit with
    | Def(lit) -> lit
    | _ -> raise (Failure "Instantiation get_prop_lit_uc: lit is undefined")
  in
  (* map known literal to original one *)
  update_uc_map uc_lit lit;
  (* return that lit *)
  uc_lit

(*returns complementary prop literal;  assume that prop key is def. *)
let get_prop_compl_lit lit =
  let atom = Term.get_atom lit in
  let atom_prop_key = Term.get_prop_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_var
    else
      prop_var_entry.prop_neg_var
  in
  match def_lit with
  | Def(lit) -> lit
  | _ -> raise (Failure "Instantiation get_prop_compl_lit: lit is undefind")

let get_prop_compl_lit_uc lit =
  let atom = Term.get_atom lit in
  let atom_prop_key = Term.get_prop_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_var_uc
    else
      prop_var_entry.prop_neg_var_uc
  in
  let uc_lit = 
    match def_lit with
    | Def(lit) -> lit
    | _ -> raise (Failure "Instantiation get_prop_compl_lit_uc: lit is undefind")
  in
  (* map known literal to original one *)
  update_uc_map uc_lit (add_compl_lit lit);
  (* return that lit *)
  uc_lit

let get_prop_gr_lit lit =
  let atom = Term.get_atom lit in
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var
    else
      prop_var_entry.prop_var
  in
  match def_lit with
  | Def(lit) -> lit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit: lit is undefind")

let get_prop_gr_lit_uc lit =
  let atom = Term.get_atom lit in
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var_uc
    else
      prop_var_entry.prop_var_uc
  in
  match def_lit with
  | Def(lit) -> lit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit: lit is undefind")



let get_prop_gr_compl_lit lit =
  let atom = Term.get_atom lit in
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_var
    else
      prop_var_entry.prop_neg_var
	
  in
  match def_lit with
  | Def plit ->
      (* Format.eprintf
	 "Literal %s is %s in simplification solver@."
	 (Term.to_string lit)
	 (PropSolver.lit_to_string solver_sim plit); *)
      plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit: lit is undefind")

let get_prop_gr_compl_lit_uc lit =
  let atom = Term.get_atom lit in
  let atom_prop_gr_key = Term.get_prop_gr_key atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_var_uc
    else
      prop_var_entry.prop_neg_var_uc
	
  in
  match def_lit with
  | Def plit ->
      (* Format.eprintf
	 "Literal %s is %s in simplification solver@."
	 (Term.to_string lit)
	 (PropSolver.lit_to_string solver_sim plit); *)
      plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit: lit is undefind")

(* adds literal after grounding to propositional solver and to var_table *)
let get_prop_gr_lit_assign lit =
  let atom = Term.get_atom lit in
  let atom_prop_gr_key = get_prop_gr_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var
    else
      prop_var_entry.prop_var
  in
  match def_lit with
  | Def plit -> plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit_assign: lit is undefind")

let get_prop_gr_lit_uc_assign lit =
  let atom = Term.get_atom lit in
  let atom_prop_gr_key = get_prop_gr_key_assign atom in
  let prop_var_entry = TableArray.get var_table atom_prop_gr_key in
  let def_lit =
    if (Term.is_neg_lit lit)
    then
      prop_var_entry.prop_neg_var_uc
    else
      prop_var_entry.prop_var_uc
  in
  match def_lit with
  | Def plit -> plit
  | _ -> raise (Failure "Instantiation get_prop_gr_lit_assign: lit is undefind")

(*--------*)
let get_grounded_atom atom = 
  try
    add_term_db (Term.get_grounded_term atom)
  with 
    Term.Grounding_undef -> 
      let _ = get_prop_gr_lit_assign atom in
      add_term_db (Term.get_grounded_term atom)

let get_grounded_lit lit = 
  if (Term.is_ground lit) 
  then 
    lit 
  else
    let atom = Term.get_atom lit in
    if (Term.is_neg_lit lit)
    then
      add_neg_atom (get_grounded_atom atom)
    else
      (get_grounded_atom atom)

let get_prop_gr_var_entry lit =
  try
    let atom = Term.get_atom lit in
    let prop_gr_key = Term.get_prop_gr_key atom in
    TableArray.get var_table prop_gr_key
  with
    Term.Grounding_undef (*Prop_gr_key_undef*) -> 
      raise (Failure (Format.sprintf "get_prop_gr_var_entry : Term.Prop_key_undef for %s@." (Term.to_string lit)))

let get_prop_var_entry lit =
    let atom = Term.get_atom lit in
    try

      let prop_key = Term.get_prop_key atom in
      TableArray.get var_table prop_key
    with
      Term.Prop_key_undef -> raise (Failure ("get_prop_var_entry : Term.Prop_key_undef: "^(Term.to_string atom)))


let get_prop_var_var_entry var_entry =
  match var_entry.prop_var with
  | Def(prop_var) -> prop_var
  | Undef -> raise (Failure "get_prop_var_var_entry: prop_var is Undef\n")

let get_prop_neg_var_var_entry var_entry =
  match var_entry.prop_neg_var with
  | Def(prop_neg_var) -> prop_neg_var
  | Undef -> raise (Failure "get_prop_neg_var_var_entry: prop_var is Undef\n")

(* (grounding of) the literal will be set as important in prop solver *)
let is_important_for_prop_lit lit =
  if (val_of_override !current_options.bmc1_incremental) && (Term.is_clock_lit lit)
  then true
  else if Important_lit.is_empty ()
  then false
  else Important_lit.is_important (Term.get_top_symb (Term.get_atom lit))
(* add activity check *)

(* the literal will be set as important in prop solver *)
let set_important_for_prop_lit lit =
  PropSolver.set_important_lit solver (get_prop_lit lit);
  PropSolver.set_important_lit solver (get_prop_gr_lit lit)
  (* ;out_str ("Setting important lit for: "^(Term.to_string lit)^"\n") *)

let set_decision_var is_decision lit = 
  PropSolver.set_decision_var solver is_decision (get_prop_lit lit);
  PropSolver.set_decision_var solver is_decision (get_prop_gr_lit lit);
  PropSolver.set_decision_var_uc solver_uc is_decision (get_prop_lit_uc lit);
  PropSolver.set_decision_var_uc solver_uc is_decision (get_prop_gr_lit_uc lit)
  


let get_lit_activity lit =
  (*  out_str ("Lit Act !\n"^(Term.to_string lit));*)
  let var_entry = get_prop_gr_var_entry lit in
  if (Term.is_neg_lit lit)
  then var_entry.neg_activity
  else var_entry.pos_activity

let lit_activity_compare l1 l2 =
  (*  out_str ("Act Compare !\n"^(Term.to_string l1)^(Term.to_string l2));*)
  compare (get_lit_activity l1) (get_lit_activity l2)

(* get truth val of lit after grounding in stored model *)

(*
let get_gr_atom_model_truth_val atom =
  let var_entry = get_prop_gr_var_entry atom in
  var_entry.truth_val
*)

(*
  let selection_fun get_prop_truth clause =
  let candidate_list = Clause.find_all get_prop_truth clause in
  let fun_list = [Term.cmp_ground; (compose_12 (~-)lit_activity_compare);
  Term.cmp_sign]
  in
  list_find_max_element (lex_combination fun_list) candidate_list

  let () = add_param_str ("Real Selection lex [-act;-num_symb]\n")
 *)


(*-----------------------*)
(*------------ assumptions -------------*)

(*
module UCLitMap = Map.Make(
  struct
    type t = prop_lit_uc
    let compare = compare_uc_lit
  end)
*)


type solver_assumptions = 
    {
     mutable sa_prop_list      : PropSolver.lit list;    (* assumptions for solver and uc solver are kept the same *)
     mutable sa_prop_uc_list   : PropSolver.lit_uc list; 
     mutable sa_fof_set        : TSet.t;     
     mutable sa_set_diff_list  : bool; 
     (* mainly work with the set but when run solve convert to list                      *)
     (* if sa_set_diff_list is false we can reuse ass_prop_list without converting again *)
   }

type solver_assumptions_env = 
    {
     mutable sae_norm_sa          : solver_assumptions; (* contain answer *)
     mutable sae_norm_soft_sa     : solver_assumptions; (* norm_sa + soft_sa *)    
     mutable sae_soft             : TSet.t;
     mutable sae_sim_sa           : solver_assumptions; (* we do not add soft nor answer *)
     mutable sae_sim_adjoint_lits : TSet.t; (* lits that should be added after simplifications *)
                                    (* soft assumptions; are subset sae_norm_sa *)
                                    (* we can remove them incrementally when unsat;     *)

(*     mutable sae_uc2fof           : term UCLitMap.t; (* we do not remove lits from this map       *) *)

     mutable sae_answer_sa        : TSet.t;

   }

let create_sa () = 
  {
   sa_prop_list       = [];  
   sa_prop_uc_list    = []; 
   sa_fof_set         = TSet.empty;     
   sa_set_diff_list   = false;    
 }

let create_sae () = 
  {
   sae_norm_sa           = create_sa (); 
   sae_norm_soft_sa      = create_sa (); 
   sae_sim_sa            = create_sa ();
   sae_sim_adjoint_lits  = TSet.empty;
   sae_soft              = TSet.empty;          
(*   sae_uc2fof            = UCLitMap.empty;*)
   sae_answer_sa         = TSet.empty;
 }

exception AssumptionsInconsistent
    
let check_consistent_with_sa sa lit = 
  if (TSet.mem (add_compl_lit lit) sa.sa_fof_set) 
  then 
    (
     dbg D_assumptions (lazy (" AssumptionsInconsistent: during adding: "^(Term.to_string lit)));
     raise AssumptionsInconsistent
    )
  else ()

(*--------------------*)

let mem_sa sa lit = 
  TSet.mem lit sa.sa_fof_set

let add_sa sa lit_list =
  let f lit = 
    check_consistent_with_sa sa lit;    
    if (mem_sa sa lit) 
    then ()
    else
      (
       sa.sa_fof_set <- TSet.add lit sa.sa_fof_set;
       sa.sa_prop_list <- (get_prop_lit_assign lit) :: sa.sa_prop_list;
       sa.sa_prop_uc_list <- (get_prop_lit_uc_assign lit) :: sa.sa_prop_uc_list;
      )
        
  in
  List.iter f lit_list

(* call before getting assumptions *)
let set_to_list_sa sa = 
  if sa.sa_set_diff_list
  then
    (
     let new_assumptions    = List.map get_prop_lit_assign (TSet.elements sa.sa_fof_set) in
     let new_assumptions_uc = List.map get_prop_lit_uc_assign (TSet.elements sa.sa_fof_set) in
     sa.sa_prop_list <- new_assumptions;
     sa.sa_prop_uc_list <- new_assumptions_uc;
     sa.sa_set_diff_list <- false
    )


let get_sa sa = 
  set_to_list_sa sa;
  (sa.sa_prop_list, sa.sa_prop_uc_list)
    
let remove_sa sa lit_list = 
  let f lit = 
    sa.sa_fof_set <- TSet.remove lit sa.sa_fof_set;
  in
  List.iter f lit_list; 
  sa.sa_set_diff_list <- true

let reset_sa sa = 
   sa.sa_prop_list       <- [];  
   sa.sa_prop_uc_list    <- []; 
   sa.sa_fof_set         <- TSet.empty;     
   sa.sa_set_diff_list   <- false
  
let assign_sa sa lit_list = 
  reset_sa sa;  
  List.iter (add_sa sa) lit_list

(*---- glb assumtions ---*)
let glb_sae = create_sae () 

(*
     mutable sae_norm_sa          : solver_assumptions; 
     mutable sae_sim_sa           : solver_assumptions;
     mutable sae_sim_adjoint_lits : TSet.t; (* lits that should be added after simplifications *)
     mutable sae_soft_sa          : TSet.t;          
                                    (* soft assumptions; are subset sae_norm_sa *)
                                    (* we can remove them incrementally when unsat;     *)

     mutable sae_uc2fof           : term UCLitMap.t; (* we do not remove lits from this map       *)

     mutable sae_answer_sa        : TSet.t;

*)    
    
let add_solver_assumptions ?(only_norm=false) ?(only_sim=false) ?(soft=false) ?(answer=false) lit_list =    
  (if (not only_sim) && (not soft) 
  then
    (
     dbg D_assumptions (lazy (" sae_norm_sa: add: "^(Term.term_list_to_string lit_list)));
     add_sa glb_sae.sae_norm_sa lit_list;)
  );

  (if (not only_norm) && (not soft) && (not answer)
  then 
    (
     dbg D_assumptions (lazy (" sae_sim_sa: add: "^(Term.term_list_to_string lit_list)));
     add_sa glb_sae.sae_sim_sa lit_list;
    )
  );
  (if (not only_sim) (* we add to norm_soft *)
  then
    (
     dbg D_assumptions (lazy (" sae_norm_soft_sa: add: "^(Term.term_list_to_string lit_list)));
     add_sa glb_sae.sae_norm_soft_sa lit_list;     
     if soft
     then
       (
        dbg D_assumptions (lazy ("sae_soft: add: "^(Term.term_list_to_string lit_list)));
        let lit_set = TSet.of_list lit_list in
        glb_sae.sae_soft <- TSet.union lit_set glb_sae.sae_soft;
       )
    )
  );
  (if answer
  then
    (
     dbg D_assumptions (lazy ("sae_answer_sa: add: "^(Term.term_list_to_string lit_list)));
     let lit_set = TSet.of_list lit_list in
     glb_sae.sae_answer_sa <- TSet.union lit_set glb_sae.sae_answer_sa;     
    )
  )
  
let remove_solver_assumptions ?(soft=false) ?(answer=false) lit_list =  
  dbg D_assumptions (lazy ("all: rm: "^(Term.term_list_to_string lit_list)));
  remove_sa glb_sae.sae_norm_sa lit_list;
  remove_sa glb_sae.sae_sim_sa lit_list;
  remove_sa glb_sae.sae_norm_soft_sa lit_list;
  (if (soft)
  then
    (
     dbg D_assumptions (lazy ("sae_soft: rm: "^(Term.term_list_to_string lit_list)));
     let lit_set = TSet.of_list lit_list in
     glb_sae.sae_soft <- TSet.diff glb_sae.sae_soft lit_set ;     
    ) 
  );
  (if answer
  then
    (
     dbg D_assumptions (lazy ("sae_answer_sa: rm: "^(Term.term_list_to_string lit_list)));
     let lit_set = TSet.of_list lit_list in
     glb_sae.sae_answer_sa <- TSet.diff glb_sae.sae_answer_sa lit_set;     
    )
  )

(* keep adjoint predicates and answers *)
let clear_solver_assumptions () = 
  glb_sae.sae_norm_sa <- create_sa ();
  glb_sae.sae_norm_soft_sa <- create_sa ();
  glb_sae.sae_sim_sa <- create_sa ();
  glb_sae.sae_soft <- TSet.empty;
  glb_sae.sae_answer_sa  <- TSet.empty
  
(*----*)
let clear_soft_assumptions () =
  remove_solver_assumptions ~soft:true (TSet.elements glb_sae.sae_soft)

let mem_soft_assumptions lit = 
  TSet.mem lit glb_sae.sae_soft

let add_soft_assumptions lit_list = 
  add_solver_assumptions ~only_norm:true ~soft:true  lit_list

let set_soft_assumptions lit_list = 
  clear_soft_assumptions ();
  add_soft_assumptions lit_list

let soft_assumptions_is_empty () = 
  TSet.is_empty glb_sae.sae_soft
    
(*----*)
let mem_assumptions lit = 
  mem_sa glb_sae.sae_norm_soft_sa lit

let is_empty_assumptions () = 
  TSet.is_empty glb_sae.sae_norm_soft_sa.sa_fof_set

(*----*)
let assign_only_norm_solver_assumptions lit_list = 
  glb_sae.sae_norm_sa <- create_sa ();
  glb_sae.sae_norm_soft_sa <- create_sa ();
  add_solver_assumptions ~only_norm:true lit_list
    
let assign_only_sim_solver_assumptions lit_list = 
  glb_sae.sae_sim_sa <- create_sa ();
  add_solver_assumptions ~only_sim:true lit_list

let assign_solver_assumptions lit_list = 
  clear_solver_assumptions ();
  add_solver_assumptions lit_list
    
(*----*)
let get_solver_fof_assumptions ~soft ~sim = 
  if sim
  then
    glb_sae.sae_sim_sa.sa_fof_set     
  else
    if soft 
    then 
      glb_sae.sae_norm_soft_sa.sa_fof_set 
    else
      glb_sae.sae_norm_sa.sa_fof_set 
     


let get_solver_assumptions ~soft ~sim = 
  if sim
  then
    let (ass, _ass_uc) = get_sa glb_sae.sae_sim_sa in
    ass
  else
    if soft 
    then 
      let (ass, _ass_uc) = get_sa glb_sae.sae_norm_soft_sa in
      ass
    else
      let (ass, _ass_uc) = get_sa glb_sae.sae_norm_sa in
      ass
        

let get_solver_uc_assumptions ~soft ~sim = 
  if sim
  then    
    let (_ass, ass_uc) = get_sa glb_sae.sae_sim_sa in
    ass_uc
  else
    if soft 
    then         
      let (_ass, ass_uc) = get_sa glb_sae.sae_norm_soft_sa in
      ass_uc
    else
      let (_ass, ass_uc) = get_sa glb_sae.sae_norm_sa in
      ass_uc

let consistent_with_assumptions ~soft ~sim lit_list = 
  let f lit = 
    if sim 
    then
      check_consistent_with_sa glb_sae.sae_sim_sa lit
    else
      if soft
      then
        check_consistent_with_sa glb_sae.sae_norm_soft_sa lit
      else
        check_consistent_with_sa glb_sae.sae_norm_sa lit
  in
  List.iter f lit_list 


let assign_sim_adjoint_lits lits =
  ignore (List.map get_prop_lit_assign lits);
  ignore (List.map get_prop_lit_uc_assign lits);
  glb_sae.sae_sim_adjoint_lits <- TSet.of_list lits

let add_sim_adjoint_lits lits =
  ignore (List.map get_prop_lit_assign lits);
  ignore (List.map get_prop_lit_uc_assign lits); 
  glb_sae.sae_sim_adjoint_lits <- TSet.union (TSet.of_list lits) glb_sae.sae_sim_adjoint_lits

let rm_sim_adjoint_lits lits =
  ignore (List.map get_prop_lit_assign lits);
  ignore (List.map get_prop_lit_uc_assign lits); 
  glb_sae.sae_sim_adjoint_lits <- TSet.diff glb_sae.sae_sim_adjoint_lits (TSet.of_list lits) 



   

(*-------------- OLD  ---------------*)
(*
let assign_solver_assumptions lit_list =
  let new_assumptions =
    normalise_assumptions (List.map get_prop_lit_assign lit_list)
  in
  
  let new_assumptions_uc =
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list)
  in
  
  (*
    Format.printf "New solver assumptions: @\n";
    
    List.iter
    (fun l -> Format.printf "%s@\n" (Term.to_string l))
    lit_list;
    
    Format.printf "@\n@.";
   *)
  
  solver_assumptions_ref := new_assumptions;
  solver_uc_assumptions_ref := new_assumptions_uc

let add_solver_assumptions lit_list =
  let new_assumptions =
    normalise_assumptions (List.map get_prop_lit_assign lit_list)
  in
  
  let new_assumptions_uc =
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list)
  in
  
  (*
    Format.printf "New solver assumptions: @\n";
    
    List.iter
    (fun l -> Format.printf "%s@\n" (Term.to_string l))
    lit_list;
    
    Format.printf "@\n@.";
   *)
  
  solver_assumptions_ref := new_assumptions@(!solver_assumptions_ref);
  solver_uc_assumptions_ref := new_assumptions_uc@(!solver_uc_assumptions_ref)



let assign_only_sim_solver_assumptions lit_list =
  
  let new_assumptions =
    normalise_assumptions (List.map get_prop_lit_assign lit_list)
  in
  
  let new_assumptions_uc =
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list)
  in
  
  (*
    Format.printf "New assumptions for simplification solver: @.";
    
    List.iter
    (fun l -> Format.printf "%s@." (Term.to_string l))
    lit_list;
   *)
  
  only_sim_solver_assumptions_ref := new_assumptions;
  solver_uc_sim_assumptions_ref := new_assumptions_uc

(*-------*)
let assign_only_norm_solver_assumptions lit_list =
  only_norm_original_assumptions_ref := lit_list;
  let new_assumptions =
    normalise_assumptions (List.map get_prop_lit_assign lit_list)
  in
  let new_assumptions_uc =
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list)
  in
  
  (*
    Format.printf "New assumptions for satisfiability solver: @.";
    
    List.iter
    (fun l -> Format.printf "%s@." (Term.to_string l))
    lit_list;
    
    Format.printf "@.";
   *)
  
  only_norm_solver_assumptions_ref:= new_assumptions;
  solver_uc_norm_assumptions_ref := new_assumptions_uc

let add_only_norm_solver_assumptions lit_list =
  only_norm_original_assumptions_ref := lit_list@(!only_norm_original_assumptions_ref);
  let new_assumptions =
    normalise_assumptions (List.map get_prop_lit_assign lit_list)
  in
  let new_assumptions_uc =
    normalise_assumptions_uc (List.map get_prop_lit_uc_assign lit_list)
  in
  
  (*
    Format.printf "New assumptions for satisfiability solver: @.";
    
    List.iter
    (fun l -> Format.printf "%s@." (Term.to_string l))
    lit_list;
    
    Format.printf "@.";
   *)
  
  only_norm_solver_assumptions_ref:= new_assumptions@(!only_norm_solver_assumptions_ref);
  solver_uc_norm_assumptions_ref := new_assumptions_uc@(!solver_uc_norm_assumptions_ref)


let assign_adjoint_preds preds =
  ignore (List.map get_prop_lit_assign preds);
  ignore (List.map get_prop_lit_uc_assign preds);
  adjoint_preds := TSet.of_list preds

(*----*)
let remove_soft_assumptions soft_ass_set = 
(* remove from norm ass *)
  let current_norm_assumptions = TSet.of_list !only_norm_original_assumptions_ref in
  (* remove the soft ones *)
  let rest_norm_assumptions = TSet.diff current_norm_assumptions soft_ass_set in
  assign_only_norm_solver_assumptions (TSet.elements rest_norm_assumptions);
(* remove from soft ass *)
  soft_assumptions.sa_set <- TSet.diff soft_assumptions.sa_set soft_ass_set
  

let clear_soft_assumptions () =
  remove_soft_assumptions soft_assumptions.sa_set

let add_soft_assumptions assumptions = 
  if !current_options.soft_assumptions
  then
    ( 
      soft_assumptions.sa_set <- TSet.union (TSet.of_list assumptions) soft_assumptions.sa_set;
      add_only_norm_solver_assumptions assumptions
     )
    
let set_soft_assumptions assumptions =
  if !current_options.soft_assumptions
  then 
    (
     clear_soft_assumptions ();
     add_soft_assumptions assumptions
    )


let mem_soft_assumptions lit = 
  TSet.mem lit soft_assumptions.sa_set

*)


(*-------------Add clause to solver----------------*)

(*----- Simpifications of grounded clauses before adding to SAT -----*)
let gr_norm_order l1 l2 =
  let cmp =
    (Term.compare (Term.get_atom l1) (Term.get_atom l2))
  in 
  if cmp = cequal
  then
    Term.cmp_sign l1 l2
  else
    cmp


(* we assume that the list is sorted so lits with the same atoms are together*)
exception GrTaut
let rec gr_remove_dupl_taut gr_lit_list =
  match gr_lit_list with
  | h1:: h2:: tl ->
      if h1 == h2
      then gr_remove_dupl_taut (h2:: tl)
      else
	if ((Term.get_atom h1) == (Term.get_atom h2))
	then
	  raise GrTaut (* if h1 h2 would have the same sign then h1==h2*)
	else (h1:: (gr_remove_dupl_taut (h2:: tl)))
  |[h] -> [h]
  |[] -> []


(* we keep all prop clauses in a trie (after normalisation) *)

module GrTrieKey =
  struct
    type t = Term.term
    let compare = gr_norm_order
  end

module GrTrieM = Trie_func.Make(GrTrieKey)

let gr_trie_ref = ref (GrTrieM.create ())

let reset_gr_trie () = 
  gr_trie_ref := GrTrieM.create ()

let rec gr_lit_list_is_subsumed lit_list =
  try
    let _ = (GrTrieM.long_or_in lit_list !gr_trie_ref) in
    true
  with
    Not_found ->
      (match lit_list with
      | l:: tl ->
	  gr_lit_list_is_subsumed tl
      |[] -> false
      )


(* TODO: in the trie we can not add short lists, but this would be useful...*)
let rec add_to_gr_trie input_gr_lit_list =
  let gr_lit_list = List.sort gr_norm_order input_gr_lit_list in
  try
    dbg D_gr_trie (lazy ("adding: "^(Term.term_list_to_string gr_lit_list)));
    gr_trie_ref:= GrTrieM.add gr_lit_list gr_lit_list !gr_trie_ref
  with
    
    (* Discard clause if it subsumes an existing clause *)
  | Trie_func.Trie_add_short_kyelist ->
      gr_trie_ref:= GrTrieM.remove_short gr_lit_list !gr_trie_ref;
      dbg D_gr_trie (lazy ("removing: "^(Term.term_list_to_string gr_lit_list)));
      add_to_gr_trie gr_lit_list
      (* Format.eprintf
	 "Clause %a backward subsumes in propositional trie, skipped@."
	 pp_prop_lit_list prop_lit_list; *)
      
      (* Format.eprintf
	 "Clauses in trie:@\n%a@."
	 pp_prop_lit_list_list
	 (PropTrieM.all_elem
	 (PropTrieM.find_short prop_lit_list !prop_trie_ref)) *)
	
	(* These won't happen if key has been checked before with
	   long_or_in *)
  | Trie_func.Trie_add_leaf_extension -> 
      (dbg D_gr_trie (lazy ("Trie_add_leaf_extension: "^(Term.term_list_to_string gr_lit_list)));)
  | Trie_func.Trie_add_already_in -> 
      (dbg D_gr_trie (lazy ("Trie_add_already_in: "^(Term.term_list_to_string gr_lit_list)));)
      

exception GrSubsumed

(* We can return an empty list, this must be caught by the caller and
   must raise exception Unsatisfiable_gr_na there. This is
   because the unsat core solver must also have the empty clause and
   it must be associated with some first - order clause only the caller
   knows. *)

let simplify_gr_lit_list gr_lit_list =
  let sorted = List.sort gr_norm_order gr_lit_list in
  let new_list = gr_remove_dupl_taut sorted in
  if new_list = []
  then
    (
     
     (* Format.eprintf "Clause simplified to empty clause in simplify_prop_lit_list@."; *)
     
     (* Check this in add_clause_to_solver, because empty clause must
	be added to unsat core solver and mapped to first - oder clause
	there *)
     (* raise PropSolver.Unsatisfiable *)
     []
    )
  else
    if (gr_lit_list_is_subsumed new_list)
    then
      raise GrSubsumed
    else
      new_list

(*      prop_lit_list*)

(*
  let norm_add_to_prop_solver solver prop_lit_list =
  try
  (PropSolver.add_clause solver (normalise_prop_lit_list prop_lit_list);
  num_in_prop_solver:=!num_in_prop_solver +1)
  with
  PropTaut -> ()
 *)

(*----- Simpifications of Propositional clauses before adding to SAT -----*)

let prop_norm_order pl1 pl2 =
  let cmp =
    (compare (PropSolver.lit_var solver pl1) (PropSolver.lit_var solver pl2))
  in
  if cmp = cequal
  then
    compare (PropSolver.lit_sign solver pl1) (PropSolver.lit_sign solver pl2)
  else
    cmp

(* we assume that the list is sorted so lits with the same atoms are together*)
exception PropTaut
let rec prop_remove_dupl_taut plit_list =
  match plit_list with
  | h1:: h2:: tl ->
      if h1 == h2
      then prop_remove_dupl_taut (h2:: tl)
      else
	if ((PropSolver.lit_var solver h1) = (PropSolver.lit_var solver h2))
	then
	  raise PropTaut (* if h1 h2 would have the same sign then h1==h2*)
	else (h1:: (prop_remove_dupl_taut (h2:: tl)))
  |[h] -> [h]
  |[] -> []


(*
(* we keep all prop clauses in a trie (after normalisation) *)

module PropTrieKey =
  struct
    type t = PropSolver.lit
    let compare = prop_norm_order
  end

module PropTrieM = Trie_func.Make(PropTrieKey)

let prop_trie_ref = ref (PropTrieM.create ())

let rec prop_lit_list_is_subsumed lit_list =
  try
    let _ = (PropTrieM.long_or_in lit_list !prop_trie_ref) in
    true
  with
    Not_found ->
      (match lit_list with
      | l:: tl ->
	  prop_lit_list_is_subsumed tl
      |[] -> false
      )
*)

let rec pp_prop_lit_list ppf = function
  | [] -> ()
  | [e] -> Format.fprintf ppf "%a" (PropSolver.pp_lit solver) e
  | e:: tl ->
      Format.fprintf ppf "%a " (PropSolver.pp_lit solver) e;
      pp_prop_lit_list ppf tl

let rec pp_prop_lit_list_list ppf = function
  | [] -> ()
  | [e] -> Format.fprintf ppf "%a" pp_prop_lit_list e
  | e:: tl ->
      Format.fprintf ppf "%a@\n" pp_prop_lit_list e;
      pp_prop_lit_list_list ppf tl

let rec pp_clause_list ppf = function
  | [] -> ()
  | [c] -> Format.fprintf ppf "%s" (Clause.to_string c)
  | c:: tl ->
      Format.fprintf ppf "%s@\n" (Clause.to_string c);
      pp_clause_list ppf tl

let rec pp_unsat_core ppf = function
  | [] -> ()
  | [e] -> Format.fprintf ppf "%d" e
  | e:: tl -> Format.fprintf ppf "%d, " e; pp_unsat_core ppf tl

(*--------------------------------------------------*)

(*------------------- main solve -------------------*)
(* in solve extra_assumptions are fof lits, lits are not grounded before transforming to prop *)
 
let solve ?(solver_in = solver) ?(soft = false) ?(reset = false) ?(extra_assumptions=[]) () =
  let sim = false (* PropSolver.is_simplification solver *) in
  consistent_with_assumptions ~sim ~soft extra_assumptions;
  let extra_assumptions_prop = List.map get_prop_lit_assign extra_assumptions in
  let all_assumptions = (extra_assumptions_prop@(get_solver_assumptions ~sim ~soft)) in
  dbg D_solve (lazy 
		 ("Assumptions: "^
		  (PropSolver.lit_list_to_string solver_in
		     all_assumptions)^ "\n")); 
  PropSolver.solve_assumptions ~reset:reset solver_in all_assumptions 
    
(*-------*)

 let fast_solve ?(solver_in = solver_sim) ?(soft = false) assumptions = 
(* DEBUG *) (* let fast_solve ?(solver_in = solver) ?(soft = false) assumptions = *)
  try
    let sim = PropSolver.is_simplification solver_in in
    consistent_with_assumptions ~sim ~soft assumptions;
    let assumptions_prop = List.map get_prop_lit_assign assumptions in
    let all_assumptions = (assumptions_prop@(get_solver_assumptions ~soft ~sim)) in
    PropSolver.fast_solve solver_in all_assumptions
  with
    AssumptionsInconsistent -> PropSolver.FUnsat
   

(*------ olny used in this module ---------------*)
(*
let solve_prop_assumptions ?(reset = false) solver prop_assumptions =
  try
(*    let ass = normalise_assumptions (assumptions@(get_solver_assumptions solver)) in *)

    let sim = PropSolver.is_simplification solver in

    consistent_with_assumptions sim assumptions;
    let all_assumptions = 
      prop_assumptions
      @
        (get_solver_assumptions sim) 
    in
    dbg D_solve (lazy 
		   ("solve_assumptions: Assumptions: "^
		    (PropSolver.lit_list_to_string solver all_assumptions)^ "\n"));     
    PropSolver.solve_assumptions ~reset: reset solver all_assumptions
  with
    AssumptionsInconsistent -> PropSolver.Unsat
*)

(*--------*)

let prop_lit_val_to_bool lit_val = 
  match lit_val with 
  |PropSolver.True  -> true
  |PropSolver.False -> false
  |PropSolver.Any   -> 
      (
       out_warning "instantiatin_sel.ml: PropSolver.Any should be eliminated";
       true
      )

let get_solver_lit_val lit = 
  let lit_prop = get_prop_lit_assign lit in 
  let lit_val = PropSolver.lit_val solver lit_prop in
  dbg D_trace (lazy ("get_solver_lit_val: lit: "^(Term.to_string lit)
                     ^" lit_prop "^(PropSolver.lit_to_string solver lit_prop)
                     ^" val: "^(PropSolver.lit_val_to_string lit_val)) );
  prop_lit_val_to_bool lit_val

let get_solver_lit_val_gr lit = 
  let gr_lit = get_grounded_lit lit in
  get_solver_lit_val gr_lit
   
(*---------------------------------------------------------------------------*)
(* all assumptions including extra_assumptions should be exactly the same as in the last call to solve *)
let get_unsat_core ~soft ?(extra_assumptions=[]) () =
  let start_time = Unix.gettimeofday () in
  let sim = PropSolver.is_simplification solver in
  consistent_with_assumptions ~sim ~soft extra_assumptions;
  let extra_assumptions_prop_uc = List.map get_prop_lit_uc_assign extra_assumptions in  
  let assumptions = (extra_assumptions_prop_uc@(get_solver_uc_assumptions ~sim ~soft)) in
  match
    (     
     try
       dbg D_solve (lazy (" get_unsat_core"));  
       (* Run unsat core solver with assumptions *)
       PropSolver.solve_assumptions_uc solver_uc assumptions
	 
	 (* Catch exception and return normally *)
     with 
       Unsatisfiable_gr_na -> PropSolver.Unsat	 
    )
      
  with    
    (* Should return unsat, but check *)
  | PropSolver.Unsat ->
      
      (* Get the unsat core as a list of clause ids *)
      let unsat_core_ids = list_remove_int_duplicates (PropSolver.get_conflicts solver_uc) in
      
      let end_time = Unix.gettimeofday () in
      add_float_stat (end_time -. start_time) prop_unsat_core_time;
      
      (* Get first-order clauses from clause ids *)
      let unsat_core_clauses, uc_assumptions =
	List.fold_left
	  (fun (ca, aa) c_id ->
	    try
	     (* (Hashtbl.find solver_uc_clauses c) :: ca, aa *)
	      (puf_get_clause c_id) :: ca, aa 
	    with Not_found ->
	      ca, c_id :: aa)
	  ([], [])
	  unsat_core_ids
      in
      
      (* Format.eprintf
	 "Assumptions in unsat core: %a @."
	 (pp_any_list Format.pp_print_int " ") assumptions; *)

      (* map assumptions into first-order ones *)
      let uc2t_assumptions accum int_lit =
        try
          (* create abstract variable from int representation *)
          let uc_lit = PropSolver.create_lit_uc solver_uc (PropSolver.bool_to_sign (int_lit < 0)) (abs int_lit) in
      
          (* find correspondence in the map and add it *)
          (UCLitMap.find uc_lit !uc2tMap)::accum
        with (* not registered -- do nothing *)
        | Not_found -> accum
      in
      
      (* Return assumptions and clauses in unsat core *)
      let unsat_core = UnsatCore.create (List.fold_left uc2t_assumptions [] uc_assumptions) unsat_core_clauses in
      dbg_env D_print_uc_time 
        (fun () ->
          let delta = Unix.gettimeofday () -. start_time in
          uc_total_time := !uc_total_time +. delta;
          uc_session_time := !uc_session_time +. delta;
          out_str ("UC size "^(string_of_int (List.length unsat_core_clauses))^" extracted: time "
                   ^(string_of_float delta)^", session "^(string_of_float !uc_session_time)
                   ^", total "^(string_of_float !uc_total_time));
        );
      dbg_env D_print_unsat_core (fun () -> UnsatCore.print unsat_core; );
      unsat_core
	
	(* Must not return sat when other solver returns unsat *)
  | PropSolver.Sat ->
      raise (Failure "Unsat core solver returned satisfiable")
(* failwith "Unsat core solver returned satisfiable" *)

(*-------------------------------------------------------------*)
            (* Multiple unsat core support *)
(*-------------------------------------------------------------*)

exception MultipleUnsat of UnsatCore.unsat_core list



(* flag that forces the unsat core count *)
let collect_unsat_cores = ref false

(* let given_clause_ref = ref [] *)

(*
(* keep the list of all the assumptions *)
let current_assumptions = ref TSet.empty

(* unconditional assumptions *)
let unconditonal_assumptions = ref TSet.empty
*)

(* maximal number of collected unsat cores *)
let max_unsat_cores_number = ref 0

(* collected unsat cores *)
let unsat_cores = ref []

(* set the maximal number of unsat cores *)
let set_max_unsat_cores_number n =
  out_str ("\nProduce not more than "^(string_of_int n)^" unsat cores");
  max_unsat_cores_number := n

(* return true if the maximal number of unsat cores is exceeded *)
let max_number_exceeded () =
  if !max_unsat_cores_number = 0
  then (* not set -- not exceeded *)
    false
  else (* check the number of unsat cores *)
    (List.length !unsat_cores) >= !max_unsat_cores_number

(* add lit to given set *)
let add_lit_to_set set lit = TSet.add lit set

let print_assumptions assumptions str =
  Format.printf "@.Assumptions (%s):@." str;
  TSet.iter (function t -> Format.printf "%s@." (Term.to_string t)) assumptions;
  Format.printf "@."

  
(* collect unsat cores for the next run *)
let init_multiple_run_mode all_assumptions uncond_assumptions =
  dbg D_unsat_core (lazy "clear_multiple_run_mode");
  (* switch on multiple unsat core mode *)
  collect_unsat_cores := true
      

(*
(* collect unsat cores for the next run *)
let init_multiple_run_mode all_assumptions uncond_assumptions =
  (* switch on multiple unsat core mode *)
  collect_unsat_cores := true

  (* init assumption sets *)
  current_assumptions := List.fold_left add_lit_to_set TSet.empty all_assumptions;

  (* print_assumptions !current_assumptions "init current assumptions"; *)
  unconditonal_assumptions := List.fold_left add_lit_to_set TSet.empty uncond_assumptions
  (* print_assumptions !unconditonal_assumptions "init unconditonal assumptions" *)
*)

(* returns true if there are no assumptions other than unconditional *)
let is_empty_model () =
  TSet.is_empty glb_sae.sae_soft

  (* TSet.equal !current_assumptions !unconditonal_assumptions *)


(* update assumptions from a given insat core *)
let reload_assumptions uc_assumptions =
  (* make a set of assumptions *)

  let uc_set' = TSet.of_list uc_assumptions in

(*
(*   print_assumptions uc_set' "unsat_core"; *)

  (* remove unconditional assumptions from it *)
  let uc_set = TSet.diff uc_set' !unconditonal_assumptions in
*)

  let uc_set = TSet.inter uc_set' glb_sae.sae_soft in

  remove_solver_assumptions ~soft:true (TSet.elements uc_set);

  dbg_env D_unsat_core
    (fun () ->
      print_assumptions uc_set "sfot: "; 
    );
  
(* remove all conditional assumptions from the set *)
(*
  current_assumptions := TSet.diff !current_assumptions uc_set;
  
 (* print_assumptions !current_assumptions "current assumptions"; *)

  (* make list of assumptions *)
  let curr_assumptions = TSet.elements !current_assumptions in
  (* update the assumptions in the prop solver (the call will rewrite them) *)
  assign_only_norm_solver_assumptions curr_assumptions;
  (* return true if there were only unconditional assumptions *)
*)
  (TSet.is_empty uc_set)


(* process the unsat result: throw the exception in a normal mode, *)
(* save the unsat core and continue if possible in multi-core mode *)
(* if soft assumptions are used, and some of them are in the UC, remove *)
(* them and continue; else raise Unsat *)
(* The interaction between the 2 modes is quite involved here *)
let process_unsat_result ?(soft = true) () =
  dbg D_unsat_core (lazy "process_unsat_result");
  if (val_of_override !current_options.bmc1_incremental) || !current_options.soft_assumptions 
(* DT part; TODO check this *)
  then
    begin

  (* completely process soft assumptions.       *)
  (* Return [] if nothing to do (keep going) or *)
  (* [uc] if UNSAT exception should be raised   *)
      let process_soft () =
  (* get the unsat core *)
        let unsat_core = get_unsat_core ~soft () in

  (* check soft assumptions *)
        let uc_assumptions = UnsatCore.get_assumptions unsat_core in
        let uc_soft_sa = TSet.inter (TSet.of_list uc_assumptions) glb_sae.sae_soft in
        
        let no_soft = TSet.is_empty uc_soft_sa in
        (* no soft assumptions: report, return UC as a sign of UNSAT *)
        if no_soft
        then 
          (
           dbg D_assumptions (lazy ("No soft assumptions found; raise Unsat"));
           [unsat_core]
          )
        else 
          ( (* soft assumptions: remove them from assumptions, continue *)
            (* assumptions to be removed from solver *)
            dbg D_assumptions (lazy ("Found soft assumptions: "
                                          ^(Term.term_list_to_string (TSet.elements uc_soft_sa))^"; keep going"));
            
            (* remove the soft ones *)
            remove_solver_assumptions ~soft:true (TSet.elements uc_soft_sa);
  
(*
  (* get the set of all current assumptions *)
      let current_assumptions = TSet.of_list !only_norm_original_assumptions_ref in
   
      let rest_assumptions = TSet.diff current_assumptions s_assumptions in
      (* load the rest back to solver *)
      assign_only_norm_solver_assumptions (TSet.elements rest_assumptions);
      (* return nothing to show that we have to keep going *)
*)
            []
           )
  in
  let process_multiple_unsat unsat_core =
    dbg D_unsat_core (lazy "process_multiple_unsat");

    (* save unsat core *)
    unsat_cores := unsat_core::!unsat_cores;
    (* print_unsat_core unsat_core; *)
    (* reload assumptions *)
    if (max_number_exceeded ())
    then
    (
      dbg D_unsat_core (lazy ((string_of_int (List.length !unsat_cores))^" unsat cores collected, returning"));
      raise (MultipleUnsat !unsat_cores)
    );
    if (reload_assumptions (UnsatCore.get_assumptions unsat_core))
    then (* the last core was due to the unconditional assumptions *)

    ( (*KK: TODO: the same exception for unsat under uncoditional assumptions and unsat for max_number exceeeded ??? *)
      dbg D_unsat_core (lazy "no assumptions depending on model");
      raise (MultipleUnsat !unsat_cores)
    )
  in
  (* completely check unsat reason *)
  let remove_unsat_reason () =
    (* we are here if either soft assumptions, or multiple UNSAT, or both *)
    if not (TSet.is_empty glb_sae.sae_soft)
    then (* process soft assumptions *)
    (
      let result = process_soft () in
      (* if we have a real UNSAT... *)
      if (list_non_empty result)
      then
      (
        if !collect_unsat_cores
        then (* AND need to check multiple assumptions -- pass the output UC *)
          process_multiple_unsat (List.hd result)
        else (* no MultiUnsat -- just raise the exception *)
          raise Unsatisfiable_gr
      )
      (* else -- keep going *)
    )
    else (* process multiple UNSAT only -- as before *)
      process_multiple_unsat (get_unsat_core ~soft ())
  in
  (* check whether we collecting unsat cores *)
  if !collect_unsat_cores || not (TSet.is_empty glb_sae.sae_soft)
  then (* remove the unsat reason and continue if possible *)
    (
     remove_unsat_reason ()
    )
  else (* just throw an exception *)
    raise Unsatisfiable_gr

   end (* --bmc1_incremental *)
 else 
   raise Unsatisfiable_gr



(* process the unsat result: do nothing in a normal mode, *)
(* check unsat cores and throw in multi-core mode *)
let process_final_sat_result () =
  dbg D_unsat_core (lazy "process_final_sat_result");
  if not !collect_unsat_cores
  then ()
  else (* check whether unsat cores are non-empty *)
    if (!unsat_cores = [])
    then ()
    else raise (MultipleUnsat !unsat_cores)

(* collect unsat cores for the next run *)
let clear_multiple_run_mode () =
  dbg D_unsat_core (lazy "clear_multiple_run_mode");
  collect_unsat_cores := false;
  unsat_cores := []


(*------------------- Answers -----------*)
(* assume ~answer(..)\bot                              *)
(* when unsat minimise set of ~answer(...)\bot and output *)
(* disjunction of corresponding answers, \bot -> X0)  *)
(* Later add more general answers: vars mapped to constants  *)
(* for this we need rewrite normalisation so unifed literals would be the same *)
(* or since there are only one answer literal in a clause, make them first in the clause and rename *)

module PropHashKey =
  struct
    type t = PropSolver.lit
    let equal = (=)
    let hash = PropSolver.lit_var solver
  end

(* will have several uses*)
module PropHash = Hashtbl.Make(PropHashKey)

(* maps prop assump -> fo assumpt *)

(* let answer_assumptions_table = ref (PropHash.create 41) *)

(* TODO: check *)
(* we negate the grounding of the answer lit before adding to the ground sovler assumtions *)
(* we use (answer \bot) at the moment *)
let add_answer_assumption answer =
  let answer_bot = Term.get_grounded_term answer in
(*  let gr_compl_answer = get_prop_gr_compl_lit answer_bot in*)
  
  
  if (TSet.mem answer_bot glb_sae.sae_answer_sa)
  then ()
  else
    begin
      add_solver_assumptions ~answer:true [answer_bot]
(*
      PropHash.add !answer_assumptions_table gr_compl_answer answer_bot;
      answer_assumptions_ref:= gr_compl_answer:: (!answer_assumptions_ref);
      answer_assumptions_uc_ref:=
	(get_prop_gr_compl_lit_uc answer_bot):: (!answer_assumptions_uc_ref)
 *)
    end

(* TODO adapt below *)
let minimise_answers () = ()
(*
  let rec min_unsat_subs' needed =
    match !answer_assumptions_ref with
    | h:: tl ->
	answer_assumptions_ref := needed@tl;
	
	(* debug *)
	(*	out_str "Assumptions: ";
	  let f ass =
	  let answer_atom = PropHash.find !answer_assumptions_table ass in
	  out_str ((Term.to_string answer_atom)^",");
	  in
	  List.iter f !answer_assumptions_ref;
	  out_str "\n";
	 *)
	(* end debug *)
	begin
	  match (solve ()) with
	  | PropSolver.Unsat ->
	      (
	       answer_assumptions_ref:= tl;
	       PropHash.remove !answer_assumptions_table h;
	       min_unsat_subs' needed
	      )
	  | PropSolver.Sat ->
	      (
	       answer_assumptions_ref:= tl;
	       min_unsat_subs' (h:: needed)
	      )
	end
    |[] -> needed
  in
  let needed = min_unsat_subs' [] in
  answer_assumptions_ref:= needed
*)
(* TODO *)
(*
(* we assume that the solver is unsat under answer assumptions and we minimise them*)
let minimise_answers () =
  let rec min_unsat_subs' needed =
    match !answer_assumptions_ref with
    | h:: tl ->
	answer_assumptions_ref := needed@tl;
	
	(* debug *)
	(*	out_str "Assumptions: ";
	  let f ass =
	  let answer_atom = PropHash.find !answer_assumptions_table ass in
	  out_str ((Term.to_string answer_atom)^",");
	  in
	  List.iter f !answer_assumptions_ref;
	  out_str "\n";
	 *)
	(* end debug *)
	begin
	  match (solve ()) with
	  | PropSolver.Unsat ->
	      (
	       answer_assumptions_ref:= tl;
	       PropHash.remove !answer_assumptions_table h;
	       min_unsat_subs' needed
	      )
	  | PropSolver.Sat ->
	      (
	       answer_assumptions_ref:= tl;
	       min_unsat_subs' (h:: needed)
	      )
	end
    |[] -> needed
  in
  let needed = min_unsat_subs' [] in
  answer_assumptions_ref:= needed
*)

(* replace bot with X0 in term *)

let add_fun_term symb args =
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let term_var var = TermDB.add_ref (Term.create_var_term var) term_db_ref

let bot_to_var term =
  let rec f t =
    match t with
    | Term.Fun(symb, args, _) ->
	let symb_type = Symbol.get_val_type_def symb in
	if (symb == Symbol.symb_bot)
	then
	  (* replace bot by first var of bot type *)
	  term_var (Var.get_first_var symb_type)
	else
	  (let new_args = Term.arg_map f args in
	  add_fun_term symb (Term.arg_to_list new_args)
	  )
    | _ -> t
  in
  f term

(* if we two answers answer_1 anser2,.. are unifiable *)
(* then we can remove one of them and apply unif to the rest of lit list *)

(*  let bound_a_list = List.map (fun a -> (1,a)) a_list in*)

let bound_list b list = List.map (fun a -> (b, a)) list
let unbound_list list = List.map (fun (_, a) -> a) list

let reduce_answer_bl_list bl bound_a_list =
  let rec reduce_answer_bl_list' bl tried rest =
    match rest with
    | h:: tl ->
	begin
	  try
	    let mgu = Unif.unify_bterms bl h in
	    Some(mgu)
	  with
	    Unif.Unification_failed ->
	      reduce_answer_bl_list' bl (h:: tried) tl
	end
    |[] -> None
  in
  reduce_answer_bl_list' bl [] bound_a_list

(* very inefficient but should be ok for reducing small disjunctive answers*)
let rec reduce_answer_list a_list =
  let ba_list = bound_list 1 a_list in
  let rec reduce_answer_list' non_unifable rest =
    match rest with
    | h:: tl ->
	begin
	  match (reduce_answer_bl_list h tl) with
	  | Some (mgu) ->
	      let new_a_list =
		SubstBound.apply_bsubst_btlist term_db_ref mgu	(non_unifable@tl)
	      in
	      reduce_answer_list new_a_list
	  | None ->
	      reduce_answer_list' (h:: non_unifable) tl
		
	end
    |[] ->
	non_unifable
  in
  reduce_answer_list' [] ba_list

let get_answer () =
  minimise_answers ();
  let answer_bot_list = TSet.elements glb_sae.sae_answer_sa in
(*
  let answer_bot_list =
    PropHash.fold (fun _ answer_bot rest -> answer_bot:: rest)
      !answer_assumptions_table []
  in
*)
  let answer_list = List.map bot_to_var answer_bot_list in
  let reduced_bound_list = reduce_answer_list answer_list in
  unbound_list reduced_bound_list

let out_answer_stream s =
  let answer_list = get_answer () in
  let answer_atom_to_stream stream answer =
    let args = Term.arg_to_list (Term.get_args answer) in
    stream.stream_add_char '[';
    list_to_stream stream Term.to_stream args ",";
    stream.stream_add_char ']'
  in
  let answer_list_to_stream a_list =
    if ((List.length a_list) > 1)
    then
      begin
	s.stream_add_char '(';
	list_to_stream s answer_atom_to_stream a_list "|";
	s.stream_add_char ')';
      end
    else
      begin
	if ((List.length a_list) =1)
	then
	  answer_atom_to_stream s (List.hd a_list)
	else ()
      end
  in
  s.stream_add_char '\n';
  s.stream_add_str "% SZS answers Tuple [";
  answer_list_to_stream answer_list;
  s.stream_add_str "]";
  s.stream_add_str " for ";
  list_to_stream s (fun stream string -> stream.stream_add_str string) !current_options.problem_files ",";
  s.stream_add_str "\n"

let out_answer () = out_answer_stream stdout_stream

(*-------End answers----------------------------------*)

(*
(* A clause in the sat solver as a list of literals *)
  module PropClause =
  struct

(* An arbitrarily sorted list of propositional literals *)
  type t = PropSolver.lit list

(* Use equality on lists *)
  let equal = (=)

(* Use polymorphic hash function on atoms, since no clause in the
   solver contains a literal and its negation *)
  let hash clause =
  Hashtbl.hash (List.map (PropSolver.lit_var solver) clause)

  end

(* A hash table over propositional clauses *)
  module PropClauseHashtbl = Hashtbl.Make(PropClause)
 *)

(*

  let add_clause_to_solver_and_solver_uc
  add_clause_to_solver
  add_clause_to_solver_uc
  clause
  prop_clause
  prop_clause_uc =

  (

  try

(* Add new clause to solver *)
  add_clause_to_solver prop_clause

(* Continue on unsatisfiable, we must add clause also to unsat
   core solve, which raises the same exception *)
  with PropSolver.Unsatisfiable ->

(* Format.eprintf
   "Unsatisfiable with added clause@." *)

  ()

  );

(* Add new clause to unsat core solver and get id  *)
  let clause_id =
  add_clause_to_solver_with_id prop_clause_uc
  in

  (

  match clause_id with

(* Clause was discarded in solver *)
  | None -> ()

(* Clause has an ID in solver *)
  | Some i ->

  (

(* Format.eprintf
   "Added clause to UC solver as %d:@\n%s@."
   i
   (Clause.to_string clause); *)

(* Map ID in solver to first-order clause *)
  Hashtbl.add solver_uc_clauses i clause

  )
  )

 *)

let rec pp_prop_lit_pair_list ppf = function
  | [] -> ()
  | [(p, q)] ->
      Format.fprintf ppf
	"(%a, %a)"
	(PropSolver.pp_lit solver) p
	(PropSolver.pp_lit solver) q
  | (p, q):: tl ->
      Format.fprintf ppf
	"(%a, %a)"
	(PropSolver.pp_lit solver) p
	(PropSolver.pp_lit solver) q;
      pp_prop_lit_pair_list ppf tl

(*--------------------------------------------------------------*)


(* adds both versions of the clauses before and after grounding *)
(* first version is used for simplifications *)
exception PropImplied


(*
let add_clause_to_solver clause =
  
  (* Skip if clause already in solver *)
(*
  if (Clause.in_prop_solver clause) 
  then
    (dbg D_add_clause (lazy ("Clause "^(Clause.to_string clause)^" is already in solver, skipping")))
  else
*)
    (
     dbg D_add_clause (lazy ("Adding clause "^(Clause.to_string clause)^" to solver"));

     (* Dump propositional clause *)
     if !current_options.dbg_dump_prop_clauses then
       Format.fprintf
	 (get_prop_clauses_dump_formatter ())
	 "c First-order clause %a@."
	 Clause.pp_clause clause;
     
     (* Mark clause as added to the solver *)
     Clause.assign_in_prop_solver true clause;
     
     (* Get literals from clause *)
     let lits = Clause.get_literals clause in
     
     (* Map clause literals to grounded propositional literals *)
     let prop_gr_lit_list =
       List.map get_prop_gr_lit_assign lits
     in
     
     (* Dump propositional clause *)
     if !current_options.dbg_dump_prop_clauses then
       Format.fprintf
	 (get_prop_clauses_dump_formatter ())
	 "c Grounded to clause %a@."
	 (PropSolver.pp_lit_list_dimacs solver) prop_gr_lit_list;
     
     (* Map clause literals to grounded propositional literals in
	unsat core solver *)
     let prop_gr_lit_uc_list =
       List.map get_prop_gr_lit_uc_assign lits
     in
     
     (* Make association list of literals in satsisfiability solver
	to literals in unsat core solver
	
	This association list is only needed locally in this function
	to convert the possibly simplifed propositional clause in the
	satisfiability solver to a clause in the unsat core solver. *)
     let prop_gr_lit_to_uc =
       List.combine prop_gr_lit_list prop_gr_lit_uc_list
     in
     
     (* Map clause literals to propositional literals grounded by
	variable *)
     let prop_lit_list = List.map get_prop_lit_assign lits in
     
     (* Map clause literals to propositional literals grounded by
	variable in unsat core solver *)
     let prop_lit_uc_list =
       List.map get_prop_lit_uc_assign lits
     in
     
     (* Make association list of literals in satsisfiability solver
	to literals in unsat core solver
	
	This association list is only needed locally to convert the
	possibly simplifed propositional clause in the satisfiability
	solver to a clause in the unsat core solver *)
     let prop_lit_to_uc =
       List.combine prop_lit_list prop_lit_uc_list
     in
     
     (* Mark propositional variables as in solver *)
     let f lit =
       let var_entry = get_prop_var_entry lit in
       var_entry.in_solver_sim <- true in
     List.iter f lits;
     
     (*  Commented *)
     (* Propositional implication  is not compatible with prop_subsumtion:*)
     (* an instance of a subsumed clause can imply an instance of the new clause*)
     (* let lits_in_solver_sim =
	let f lit =
	let var_entry = get_prop_var_entry lit in
	var_entry.in_solver_sim in
	List.find_all f lits in
	let compl_lit_list = List.map get_prop_compl_lit lits_in_solver_sim in
	num_of_fast_solver_calls:=!num_of_fast_solver_calls +1;
	match (fast_solve solver_sim compl_lit_list)
	with
	| PropSolver.FUnsat ->
	((*num_prop_implied:=!num_prop_implied+1; *)
	(*       out_str ("Prop Implied: "^(Clause.to_string clause)^"\n");*)
	raise PropImplied)
	| PropSolver.FSat | PropSolver.FUnknown -> *)
     (* debug*)
     (* let str = list_to_string PropSolver.lit_to_string prop_gr_lit_list ";" in
	out_str_debug ("Clause: "^(Clause.to_string clause)^"\n"
	^"Prop Clause:"^str^"\n");*)
     (*  debug *)
     (*  out_str ("Old Clause: "^(PropSolver.lit_list_to_string prop_gr_lit_list)^"\n");*)
     (* end Commented*)
     
     (
      
      try
	
	(* Propositionally simplify list of grounded literals *)
	let simpl_gr_lit_list =
	  simplify_prop_lit_list prop_gr_lit_list
	in


	(* Catch simplification to empty clause *)
	if simpl_gr_lit_list = [] 
	then	  
	  (
	   dbg D_add_clause (lazy ("empty clause from"^(Clause.to_string clause)));
	   
	   (* Add empty clause to unsat core solver and get id *)
	   let clause_id =
	     PropSolver.add_clause_with_id solver_uc None []
	   in
	   
	   (
	    
	    match clause_id with
	      
	      (* Clause was discarded in solver *)
	    | None ->
		
		(
		 dbg D_add_clause (lazy ("Clause was discarded by solver1 "^(Clause.to_string clause)));
		 out_warning ("The empty clause was discarded by solver \n");
		 (* Format.eprintf
		    "Clause %a discarded in solver@\n@,"
		    Clause.pp_clause
		    clause *)
		 
		)
		  
		  (* Clause has an ID in solver *)
	    | Some i ->
		
		(
		 
		 (* Map ID in solver to first-order clause *)
		 Hashtbl.add solver_uc_clauses i clause;
		 
		 dbg D_add_clause (lazy ("Clause: "^(Clause.to_string clause)^" solver id 1: "^(string_of_int i)));
		 (* Assign ID to clause
		    
		    Clauses are only added to the solver once,
		    therefore IDs are not reassigned *)
		 Clause.assign_prop_solver_id clause i
		   
		)
	   );
	   
	   (* Raise exception only after empty clause is in unsat
	      core solver *)
	   raise Unsatisfiable
	     
	  );
	
	(* Map literals in simplified clause in satisfiability solver
	   to literals in unsat core solver
	   
	   Use short association list of grounded literals to
	   grounded literals in unsat core solver to remove the
	   literals eliminated by propositional subsumption from the
	   clause to be added to the unsat core solver *)
	let simpl_gr_lit_uc_list =
	  List.map
	    (function e -> List.assoc e prop_gr_lit_to_uc)
	    simpl_gr_lit_list
	in
	
	(* Add simplified clause to unsat core solver and get id
	   
	   Must do this first, since adding a clause to
	   satisfiability solver can be immediately unsatisfiable,
	   but not in unsat core solver *)
	let clause_id =
	  PropSolver.add_clause_with_id solver_uc None simpl_gr_lit_uc_list
	in
	
	(
	 
	 match clause_id with
	   
	   (* Clause was discarded in solver *)
	 | None ->
	     
	     (
	      dbg D_add_clause (lazy ("Clause was discarded by solver2 "^(Clause.to_string clause)));
	      (* Format.eprintf
		 "Clause %a discarded in solver@\n@,"
		 Clause.pp_clause
		 clause *)
	      
	     )
	       
	       (* Clause has an ID in solver *)
	 | Some i ->
	     
	     (
	      
	      (* Assign ID to clause
		 
		 Clauses are only added to the solver once,
		 therefore IDs are not reassigned *)
	      Clause.assign_prop_solver_id clause i;
	      
	      (* Map ID in solver to first-order clause *)
	      Hashtbl.add solver_uc_clauses i clause;
	      dbg D_add_clause (lazy ("Clause: "^(Clause.to_string clause)^" solver id 2: "^(string_of_int i)));
	     )
	);
	 
	(* Dump propositional clause *)
	if !current_options.dbg_dump_prop_clauses then
	  Format.fprintf
	    (get_prop_clauses_dump_formatter ())
	    "c Added with ID %d@\n%a@."
	    (match clause_id with None -> -1 | Some i -> i)
	    (PropSolver.pp_lit_list_dimacs solver) simpl_gr_lit_list;
	
	(* Add simplified clause to satisfiability solver
	   
	   Clause must already be in unsat core solver, since this may
	   raise the PropSolver.Unsatisfiable exception *)
	(try
	  PropSolver.add_clause solver simpl_gr_lit_list
	with
	| (
	  Term.Term_grounding_undef(term)) ->
	    (out_warning ("Term_grounding_undef: "^(Term.to_string term)^"\n"));
	);
	(* Add simplified clause to simplification solver *)
	PropSolver.add_clause solver_sim simpl_gr_lit_list;
	
	(* Add simplified clause to propositional trie *)
	add_to_prop_trie simpl_gr_lit_list;
	
	(* Increment counter for number of propositional clauses *)
	incr_int_stat 1 prop_num_of_clauses
	  
      with
	
	(* Clause is a tautology or was propositionally simplified *)
      | PropTaut
      | PropSubsumed ->
	  
	  (* Increment counter for simplified clauses *)
	 (  
	    dbg D_add_clause (lazy ("Clause PropTaut | PropSubsumed 1"^(Clause.to_string clause)));
	   incr_int_stat 1 prop_preprocess_simplified;
	  )
	    
     );
     
     (
      
      try
	
	(* Propositionally simplify list of literals grounded by
	   variable *)
	let simpl_lit_list = simplify_prop_lit_list prop_lit_list in
	
	(* Catch simplification to empty clause *)
	if simpl_lit_list = [] then
	  
	  (
	   
	   (* Add empty clause to unsat core solver and get id *)
	   let clause_id =
	     PropSolver.add_clause_with_id
	       solver_uc
	       (Clause.get_prop_solver_id clause)
	       []
	   in
	   
	   (
	    
	    match clause_id with
	      
	      (* Clause was discarded in solver *)
	    | None -> (
	      dbg D_add_clause (lazy ("Clause was discarded by solver3 "^(Clause.to_string clause)));
)
		  
		  (* Clause has an ID in solver *)
	    | Some i ->
		
		(
		 
		 (* Map ID in solver to first-order clause *)
		 Hashtbl.add solver_uc_clauses i clause;
		 dbg D_add_clause (lazy ("Clause: "^(Clause.to_string clause)^" solver id 3: "^(string_of_int i)));		   
		)
	   );
	   
	   (* Raise exception only after empty clause is in unsat
	      core solver *)
	   raise Unsatisfiable
	     
	  );
	
	(* Map literals in simplified clause in simplification
	   solver to literals in unsat core solver
	   
	   Use short association list of literals grounded by variable to
	   literals grounded by variable in unsat core solver to remove
	   the literals eliminated by propositional subsumption from the
	   clause to be added to the unsat core solver *)
	let simpl_lit_uc_list =
	  List.map
	    (function e -> List.assoc e prop_lit_to_uc)
	    simpl_lit_list
	in
	
	(* Add simplified clause to unsat core solver and get id
	   
	   Must do this first, since adding a clause to satisfiability
	   solver can be immediately unsatisfiable, but not in unsat
	   core solver *)
	let clause_id =
	  PropSolver.add_clause_with_id
	    solver_uc
	    (Clause.get_prop_solver_id clause)
	    simpl_lit_uc_list
	in
	
	(
	 
	 match clause_id with
	   
	   (* Clause was discarded in solver *)
	 | None -> (
	      dbg D_add_clause (lazy ("Clause was discarded by solver4 "^(Clause.to_string clause)));
)
	       
	       (* Clause has an ID in solver *)
	 | Some i ->
	     
	     (
	      
	      dbg D_add_clause (lazy ("Clause: "^(Clause.to_string clause)^" solver id 4: "^(string_of_int i)));		   
	      (* Map ID in solver to first-order clause *)
	      Hashtbl.add solver_uc_clauses i clause;
	      
	      (* Assign ID to clause
		 
		 Clauses are only added to the solver once,
		 therefore IDs are not reassigned *)
	      (match Clause.get_prop_solver_id clause with
	      | None ->
		  Clause.assign_prop_solver_id clause i
	      | Some _ -> ())
		
	     )
	);
	
	(* Add simplified clause to simplification solver *)
	PropSolver.add_clause solver_sim simpl_lit_list;
	
	(* Add simplified clause to propositional trie *)
	add_to_prop_trie simpl_lit_list;
	
	(* Increment counter for number of propositional clauses *)
	incr_int_stat 1 prop_num_of_clauses
	  
      with
	
	(* Clause is a tautology or was propositionally simplified *)
      | PropTaut
      | PropSubsumed ->
	  (
	  (* Increment counter for simplified clauses *)
	   dbg D_add_clause (lazy ("Clause PropTaut | PropSubsumed 2"^(Clause.to_string clause)));
	  incr_int_stat 1 prop_preprocess_simplified
	  ) 
     );
     
     (*----- add answer assumtions *)
     (
      
      let add_answer_lit lit =
	(* answer lits are assumed to occur only positively*)
	if ((Term.get_top_symb lit) == Symbol.symb_answer)
	then
	  add_answer_assumption lit
	else ()
      in
      if !answer_mode_ref
      then
	List.iter add_answer_lit lits
      else ()
     );

     (*------set important prop lits-----------*)
     if !current_options.add_important_lit then
       (
	let set_imp_lit lit =
          if (is_important_for_prop_lit lit)
        then set_important_for_prop_lit lit
	in
	List.iter set_imp_lit lits
       )
    )

*)



(*------------------ add clause to solver -----------------------*)

(* TODO: add_sim_solver_test replace by more explicit *)

let add_sim_solver_test opts = true
(*
  opts.prep_gs_sim 
|| 
  (opts.instantiation_flag && ( opts.inst_prop_sim_given || opts.inst_prop_sim_new))
|| 
  (opts.resolution_flag && (opts.res_prop_simpl_new || opts.res_prop_simpl_given )) 
*)

(*-------assumtion: only one clause with the same id in the uc solver due to proof reconstruction -----*)

(*--------*)
let add_clause_to_solver input_clause =
  
  (* Skip if clause already in solver *)
  (*
  if (Clause.in_prop_solver clause) 
  then
    (dbg D_add_clause (lazy ("Clause "^(Clause.to_string clause)^" is already in solver, skipping")))
  else
  *)
  
  dbg D_add_clause (lazy (""));
  dbg D_add_clause (lazy ("Adding input_clause to solver: "^(Clause.to_tptp input_clause)));
  dbg D_add_clause (lazy (""));

(*   let lits = Clause.get_literals clause in *)
   
(* we assume that prop_lits and prop_uc_lits are direct maps from fo_lits *)

(* inst_clause is the clause with fo_lits *)
(*-----------------*)
(*  can raise  PropTaut, PropSubsumed *)
(*-----------------*)

  let add_to_sim_solver_flag = (add_sim_solver_test !current_options) in

(*------ we add to uc solver in all cases (when either add to sim_solver or to solver ) ----- *)

  let add_lits_to_solver clause ~add_to_sim_solver_flag ~add_to_solver_flag (* prop_lits prop_uc_lits*) = 
    
    let lits = Clause.get_literals clause in 
	(* Add simplified clause to unsat core solver and get id
	   
	   Must do this first, since adding a clause to
	   satisfiability solver can be immediately unsatisfiable,
	   but not in unsat core solver *)

    dbg D_add_clause (lazy ("Adding clause to solver: "^(Clause.to_tptp clause)));

    add_to_gr_trie lits;    
    
     (* Map clause literals to propositional literals grounded by
	variables *)
    let prop_lits = List.map get_prop_lit_assign lits in
     
     dbg D_add_clause (lazy ("prop_lits: "^(PropSolver.lit_list_to_string solver prop_lits)));
    
     (* Map clause literals to propositional literals grounded by
	variable in unsat core solver *)
     let prop_uc_lits =
       List.map get_prop_lit_uc_assign lits
     in
     
     dbg D_add_clause (lazy ("prop_uc_lits: "^(PropSolver.lit_uc_list_to_string solver_uc prop_uc_lits)));

     (* Mark propositional variables as in solver *)
(*
     let f lit =
       let var_entry = get_prop_var_entry lit in
       var_entry.in_solver_sim <- true in
     List.iter f lits;
*)    
     let clause_id =
       try 
         puf_get_id clause 
       with 
         Not_found ->
           begin
           let clause_new_id =
	     PropSolver.add_clause_with_id solver_uc None prop_uc_lits
	   in         
	   match clause_new_id with
	   
	    (* Clause was discarded in solver *)
	    | None ->	     
		( (* should not happen; exception Unsatisfiable_na should be raised  *)
                  dbg D_add_clause (lazy ("Clause was discarded by UC solver "^(Clause.to_tptp clause)));
                  raise Unsatisfiable_gr_na;		 
                 )
            | Some id ->	    
                (
	         dbg D_add_clause (lazy ("puf: add clause: "^(Clause.to_tptp clause)
					 ^" uc solver id: "^(string_of_int id)));      
                 puf_add_clause id clause;
                 id
		)
	   end
     in

     (if  prop_lits = []  
     then 
       (        
       raise Unsatisfiable_gr_na
       )
     );

	(* Dump propositional clause *)
     if !current_options.dbg_dump_prop_clauses then
       Format.fprintf
	 (get_prop_clauses_dump_formatter ())
	 "c Added with ID %d@\n%a@."
	 clause_id  
	 (PropSolver.pp_lit_list_dimacs solver) prop_lits;
     
	
	(* Add prop clause to satisfiability solver
	   
	   Clause must already be in unsat core solver, since this may
	   raise the PropSolver.Unsatisfiable exception *)

     (if add_to_solver_flag 
     then
       PropSolver.add_clause solver prop_lits
     );


	(* Add simplified clause to simplification solver *)
     (if add_to_sim_solver_flag
     then
	PropSolver.add_clause solver_sim prop_lits
     );	
	
(*----- add answer assumtions *)
     (
      
      let add_answer_lit lit =
	(* answer lits are assumed to occur only positively*)
	if ((Term.get_top_symb lit) == Symbol.symb_answer)
	then
	  add_answer_assumption lit
	else ()
      in
      if !answer_mode_ref
      then
	List.iter add_answer_lit lits
      else ()
     );
     
     (*------set important prop lits-----------*)
     (
      if !current_options.add_important_lit then
	(
	let set_imp_lit lit =
          if (is_important_for_prop_lit lit)
          then set_important_for_prop_lit lit
	in
	List.iter set_imp_lit lits
	)
     );
	
     (*----- set_is_decision_var -------*)
     (match !decision_var_test_param with 
     |Def(decision_var_test) -> 
	 let f lit = 
	   set_decision_var (decision_var_test lit) lit
	 in
	 List.iter f lits

     |Undef -> ()
     );	

    (* Increment counter for number of propositional clauses *)
     incr_int_stat 1 prop_num_of_clauses
   in (* end of add_lits_to_solver *)
(*----------------*)

   let init_lits = Clause.get_literals input_clause in

   let _prop_lits = List.map get_prop_lit_assign init_lits in

   if (Clause.is_ground input_clause) 
   then 
     (* Propositionally simplify list of literals in particular we do not add the same clause twice *)
     (* currently lits will not be simplified just checked wether they are subsumed/tautology *)
     try
       let _lits =
	 simplify_gr_lit_list init_lits
       in
       add_lits_to_solver input_clause ~add_to_sim_solver_flag ~add_to_solver_flag:true (* prop_lits prop_uc_lits*) 
     with 
     | GrTaut | GrSubsumed ->
	     (  
		dbg D_add_clause (lazy ("Clause GrTaut | GrSubsumed 1: "^(Clause.to_tptp input_clause)));
		incr_int_stat 1 prop_preprocess_simplified;
	       )  
   else
     begin
(* Moved below
	   (
	    try
	   
	   (* we need to reculculate grounding *)
	      let _prop_lits = List.map get_prop_gr_lit_assign init_lits in
	      
	      (* apply grounding *)
	      let gr_init_lits = List.map get_grounded_lit init_lits in 
	      let gr_lits =
		simplify_gr_lit_list gr_init_lits
	      in
	      let gr_tstp_source = Clause.tstp_source_instantiation input_clause [] in
	      let gr_clause = create_clause gr_tstp_source gr_lits in 
	      add_lits_to_solver gr_clause ~add_to_sim_solver_flag ~add_to_solver_flag:true (* prop_lits prop_uc_lits*)	
	    with 
	    | GrTaut | GrSubsumed ->
		(  
		   dbg D_add_clause (lazy ("Clause GrTaut | GrSubsumed 2: "^(Clause.to_tptp input_clause)));
		   incr_int_stat 1 prop_preprocess_simplified;
		  )
	   );

*)

	   (
	    try (* we need to check the flag here since otherwise the clause will be added to uc solver *)
	      if (add_to_sim_solver_flag)
	      then 
		(
		  let _lits =
		    simplify_gr_lit_list init_lits
		  in
		  add_lits_to_solver 
		    input_clause ~add_to_sim_solver_flag ~add_to_solver_flag:true (* false *) (* prop_lits prop_uc_lits*)    
		)
	      else
		()
		  
	    with 
	    | GrTaut | GrSubsumed ->
		(  
		   dbg D_add_clause (lazy ("Clause PropTaut | GrSubsumed 3: "^(Clause.to_tptp input_clause)));
		   incr_int_stat 1 prop_preprocess_simplified;
		  )  
	   );
	   (
	    try
	   
	   (* we need to reculculate grounding *)
	      let _prop_lits = List.map get_prop_gr_lit_assign init_lits in
	      
	      (* apply grounding *)
	      let gr_init_lits = List.map get_grounded_lit init_lits in 
	      let gr_lits = simplify_gr_lit_list gr_init_lits in
	      let gr_tstp_source = Clause.tstp_source_instantiation input_clause [] in
	      let gr_clause = create_clause gr_tstp_source gr_lits in 
	      add_lits_to_solver gr_clause ~add_to_sim_solver_flag ~add_to_solver_flag:true (* prop_lits prop_uc_lits*)	
	    with 
	    | GrTaut | GrSubsumed ->
		(  
		   dbg D_add_clause (lazy ("Clause GrTaut | GrSubsumed 2: "^(Clause.to_tptp input_clause)));
		   incr_int_stat 1 prop_preprocess_simplified;
		  )
	   );
	 end


  
	 
(*--------------------------------*)      
(*
let preserve_model_solver_gr lit =
  let 
*)


(*----------------- change selection -----------------------------*)

(*
let pp_truth_val ppf = function
  | Undef -> Format.fprintf ppf "Undef"
  | Def PropSolver.True -> Format.fprintf ppf "True"
  | Def PropSolver.False -> Format.fprintf ppf "False"
  | Def PropSolver.Any -> Format.fprintf ppf "Any"

(* Warning both A and neg A can be consitent with the solver *)
(* (if the solver returns Any) *)
(* after grounding*)
let consistent_with_solver lit =
  (* Format.eprintf
     "consistent_with_solver %a@."
     Term.pp_term lit; *)
  let var_entry = get_prop_gr_var_entry lit in
  let prop_var = get_prop_var_var_entry var_entry in
  let var_truth_val = PropSolver.lit_val solver prop_var in

  dbg D_selection_renew_lit
    (lazy 
       (("lit: ")^(Term.to_string lit)^" solver val: "^(PropSolver.lit_val_to_string var_truth_val))
    );
  
  if var_truth_val = PropSolver.Any
  then
    ( (* Format.eprintf
	 "Literal %s is consistent with solver, since model value is Any@."
	 (Term.to_string lit); *)      
      true)
  else
    let is_neg = Term.is_neg_lit lit in
    if
      ((var_truth_val = PropSolver.True) && (not is_neg)) ||
      ((var_truth_val = PropSolver.False) && is_neg)
    then
      ( (* Format.eprintf
	   "Literal %s is consistent with solver, since model value is True@."
	   (Term.to_string lit); *)
	true)
    else
      ( 
  
(* Format.eprintf
	   "Literal %s is not consistent with solver, since model value is False@."
	   (Term.to_string lit); *)
	false)

(* without grounding*)
let consistent_with_solver_lit lit =
  let var_entry = get_prop_var_entry lit in
  let prop_var = get_prop_var_var_entry var_entry in
  let var_truth_val = PropSolver.lit_val solver prop_var in
  if var_truth_val = PropSolver.Any
  then true
  else
   ( 
     let is_neg = Term.is_neg_lit lit in        
     ((var_truth_val = PropSolver.True) && (not is_neg)) ||
     ((var_truth_val = PropSolver.False) && is_neg)
) 

(* after grounding *)
let consistent_with_model lit =
  let var_entry = get_prop_gr_var_entry lit in
  (*    let var_truth_val  = get_truth_var_entry var_entry in*)
  match var_entry.truth_val with
  | Def(var_truth_val) ->
      if (var_truth_val = PropSolver.Any)
      then
	((*out_str "consistent_with_model: Any\n "; *)
	 (* Format.eprintf
	    "Literal %s is consistent with model, since model value is Any@."
	    (Term.to_string lit); *)
	 true )
      else
	let is_neg = Term.is_neg_lit lit in
	if
	  ((var_truth_val = PropSolver.True) && (not is_neg)) ||
	  ((var_truth_val = PropSolver.False) && is_neg)
	then
	  (
              (* Format.eprintf
	      "Literal %s is consistent with model, since model value is True@."
	      (Term.to_string lit); *)
	   true)
	else
	  (
            (* Format.eprintf
	      "Literal %s is not consistent with model, since model value is False@."
	      (Term.to_string lit); *)
	   false)
  | Undef ->
    ((* Format.eprintf
	"Literal %s is consistent with model, since model value is Undef@."
	(Term.to_string lit); *)
     true)

let get_lit_activity lit =
  let var_entry = get_prop_var_entry lit in
  if (Term.is_neg_lit lit) then
    var_entry.neg_activity
  else
    var_entry.pos_activity
      
let activity_condition lit =
  let activity = get_lit_activity lit in
  ((activity < ((get_val_stat inst_max_lit_activity) lsr 2 ))
 ||
   (activity < !lit_activity_threshold)
)

let consistent_with_model_activity lit =
  (* remove true later*)
  if (activity_condition lit)
  then consistent_with_model lit
  else false

let consistent_with_solver_activity lit =
  (* remove true later*)
  if (activity_condition lit)
  then consistent_with_solver lit
  else false

(* without grounding*)
let consistent_with_model_lit lit =
  let var_entry = get_prop_var_entry lit in
  let var_truth_val = get_truth_var_entry var_entry in
  if (var_truth_val = PropSolver.Any)
  then true
  else
    let is_neg = Term.is_neg_lit lit in
    if
      ((var_truth_val = PropSolver.True) && (not is_neg)) ||
      ((var_truth_val = PropSolver.False) && is_neg)
    then true
    else false

(* move_lit_from_active_to_passive is a function which is a parameter here *)
(* and is defined in instantiation.ml *)

(* returns true if it can preserve model (solver is run under entry assumption) *)
(* otherwise return false *)

let preserve_model_solver move_lit_from_active_to_passive var_entry =
  let prop_var = get_prop_var_var_entry var_entry in
  let prop_neg_var = get_prop_neg_var_var_entry var_entry in
  let new_truth_val = PropSolver.lit_val solver prop_var in
  (* out_str ("Var entry:"^(var_entry_to_string solver var_entry)^"\n");
     out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with
  | Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any)
      then
	(* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(var_entry.truth_val <- Def(new_truth_val);
	 (*debug check *)
	 (* (if var_entry.sel_clauses !=[]
	    then out_str "preserve_model_solver: sel_clauses should be empty \n");
	  *)
	 true)
      else
	if (old_truth_val = new_truth_val) || (new_truth_val = PropSolver.Any)
	then true
	else
	  (
	   let assumption =
	     if old_truth_val = PropSolver.True
	     then prop_var
	     else prop_neg_var
	   in
	   (
	    dbg D_solve (lazy (" preserve_model_solver"));  
           (*num_of_solver_calls := !num_of_solver_calls +1;*)
	    match(solve_assumptions solver [assumption])
	    with
	    | PropSolver.Sat -> true
	    | PropSolver.Unsat (*| PropSolver.FUnknown*) ->
		( (*out_str "Prop unsat \n"; *)
		  let new_truth_val = PropSolver.lit_val solver prop_var in
		  var_entry.truth_val <- Def(new_truth_val);
		  let move_cl_from_active_to_passive clause =
		    if (Clause.get_ps_in_active clause)
		    then
		      (let sel_lit = Clause.inst_get_sel_lit clause in
		      (* moves all clauses indexed by sel_lit *)
		      move_lit_from_active_to_passive sel_lit)
		    else ()
		  in
		  List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
		  var_entry.sel_clauses <- [];
		  
		  (* out_str ("Preserve Model: Unsat: "
		     ^"Assum: "^(PropSolver.lit_to_string assumption)^"  "
		     ^(var_entry_to_string solver var_entry)^"\n");*)
		  
		  (* (match (solve ())
		     with PropSolver.Unsat -> raise Unsatisfiable
		     | PropSolver.Sat -> ());*)
		  
		  false)
	   ))
	    
  | Undef ->
      (var_entry.truth_val <- Def(new_truth_val);
       true)
(*with Not_found -> failwith "Nor_found here"*)

(* if model value is  defferent from solver then chage the model value *)
let change_model_solver move_lit_from_active_to_passive var_entry =
  let prop_var = get_prop_var_var_entry var_entry in
  (*  let prop_neg_var  = get_prop_neg_var_var_entry var_entry in*)
  let new_truth_val = PropSolver.lit_val solver prop_var in
  (* out_str ("Var enty:"^(var_entry_to_string solver var_entry)^"\n");
     out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with
  | Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any)
      then
	(* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(
	 (*debug*)
	 (* (if var_entry.sel_clauses !=[]
	    then out_str "change_model_solver: sel_clauses should be empty \n");*)
	 var_entry.truth_val <- Def(new_truth_val))
      else
	if (old_truth_val = new_truth_val) (* || (new_truth_val = PropSolver.Any) *)
	then ()
	else
	  (
	   (* out_str ("Change_model_solver: "^
	      (var_entry_to_string var_entry)^"\n");*)
	   var_entry.truth_val <- Def(new_truth_val);
	   let move_cl_from_active_to_passive clause =
	     if (Clause.get_ps_in_active clause)
	     then
	       (let sel_lit = Clause.inst_get_sel_lit clause in
	       (*  out_str ("Change_model in Active: "^(Clause.to_string clause)^"\n");*)
	       (* moves all clauses indexed by sel_lit *)
	       move_lit_from_active_to_passive sel_lit
	       )
	     else ()
	   in
	   List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
	   var_entry.sel_clauses <- []
	  )
	    
  | Undef ->
      var_entry.truth_val <- Def(new_truth_val)

(* auxilary function for below, apply only if lit is consitent with the model!*)

let ass_if_consistent lit clause =
  let var_entry = get_prop_gr_var_entry lit in
  if (get_truth_var_entry var_entry = PropSolver.Any)
  then
    (
     (*debug check *)
     
       (if var_entry.sel_clauses !=[]
       then Format.eprintf "ass_if_consistent: sel_clauses should be empty@.");
      
     var_entry.sel_clauses <- [clause];
     if (Term.is_neg_lit lit)
     then var_entry.truth_val <- Def(PropSolver.False)
     else var_entry.truth_val <- Def(PropSolver.True))
  else
    var_entry.sel_clauses <- clause:: (var_entry.sel_clauses)
(* we assume that the clause is from passive and therefore *)
(* not assigned in to any of var_entry.sel_clauses         *)
(* we try to keep the old selection                        *)
(*
  let find_nex_true_lit
 *)

let remove_undef_model clause =
  (* Format.eprintf
     "remove_undef_model %a@."
     Clause.pp_clause clause; *)
  let remove_undef_lit lit =
    (* Format.eprintf
       "remove_undef_lit %a@."
       Term.pp_term lit; *)
    let var_entry = get_prop_gr_var_entry lit in
    match var_entry.truth_val with
    | Def(PropSolver.Any) | Undef ->
	(* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(let prop_var = get_prop_var_var_entry var_entry in
	let new_truth_val = PropSolver.lit_val solver prop_var in
	(* Format.eprintf
	   "Changing model for atom %s from %a to %a@."
	   (Term.to_string (Term.get_atom lit))
	   pp_truth_val var_entry.truth_val
	   pp_truth_val (Def new_truth_val); *)
	var_entry.truth_val <- Def(new_truth_val))
    | _ -> ()
	  (* Format.eprintf
	     "Keeping model for atom %s as %a@."
	     (Term.to_string (Term.get_atom lit))
	     pp_truth_val var_entry.truth_val *)
  in
  Clause.iter remove_undef_lit clause

exception Sel_Changed
exception Solver_Sel
let rec selection_renew_model move_lit_from_active_to_passive selection_fun clause =

  dbg D_selection_renew  (lazy ("clause:"^(Clause.to_string clause)));   
  (* Format.eprintf
     "selection_renew_model for clause %s@."
     (Clause.to_string clause); *)
  
  (*  out_str (" selection_renew clause:  "^(Clause.to_string clause)^"\n");*)
  (*
    let accord lit =
    let var_entry = get_prop_gr_var_entry lit in
    let _ = model_accords_solver solver var_entry in () in
    Clause.iter accord clause; *)
  (* do not try, it will cycle!
     let preserve_mod lit =
     let var_entry = get_prop_gr_var_entry lit in
     let _ = preserve_model_solver move_lit_from_active_to_passive solver var_entry in () in
     Clause.iter preserve_mod clause; *)
  try
    let sel_lit = Clause.inst_get_sel_lit clause in
    let sel_var_entry = get_prop_gr_var_entry sel_lit in
    if
      (consistent_with_model sel_lit)
    then
      if
	(preserve_model_solver move_lit_from_active_to_passive sel_var_entry)
      then
	((* Format.eprintf "Selection is consistent and can be preserved@."; *)
	 ass_if_consistent sel_lit clause)
      else
	((* Format.eprintf "Selection is consistent but cannot be preserved@."; *)
	 raise Sel_Changed)
    else
      ((* Format.eprintf "Selection is not consistent@."; *)
       raise Sel_Changed)
  with
    Sel_Changed | Clause.Inst_sel_lit_undef ->
      (
       try
	 (
	  remove_undef_model clause;
	  
	  dbg_env D_selection_renew  
	    (fun () ->
	      (out_str ("\n----------------------------\n");
	       out_str ("Try consist with Model:");
	       let out_entry lit =
		 let var_entry = get_prop_gr_var_entry lit in
		 out_str ("\n Lit: "^(Term.to_string lit)^"\n"
			  ^(var_entry_to_string var_entry)^"\n"
			  ^"Consist_with_Model: "
			  ^(string_of_bool (consistent_with_model lit))^"\n");
	       in Clause.iter out_entry clause; 
	      ));
	  let model_sel_lit =
	    selection_fun consistent_with_model_activity clause in
	  (* let model_sel_lit =
	     selection_fun consistent_with_model clause in *)
	  (*             out_str ("Consist_model: "^(Term.to_string model_sel_lit)^"\n");*)
	  let model_sel_var_entry = get_prop_gr_var_entry model_sel_lit in
	  if (preserve_model_solver move_lit_from_active_to_passive model_sel_var_entry) then
	    ((*change_model_solver model_sel_var_entry;*)
	     Clause.inst_assign_sel_lit model_sel_lit clause;
	     ass_if_consistent model_sel_lit clause;
	     (* out_str ("preserve model:  "^
		(var_entry_to_string model_sel_var_entry)^"\n");
		out_str ("----------------------------\n") *)
	    )
	  else
	    (* optional change_model*)
	    (
	     change_model_solver move_lit_from_active_to_passive model_sel_var_entry;
	     raise Solver_Sel)
	 )
       with Not_found | Solver_Sel ->
	 try (
	   (*debug*)
	   (* out_str ("----------------------------\n");
	      out_str ("No consist with Model:");
	      let out_entry lit =
	      let var_entry = get_prop_gr_var_entry lit in
	      out_str ("\n Lit: "^(Term.to_string lit)^"\n"
	      ^(var_entry_to_string var_entry)^"\n"
	      ^"Consist_with_Model: "
	      ^(string_of_bool (consistent_with_model lit))^"\n");
	      in Clause.iter out_entry clause;*)
	   
(* new *)
	   add_clause_to_solver clause;

	   let solver_sel_lit =
	     selection_fun consistent_with_solver_activity clause in
	   let solver_sel_var_entry = get_prop_gr_var_entry solver_sel_lit in
	   (*  out_str ("Before change\n");*)
	   change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;
	   (*     out_str "Change here \n";*)
	   (* out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
	      ^"Sel_lit entry: "
	      ^(var_entry_to_string solver_sel_var_entry));*)
	   Clause.inst_assign_sel_lit solver_sel_lit clause;
	   ass_if_consistent solver_sel_lit clause
	     (*	     out_str ("----------------------------\n");*)
	  )
	 with Not_found ->
	   ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	    dbg D_solve (lazy (" selection_renew_model"));
	    match (solve ()) with
	    | PropSolver.Unsat ->
		( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_model@."; *)
		  raise Unsatisfiable_gr (* solve () can have default assumtions *)
		 )
	    | PropSolver.Sat ->
		
		let new_solver_sel_lit =
		  try
		    selection_fun consistent_with_solver clause
		  with
		    Not_found ->

		      (
		       out_warning ("\n Selection is not found for clause: "
				    ^(Clause.to_string clause)^"\n"
				    (*^" is in prop_solver "
				     ^(string_of_bool (Clause.in_prop_solver clause))*));

		       dbg_env D_selection_renew 
			 ( fun () -> 
			   dbg_groups_ref:=(D_selection_renew_lit ::(!dbg_groups_ref));
			   let f lit = 
			     dbg D_selection_renew  
			       (lazy 
				  (" lit "^(Term.to_string lit)
				   ^" consistent with solver: "^(string_of_bool (consistent_with_solver lit))
						  )
			       );
			   in Clause.iter f clause 
			  );

		      raise (Failure "selection_renew_model") )
			
		in
		let new_solver_sel_var_entry =
		  get_prop_gr_var_entry new_solver_sel_lit in
		(*		 out_str "\n Change here!!!!\n";*)
		change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
		(*
		  out_str ("Solver select:"^
		  "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
		  ^"Sel_lit entry: "
		  ^(var_entry_to_string new_solver_sel_var_entry)^"\n");
		 *)
		Clause.inst_assign_sel_lit new_solver_sel_lit clause;
		ass_if_consistent new_solver_sel_lit clause
		  
	   )
      )

(*
  exception Sel_Unchanged
  let apply_new_model solver =
  let sel_is_changed = ref false in
  let change_entry var_entry =
  let prop_var = get_prop_var_var_entry var_entry in
  match var_entry.truth_val with
  | Def(_) ->
  if (change_model_solver move_lit_from_active_to_passive var_entry)
  then ()
  else sel_is_changed:= true
  | Undef ->
  (    (* sel_is_changed:=true; *)
  let new_truth_val = PropSolver.lit_val solver prop_var in
  var_entry.truth_val <- Def(new_truth_val)
  )
  in
  TableArray.iter change_entry var_table;
  if !sel_is_changed then ()
  else
  raise Sel_Unchanged
 *)

(*----------------- end change selection -----------------------------*)

(*let solver_calls_renew = ref 0*)

let rec selection_renew_solver move_lit_from_active_to_passive selection_fun clause =
  
  (* Format.eprintf
     "selection_renew_solver for clause %s@."
     (Clause.to_string clause); *)
  
  try
    (
     let solver_sel_lit =
       (*	       selection_fun consistent_with_solver_activity clause in	 *)
       selection_fun consistent_with_solver clause in
     let solver_sel_var_entry = get_prop_gr_var_entry solver_sel_lit in
     (*  out_str ("Before change\n");*)

     change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;

     (*     out_str "Change here \n";*)
     (* out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
	^"Sel_lit entry: "
	^(var_entry_to_string solver_sel_var_entry));*)
     Clause.inst_assign_sel_lit solver_sel_lit clause;
     ass_if_consistent solver_sel_lit clause
       (*	     out_str ("----------------------------\n");*)
    )
  with Not_found ->
    ((*num_of_solver_calls := !num_of_solver_calls +1;*)
     (* solver_calls_renew:= !solver_calls_renew +1;
	out_str ("solver_calls renew "^(string_of_int !solver_calls_renew));*)

     dbg D_solve (lazy (" selection_renew_solver: "^(Clause.to_string clause)));
     
(* TODO revise *)
(*     Clause.iter (set_decision_var true) clause; *)
     match (solve ()) with
     | PropSolver.Unsat ->
	 ( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_solver@."; *)
           dbg D_solve (lazy ("Unsatisfiable_gr in selection_renew_solver"));
	   raise Unsatisfiable_gr (* solve () can have default assumptions *)
	  ) 
     | PropSolver.Sat ->
	 let new_solver_sel_lit =
	   try
	     selection_fun consistent_with_solver clause
	   with Not_found ->
	     (
	      raise (Failure (Format.sprintf "No selection possible for %s@." (Clause.to_string clause))))
	 in
	 let new_solver_sel_var_entry =
	   get_prop_gr_var_entry new_solver_sel_lit in
	 (*		 out_str "\n Change here!!!!\n";*)
	 change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
	 (* out_str ("Solver select:"^
	    "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
	    ^"Sel_lit entry: "
	    ^(var_entry_to_string new_solver_sel_var_entry)^"\n");*)
	 Clause.inst_assign_sel_lit new_solver_sel_lit clause;
	 ass_if_consistent new_solver_sel_lit clause
    )

(* let _ = out_str "\n\n !!!selection_renew_main later switch to  selection_renew_tmp!!!\n\n "
 *)

let selection_renew x =
  match !current_options.inst_sel_renew with
  | Inst_SR_Solver ->
      selection_renew_solver x
  | Inst_SR_Model ->
      selection_renew_model x
*)
(*------------Instantiation Lit Activity -----------------------------*)
(*
exception Activity_Check
exception Activity_Undef
let lit_activity_check move_lit_from_active_to_passive lit =
  if (not !current_options.inst_lit_activity_flag)
  then ()
  else
    begin
      try
	let var_entry = get_prop_gr_var_entry lit in
	let model_truth_val =
	  match var_entry.truth_val with
	  | Def(PropSolver.True) -> true
	  | Def(PropSolver.False) -> false
	  | _ -> raise Activity_Undef
	in
	if ((model_truth_val = false)
	      (* && (var_entry.neg_activity >
		 (var_entry.pos_activity + !lit_activity_threshold + (!max_lit_activity lsr 2))) *)
	      && (var_entry.neg_activity > var_entry.pos_activity + var_entry.change_activity_limit)
	   )
	then
	  (
	   
	   dbg D_solve (lazy ("lit_activity_check"));  
	   (* set_important_for_prop_lit lit; *)
	   match (solve_assumptions solver [(get_prop_var_var_entry var_entry)])
	   with
	   | PropSolver.Unsat ->
	       (var_entry.change_activity_limit <- 1000000; (*any big number*)
		(* match (PropSolver.solve solver)
		   with PropSolver.Unsat -> raise Unsatisfiable
		   | PropSolver.Sat -> () *) )
	   | PropSolver.Sat -> (
	       incr_int_stat 1 inst_lit_activity_moves;
	       var_entry.pos_activity <- 0;
	       var_entry.neg_activity <- 0;
	       var_entry.change_activity_limit <-
		 (2 * var_entry.change_activity_limit);
	       (* out_str ("Act Lit: "^(Term.to_string lit)^"\n"
		  ^"Before Change: "
		  ^(var_entry_to_string solver var_entry)^"\n");
		*)
	       change_model_solver move_lit_from_active_to_passive var_entry;
	       
	       (* out_str ("After Chnage: "
		  ^(var_entry_to_string solver var_entry)^"\n");
		*)
	       raise Activity_Check)
		 
	  )
	else
	  if ((model_truth_val = true)
		(* && (var_entry.pos_activity > (var_entry.neg_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
		&& (var_entry.pos_activity > (var_entry.neg_activity + var_entry.change_activity_limit))
	     )
	  then
	    (
	     (* set_important_for_prop_lit lit; *)
	     dbg D_solve (lazy ("lit_activity_check"));  
	     match (solve_assumptions solver [(get_prop_neg_var_var_entry var_entry)])
	     with
	     | PropSolver.Unsat ->
		 (var_entry.change_activity_limit <- 1000000; (*any big number*)
		  (* match (PropSolver.solve solver)
		     with PropSolver.Unsat -> raise Unsatisfiable
		     | PropSolver.Sat -> () *))
		   (* (out_str ("Act_Check Unsat with assumption: "
		      ^(PropSolver.lit_to_string
		      (get_prop_neg_var_var_entry var_entry))^"\n")) *)
	     | PropSolver.Sat -> (
		 incr_int_stat 1 inst_lit_activity_moves;
		 var_entry.neg_activity <- 0;
		 var_entry.pos_activity <- 0;
		 var_entry.change_activity_limit <-
		   (2 * var_entry.change_activity_limit);
		 (* out_str ("Act Lit: "^(Term.to_string lit)^"\n"
		    ^"Before Change: "
		    ^(var_entry_to_string solver var_entry)^"\n");
		  *)
		 change_model_solver move_lit_from_active_to_passive var_entry;
		 (*
		   out_str ("After Chnage: "
		   ^(var_entry_to_string solver var_entry)^"\n");
		  *)
		 raise Activity_Check)
		   
	    )
	  else ()
      with Activity_Undef -> ()
    end

let increase_lit_activity i lit =
  try
    let var_entry = get_prop_gr_var_entry lit in
    let model_truth_val =
      match var_entry.truth_val with
      | Def(PropSolver.True) -> true
      | Def(PropSolver.False) -> false
      | _ -> raise Activity_Undef
    in
    if (model_truth_val = false)
    then
      (var_entry.neg_activity <- var_entry.neg_activity + i;
       if var_entry.neg_activity > (get_val_stat inst_max_lit_activity)
       then (assign_int_stat var_entry.neg_activity inst_max_lit_activity
	       (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		  ^(var_entry_to_string var_entry)) *)
	    )
      )
    else
      (var_entry.pos_activity <- var_entry.pos_activity + i;
       if var_entry.pos_activity > (get_val_stat inst_max_lit_activity)
       then (assign_int_stat var_entry.pos_activity inst_max_lit_activity
	       (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		  ^(var_entry_to_string var_entry)) *)
	    )
      )
  with Activity_Undef -> ()

*)
(*
  let lit_activity_check = lit_activity_check_main

  let lit_activity_check _ _ = ()
  let _ = out_str "\n\n !!! lit_activity_check -> lit_activity_check_main !!!"
 *)

(*------------End Instantiation Lit Activity -----------------------------*)

(*----------- Global Subsumption--------------------------------*)

type add_lit =
    {
     slit : lit;
     slit_compl : lit;
     sprop_lit : PropSolver.lit;
     sprop_compl_lit : PropSolver.lit;
     mutable slabel : bool
   }

exception Subsum_all_tried
let rec first_non_tried rest list_add_lit =
  match list_add_lit with
  | h:: tl ->
      if (not h.slabel)
      then (h, (rest@tl))
      else (first_non_tried (h:: rest) tl)
  |[] -> raise Subsum_all_tried

let rec prop_subs_lits list_add_lit =
  try
    let (lit, to_test_add_lits) = first_non_tried [] list_add_lit in
    lit.slabel <- true;
(*
    let to_test_prop_lits =
      List.map (function add_lit -> add_lit.sprop_compl_lit) to_test_add_lits
    in
*)
    let to_test_compl_lits =
      List.map (function add_lit -> add_lit.slit_compl) to_test_add_lits
    in
    match (fast_solve ~solver_in:solver_sim to_test_compl_lits) with 
(* DEBUG *)   (* match (fast_solve ~solver_in:solver to_test_compl_lits) with *)
    | PropSolver.FUnsat ->
	(
	 incr_int_stat 1 prop_fo_subsumed;         
(*
	 dbg D_prop_subs (lazy ("solver_sim="^(string_of_bool 
                                                 (PropSolver.is_simplification solver_sim))));
*)

(*	 dbg D_prop_subs (lazy (" funsat: lits: "^(PropSolver.lit_list_to_string solver_sim to_test_prop_lits)
                                ^" solver ass: "^(PropSolver.lit_list_to_string solver_sim (get_solver_assumptions solver_sim))));
*)
	 prop_subs_lits to_test_add_lits
        )
    | PropSolver.FSat | PropSolver.FUnknown ->
	(*    |PropSolver.Sat ->*)
	prop_subs_lits list_add_lit
  with
    Subsum_all_tried -> list_add_lit

(*let () = out_str "\n\n !!!Uncomment  prop_subsumption \n\n !!!"*)

(* We need first to filter the adjoint predicate! *)
(* otherwise the same clause will be generated: c\/p  *)
(* by first cutting p and then adding it *)
(* this will result that the old clause will be declared dead *)
(* but new one will not be added since the old one is in the db *)

(*
let filter_adjoint_pred lit_list =
  let filter_pred list pred = List.filter (fun l -> not (l == pred)) list in
  List.fold_left filter_pred lit_list !adjoint_preds
*)

exception Prop_subs_not_eligible
let filter_adjoint_pred lits = 
  let adjoint_lits = glb_sae.sae_sim_adjoint_lits in
  if  (not (TSet.is_empty adjoint_lits))
  then     
    let lit_set = TSet.of_list lits in 
    let adjoint_lit_set = TSet.inter lit_set adjoint_lits in
    if (TSet.equal adjoint_lits adjoint_lit_set) 
    then 
      TSet.elements (TSet.diff lit_set adjoint_lit_set)
    else
      raise Prop_subs_not_eligible
  else
    lits

let prop_subsumption_single (* context_param *) clause =
  dbg D_prop_subs (lazy ("input:  "^(Clause.to_tptp clause)));
  let adjoint_lits = glb_sae.sae_sim_adjoint_lits in

  add_clause_to_solver clause;

  try  
    let lits = filter_adjoint_pred (Clause.get_literals clause) in
  
    let list_add_lit =
      let f lit =
        { slit = lit;
          slit_compl = add_compl_lit lit;
	  sprop_lit = (get_prop_lit lit);
	  sprop_compl_lit = (get_prop_compl_lit lit);
	  slabel = false }
      in
    List.map f lits in
    let new_add_lits = prop_subs_lits list_add_lit in
    if (List.length new_add_lits) < (List.length list_add_lit)
    then
(* empty clause during adding into prop_solver
    (*out_str "Eliminate Prop Subs\n";*)
    if ((new_add_lits = []) && (!adjoint_preds = []))
    then
      ( 
(* sim solvers can have assumptions  *)
        dbg D_prop_subs (lazy ("Clause simplified to empty clause in prop_subsumption: "^(Clause.to_string clause))); 
	raise Unsatisfiable_gr
       )
    else
*)
      (
       let prop_dep_lvl = (TableArray.num_of_elem var_table) + (PropSolver.clauses_with_id solver_uc)  (* +1 *) in (* KK 2018*)

       let tstp_source_raw =
	 Clause.tstp_source_global_subsumption
	   (prop_dep_lvl) clause
       in
       let new_lits = 
         (List.map (function add_lit -> add_lit.slit) new_add_lits)@(TSet.elements adjoint_lits) in
       let bc_imp_inh = Options.bc_imp_inh_default_val in

(* should use create_clause_raw here due to literal mapping in the proof extraction *)
       let new_clause_raw = Clause.create_clause_raw tstp_source_raw ~bc_imp_inh new_lits in 

       let tstp_source_rename = Clause.tstp_source_renaming new_clause_raw in
       let renamed_clause = create_clause ~bc_imp_inh tstp_source_rename new_lits in
       let new_clause = 
         if (Clause.equal_bc new_clause_raw renamed_clause) 
         then 
           new_clause_raw (* skip trivial renaming *)
         else  
           renamed_clause
       in
(*         create_clause tstp_source new_lits in *)

       (* out_str ("Old Clause: "^(Clause.to_string clause)^"\n");  *)
       (* Clause.inherit_param_modif clause new_clause; *)
       (*
       (match context_param with 
       |Def(context) -> 
           clause_register_subsumed_by context ~by:new_clause clause;
       |Undef -> ()
       );
        *)
       dbg D_prop_subs (lazy ("before simp: "^(Clause.to_tptp clause)));
       dbg D_prop_subs (lazy ("after  simp: "^(Clause.to_tptp new_clause)^ " prop_dep_lvl: "^(string_of_int prop_dep_lvl)));
       
       dbg_env D_prop_subs_assert
         ( fun () -> 

           (* check that the compl of new_clause is unsat in sim solver*)
(*           let lits = Clause.get_literals new_clause in *)
           let _prop_lits = List.map get_prop_lit_assign new_lits in    
           let prop_compl_lits = List.map get_prop_compl_lit new_lits in 
           let compl_lits = List.map add_compl_lit new_lits in 
           let sim = PropSolver.is_simplification solver_sim in
           let sim_ass = get_solver_assumptions ~soft:false ~sim in (* automatically added *)
           (
(*            match (solve_assumptions solver_sim compl_lits) with *)
            match (solve ~solver_in:solver_sim ~extra_assumptions:compl_lits ()) with 
           | PropSolver.Unsat -> 
               dbg D_prop_subs 
                 (lazy ("sim unsat: "^(PropSolver.lit_list_to_string solver_sim prop_compl_lits)
                        ^" num of ass"^(string_of_int (List.length sim_ass))));
	   | _-> 
               failwith ("sim sat: "^((PropSolver.lit_list_to_string solver_sim prop_compl_lits))
                         ^" num of ass: "^(string_of_int (List.length sim_ass)))
           );
(*
           match (fast_solve solver_sim prop_compl_lits) with
           | PropSolver.FUnsat -> 
               dbg D_prop_subs 
                 (lazy ("sim unsat: "^(PropSolver.lit_list_to_string solver_sim prop_compl_lits)
                        ^" num of ass"^(string_of_int (List.length sim_ass))));
	   | _-> 
               failwith ("sim sat: "^((PropSolver.lit_list_to_string solver_sim prop_compl_lits))
                         ^" num of ass: "^(string_of_int (List.length sim_ass)))
           );
  *)         
        (* check that compl of new_clause is are unsat in uc solver  *)
           let _prop_uc_lits = List.map get_prop_lit_uc_assign new_lits in    
           let prop_compl_uc_lits =  List.map get_prop_compl_lit_uc new_lits in 
           let uc_ass = get_solver_uc_assumptions ~soft:false ~sim:false in 
           (
            match 
             (PropSolver.solve_assumptions_upto_id_uc
	      solver_uc
	        (prop_compl_uc_lits @ uc_ass)
	      prop_dep_lvl
             )
           with 
            |PropSolver.Unsat -> 
                dbg D_prop_subs 
                  (lazy ("uc unsat: "    ^(PropSolver.lit_uc_list_to_string solver_uc prop_compl_uc_lits)
                         ^" num of ass: "^(string_of_int (List.length uc_ass))));
            |PropSolver.Sat -> 
                failwith ("uc sat: "^((PropSolver.lit_uc_list_to_string solver_uc prop_compl_uc_lits))
                          ^" num of ass: "^(string_of_int (List.length uc_ass)) 
                         )
           );
          );

       

       (* Clause was propositionally subsumed by some clauses up to
	  the currently highest clause ID *)
       
       add_clause_to_solver new_clause;
       
       (*	    out_str ("New Clause: "^(Clause.to_string new_clause)^"\n");*)
       new_clause )
  else 
    clause (*raise Non_simplifiable*)
  with 
    Prop_subs_not_eligible -> clause


let prop_subsumption_exhaustive (* context_param *) clause =
  let rec f c = 
    let subs_c = prop_subsumption_single (* context_param *) c in 
    if (c == subs_c)
    then 
      subs_c
    else
      f subs_c
  in
  f clause

(*
 let prop_subsumption clause = prop_subsumption_single clause 
*)
let prop_subsumption (* context_param *) clause = prop_subsumption_exhaustive (* context_param *) clause

(*
  let rec justify_prop_lit_subsumption clause_id accum = function

(* Terminate on empty list *)
  | [] -> accum

(* Take head element of list *)
  | literal :: tl ->

(* Get complementary propositional literal in unsat core solver *)
  let prop_compl_lit = get_prop_compl_lit_uc literal in

  match

  (

  try

(* Run unsat core solver with assumptions *)
  PropSolver.solve_assumptions_upto_id_uc
  solver_uc
  (prop_compl_lit :: (get_solver_uc_assumptions ()))
  clause_id

  with PropSolver.Unsatisfiable ->

  failwith
  "Could not get justification for propositional subsumption."

  )

  with

(* Should return unsat, but check *)
  | PropSolver.Unsat ->

(* Get the unsat core as a list of clause ids *)
  let unsat_core_ids = PropSolver.get_conflicts solver_uc in

(* Get first-order clauses from clause ids *)
  let unsat_core_clauses =
  List.fold_left
  (fun a c ->
  try
  (Hashtbl.find solver_uc_clauses c) :: a
  with Not_found ->
  a)
  []
  unsat_core_ids
  in

(* Append clauses in unsat core and continue with tail of list *)
  justify_prop_lit_subsumption
  clause_id
  (accum @ unsat_core_clauses)
  tl

(* Must not return sat when other solver returns unsat *)
  | PropSolver.Sat ->
  raise (Failure "Unsat core solver returned satisfiable when trying to justify propositional subsumption.")

 *)


(* justify_prop_subsumption: clause subsumes parent *)
let justify_prop_subsumption max_clause_id parent clause =
  
  (* Format.eprintf
     "Simplifed %a to %a@\n@."
     Clause.pp_clause clause
     Clause.pp_clause clause'; *)
  
  (* Assume complement of each not simplified literal *)
  let assumptions =
    List.map get_prop_compl_lit_uc (Clause.get_literals clause)
  in  
  dbg D_uc (lazy ("justify ps: clause: "^(Clause.to_tptp clause)^" max_clause_id: "^(string_of_int max_clause_id)));  
  dbg D_uc (lazy ("justify ps: parent: "^(Clause.to_tptp parent)));  
  dbg D_uc (lazy ("justify ps: clause prop uc assumptions: "^(PropSolver.lit_uc_list_to_string solver_uc assumptions)));  
  dbg D_uc (lazy ("justify ps:  solver_uc assumptions: "
                  ^(PropSolver.lit_uc_list_to_string solver_uc (get_solver_uc_assumptions ~soft:false ~sim:false))));  
  match    
    (     
     try
       (* Run unsat core solver with assumptions *)
       PropSolver.solve_assumptions_upto_id_uc
	 solver_uc
	 (assumptions @ (get_solver_uc_assumptions ~soft:false ~sim:false))
	 max_clause_id
	 
     with Unsatisfiable_gr_na ->       
       failwith
	 "Could not get justification for propositional subsumption."	 
    )
      
  with
    
    (* Should return unsat, but check *)
  | PropSolver.Unsat ->
      
      (* Get the unsat core as a list of clause ids *)
      let unsat_core_ids = PropSolver.get_conflicts solver_uc in
     
      dbg D_uc (lazy ("justify ps: unsat_core_ids: "^( list_to_string string_of_int unsat_core_ids " " )));  

      (* Get first-order clauses from clause ids *)
      let unsat_core_clauses =
	List.fold_left
	  (fun a c_id ->
	    try
	      (puf_get_clause c_id) :: a
	    with 
              Not_found ->
              (              
	       a (* ids are mixed with assumtions which needs to be filtered out *) 
              )
	  ) []
	  unsat_core_ids
      in
      dbg D_uc (lazy ("justify ps: unsat_core clauses: "^( Clause.clause_list_to_tptp unsat_core_clauses )));  
      (* Format.eprintf
	 "Justified by@\n%a@."
	 (pp_any_list Clause.pp_clause "\n") unsat_core_clauses; *)
      
      (* Return clauses in unsat core *)
      unsat_core_clauses
	
	(* Must not return sat when other solver returns unsat *)
  | PropSolver.Sat ->
      raise (Failure "Unsat core solver returned satisfiable when trying to justify propositional subsumption.")

(* Add groundings for the list of variables to the association list *)
let rec add_var_grounding accum = function
  | [] -> accum
  | v :: tl when List.mem_assoc v accum ->
      add_var_grounding accum tl
  | v :: tl ->
      add_var_grounding ((v, (get_gr_by_var v)) :: accum) tl

(* Return list of grounded literals and an association list
   documenting the groundings of the variables *)
let rec ground_literals (gnd_literals, grounding) = function
  | [] -> (gnd_literals, grounding)
  | lit :: tl ->
      
      let grounding' = add_var_grounding grounding (Term.get_vars lit) in
      (*
	ground_literals
	((Subst.grounding term_db_ref !gr_by_map lit) :: gnd_literals,
	grounding')
       *)
      ground_literals
	( (TermDB.add_ref (Term.get_grounding_lit lit) term_db_ref) :: gnd_literals,
	  grounding')
	tl

let ground_clause clause =  
  if Clause.is_ground clause 
  then   
    clause      
  else    
    (
     try
       (* Ground literals in clause *)
       let gnd_literals, grounding =
	 ground_literals ([], []) (Clause.get_literals clause)
       in
       let tstp_source =
	 Clause.tstp_source_grounding grounding clause in
       
       (* Create new ground clause *)
       let gnd_clause = create_clause tstp_source (List.rev gnd_literals) in
       
       (* Return clause *)
       gnd_clause
     with
     | 
       Term.Grounding_undef ->
	 (
          (* out_str ("Term_grounding_undef: "^(Term.to_string term)^"\n");
	  out_str ("Clause: "^(Clause.to_string clause)^"\n");
*)
	  out_str ("Clause: "^(Clause.to_string clause)^"\n");
	  failwith ("Term.Grounding_undef");
	 )
	   
    )


(*-------------------------------------*)

let preserve_lits_vals_solver ?(soft = false) lits =  
  let all_consistent =  (not (List.exists (fun lit -> not (get_solver_lit_val lit)) lits)) in
  if all_consistent 
  then
    true
  else
    begin
      try
        match (solve ~soft ~extra_assumptions:lits ()) with 
        | PropSolver.Unsat -> false
        | PropSolver.Sat   -> true
      with 
        AssumptionsInconsistent -> false
    end

let preserve_lits_vals_solver_gr ?(soft = false) lits =  
  let gr_lits = List.map get_grounded_lit lits in
  preserve_lits_vals_solver ~soft gr_lits


(* returns None if success and Some(UnsatCore.unsat_core) *)

(*
let preserve_lits_vals_solver_uc lits =
  if (preserve_lits_vals_solver lits)
  then 
    None
  else
    Some (get_unsat_core ~extra_assumptions:lits ())


let preserve_lits_vals_solver_gr_uc lits =
  let gr_lits = List.map get_grounded_lit lits in
  preserve_lits_vals_solver_uc gr_lits
*)

(*----------------Commented-----------------------*)

let reset_solvers () = 
(*  out_str (pref_str^"Solver resets are skipped\n");*)
  
  reset_gr_trie ();
  PropSolver.reset_solver solver;
  PropSolver.reset_solver_uc solver_uc;
  PropSolver.reset_solver solver_sim



let out_mem () = 
  print_objsize (module_name^" prop var_table:")  var_table;
  print_objsize (module_name^" puf: ") puf;
  print_objsize (module_name^" gr_trie_ref:") gr_trie_ref



(*----------------Commented-----------------------*)


(*

(*--------------------get term for grounding-----------------------*)

(* with the conjecture having a priority, not very good results

   let get_term_for_grounding () =
(* first try the  constant with max occurrence, which is in the conjecture*)
   let f_max_conj_sym s max_conj_sym =
   if (
   (Symbol.get_bool_param Symbol.is_conj_symb s) &&
   ((Symbol.get_type s) = Symbol.Fun) &&
   ((Symbol.get_arity s) = 0) &&
   (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_conj_sym))
   then s
   else max_conj_sym
   in
   let max_conj_sym = SymbolDB.fold f_max_conj_sym !symbol_db_ref bot_symb in
   let gr_symb =
   if (max_conj_sym == bot_symb) then
   let f_max_sym s max_sym =
   if (((Symbol.get_type s) = Symbol.Fun) &&
   ((Symbol.get_arity s) = 0) &&
   (Symbol.get_num_input_occur s) > (Symbol.get_num_input_occur max_sym))
   then s
   else max_sym
   in
   let max_sym = SymbolDB.fold f_max_sym !symbol_db_ref bot_symb in
   max_sym
   else
   max_conj_sym
   in
(* we need to find the term in term_db corresponding to max_sym*)
(* for this we just try to add it to term_db *)
   let gr_by_term = TermDB.add_ref (Term.create_fun_term gr_symb []) term_db_ref in
   gr_by_term

   let init_solver_exchange () =
   gr_by := (get_term_for_grounding ())
(* debug*)
(* out_str ("Term for grounding_new: "^(Term.to_string gr_by_new)^"\n");
   match gr_by_new with
   | Term.Fun(symb, _, _) ->
   out_str ("Number of occ_new: "^( string_of_int (Symbol.get_num_input_occur symb))^"\n")
   | _ -> ()
 *)

 *)

(*--------------------get term for grounding-----------------------*)
(* works but now much simpler version *)
(*

  let get_term_for_grounding () =
  let size = (SymbolDB.size !symbol_db_ref) +1 in
(*  out_str ("size: "^(string_of_int size)^"\n");*)
(* array contains number of occurences of constants, index is *)
  let occur_array = Array.make size 0 in
(*array of corresponding terms since we cannod easily find const term by symbol*)
  let const_term_array = Array.make size bot_term in
  let rec fill_term term =
  match term with
  | Term.Fun(symb, args, _) ->
(*      if (Term.is_empty_args args) then *)
  if (Term.is_constant term) then
  (let index = (Symbol.get_fast_key symb) in
(*	  out_str ("index: "^(string_of_int index)^"\n");*)
  Array.set occur_array index ((Array.get occur_array index) +1);
  Array.set const_term_array index term;
  )
  else
  Term.arg_iter fill_term args
  | Term.Var _ -> ()
  in
  let fill_clause clause =
  List.iter fill_term (Clause.get_literals clause) in
  let () = List.iter fill_clause !init_clause_list_ref in
  let index_max =
  let max = ref 0 in
  let index = ref 0 in
  Array.iteri
  (fun c_index c_max ->
(*	out_str ("index: "^(string_of_int c_index)^" num_occ: "^(string_of_int c_max)^" Term: "^(Term.to_string (Array.get const_term_array c_index))^"\n"); *)
  if c_max >= !max
  then
  (max := c_max; index:= c_index)
  else ()
  ) occur_array;
  !index
  in
  let gr_term = (Array.get const_term_array index_max)
  in gr_term

  let init_solver_exchange () =
  gr_by := (get_term_for_grounding ())
(*  out_str ("Term for grounding: "^(Term.to_string !gr_by)^"\n")*)
 *)

(*--------------------get term for grounding-----------------------*)
(* works but now much simpler version *)

  let get_term_for_grounding () =
  let size = (SymbolDB.size !symbol_db_ref) +1 in
(*  out_str ("size: "^(string_of_int size)^"\n");*)
(* array contains number of occurences of constants, index is *)
  let occur_array = Array.make size 0 in
(*array of corresponding terms since we cannod easily find const term by symbol*)
  let const_term_array = Array.make size bot_term in
  let rec fill_term term =
  match term with
  | Term.Fun(symb, args, _) ->
(*      if (Term.is_empty_args args) then *)
  if (Term.is_constant term) then
  (let index = (Symbol.get_fast_key symb) in
(*	  out_str ("index: "^(string_of_int index)^"\n");*)
  Array.set occur_array index ((Array.get occur_array index) +1);
  Array.set const_term_array index term;
  )
  else
  Term.arg_iter fill_term args
  | Term.Var _ -> ()
  in
  let fill_clause clause =
  List.iter fill_term (Clause.get_literals clause) in
  let () = List.iter fill_clause !init_clause_list_ref in
  let index_max =
  let max = ref 0 in
  let index = ref 0 in
  Array.iteri
  (fun c_index c_max ->
(*	out_str ("index: "^(string_of_int c_index)^" num_occ: "^(string_of_int c_max)^" Term: "^(Term.to_string (Array.get const_term_array c_index))^"\n"); *)
  if c_max >= !max
  then
  (max := c_max; index:= c_index)
  else ()
  ) occur_array;
  !index
  in
  let gr_term = (Array.get const_term_array index_max)
  in gr_term

  let init_solver_exchange () =
  gr_by := (get_term_for_grounding ())
(*  out_str ("Term for grounding: "^(Term.to_string !gr_by)^"\n")*)

  exception Given_clause_simplified
(* is weaker than prop_subsumption *)

  let prop_subs_resolution solver_sim solver gr_by clause =
(*  out_str ("\n Given Clause: "^(Clause.to_string clause)^"\n");*)
  let is_simplified = ref false in
(*  let lits = Clause.get_lits clause in*)
  let resolve rest lit =
  if (consistent_with_solver_lit solver lit) then lit:: rest
  else
  (let prop_lit = get_prop_lit lit in
(*      let prop_compl_lit = get_prop_compl_lit solver lit in*)
  let result = (solve_assumptions solver_sim [prop_lit]) in
  match result with
  | PropSolver.Unsat ->
(* out_str "Unsat Assmpt \n ";*)
  ( is_simplified:= true;
  incr_int_stat 1 porp_fo_subsumed;
  rest)
  | PropSolver.Sat -> lit:: rest
  )
  in
  let new_lit_list = Clause.fold resolve [] clause in
  if !is_simplified then
  ( (*out_str "Given Simplified! \n";*)
  eliminate_clause clause;
  if (new_lit_list = [])
  then raise Unsatisfiable
  else
  (let new_clause = Clause.create new_lit_list in
  if (not (ClauseAssignDB.mem new_clause !clause_db_ref))
  then
  (let added_clause =
  ClauseAssignDB.add_ref new_clause clause_db_ref in
(*add_clause_to_solver solver_sim solver gr_by added_clause;*)
  Clause.assign_when_born !num_of_instantiation_loops added_clause;
(*	out_str ("\n Clause: "^(Clause.to_string clause)^"\n");
  out_str ("\n Simplified to: "^(Clause.to_string added_clause)^"\n");*)
(* add_clause_to_unprocessed added_clause;*)
  added_clause)
  else
  raise Given_clause_simplified
(*added_clause*))
  )
  else () (*clause*)
 *)

(*----------------End Commented-----------------------*)
