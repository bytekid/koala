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





open Options
open Statistics 
open Lib
open Problem_properties
open Logic_interface
open Resolution_loop
open PredElim


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_trace 
  | D_init
  | D_out_prep_clauses
  | D_solver 
  | D_marshal
  | D_cone_symb
  | D_cone_symb_full
  | D_eq
  | D_pred_elim
  | D_pred_elim_keep
  | D_dom_taut
  | D_sem_filter
  | D_sub_typing
  | D_time
  | D_proof
  | D_impl_units
  | D_rm_added 

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_init -> "init"
  | D_out_prep_clauses -> "out_prep_clauses"
  | D_solver -> "solver"
  | D_marshal -> "marshal"
  | D_cone_symb -> "cone_symb"
  | D_cone_symb_full -> "cone_symb_full"
  | D_eq -> "eq"
  | D_pred_elim -> "pred_elim"
  | D_pred_elim_keep -> "pred_elim_keep"
  | D_dom_taut -> "dom_taut"
  | D_sem_filter -> "sem_filter"
  | D_sub_typing -> "sub_typing"
  | D_time -> "time"
  | D_proof -> "proof"
  | D_impl_units -> "impl_units"
  | D_rm_added -> "rm_added"

let dbg_groups =
  [
   (* D_trace;  *)
(*   D_time; *)

   (* D_sem_filter;  *)
   (* D_init;  *)
   (* D_out_prep_clauses;  *)
(*   D_dom_taut; *)
(*   D_marshal; *)
   (* D_solver; *)
   (* D_cone_symb;  *)
   (* D_eq; *)
   D_pred_elim; 
(*   D_solver; *)
   (* D_impl_units;  *)
(*   D_cone_symb_full; *)
(* D_proof; *)
(*   D_pred_elim_keep; *)
   (* D_rm_added; *)
 ]
    
let module_name = "preprocess"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)

let top_term = Parser_types.top_term

let is_ver_epr () = 
  (!current_options.aig_mode || (val_of_override  !current_options.bmc1_incremental)) 

(*--------------------------*)

type prep_state = 
  {
   mutable prep_clauses : clause list; (* current clauses *)

   mutable prep_side_clauses : clause list; (* used in prep_sem_filter *)
   mutable prep_side_atoms : term list; 
      (* we do not preprocess them but assume that they can be added later *)
      (* to the input so some eliminations can be blocked *)
      (* side atoms can be in assumptions to solver *)

   mutable prep_side_includes_eq : bool;
   mutable prep_inst_pre_model : Instantiation_env.inst_pre_model;
  
 }

let prep_create_state ~clause_list (* ~side_clauses *) ~extra_side_atoms = 
  let solver_assumptioins_atoms = 
    List.map Term.get_atom (TSet.elements (Prop_solver_exchange.get_solver_fof_assumptions ~soft:false ~sim:false)) 
  in
  { 
    prep_clauses = clause_list; 
    prep_side_clauses = []; (* side_clauses; *)
    prep_side_atoms = extra_side_atoms@solver_assumptioins_atoms;   
    prep_side_includes_eq = false;
    prep_inst_pre_model = BCMap.empty;
  }
   
let prep_get_inst_pre_model prep_state = prep_state.prep_inst_pre_model

let prep_get_clauses prep_state = prep_state.prep_clauses

let prep_get_side_clauses prep_state = prep_state.prep_side_clauses

(* ------------------------- *)
(* negative is unlimited *)
let prep_time_limit () =  
  dbg D_time (lazy (
               " time_out_real: "^(string_of_float !current_options.time_out_real)^
               " iprover_running_time: "^(string_of_float (iprover_running_time ()))^
              " time_out_prep_mult: "^(string_of_float !current_options.time_out_prep_mult)));
  ((!current_options.time_out_real -. (iprover_running_time ())) *. !current_options.time_out_prep_mult) 


(*
let prep_remaining_time () = 
  ((!current_options.time_out_real*. !current_options.time_out_prep_mult) -. (iprover_running_time ())) 
*)

(*
exception Prep_timeout

let check_time ~start_time ~time_limit = 
  let current_time = Unix.gettimeofday () in
  if (!current_options.time_out_real > 0.) 
  then 
    (
     let time_diff = (current_time -. start_time) in 
     if (time_diff > time_limit)
     then
       ( 
         dbg D_time (lazy (" timeout time_limit: "^(string_of_float time_limit)
                           ^" iprover_running_time: "^(string_of_float (iprover_running_time ()))
                           ^" prep_remaining_time: "^(string_of_float (prep_remaining_time ()))
                     ));

         raise Prep_timeout
        )
    )     
*)

(*----------- solver run and getting implied units ------*)

(* && compose options *)

let compose_prop_impl_unit_opt_list lit = 
  Term.compose_bool_prop_opt_list (&&) true !current_options.prop_impl_unit lit


let impl_unit_to_keep lit =   
  ((Term.get_num_of_symb lit) <= !current_options.prop_impl_unit_size) && 
  (compose_prop_impl_unit_opt_list lit) &&
  (Term.is_well_typed_term ~allow_sub_types:false lit) 
  
 

let get_all_new_implied_units () = 
  if (!current_options.prop_impl_unit_size <= 0)
  then ([])
  else
    (
     Prop_solver_exchange.get_all_newly_implied_unit_clauses 
       ~is_relevant:impl_unit_to_keep
    )
 
let prep_solver_run prep_state =

  List.iter Prop_solver_exchange.add_clause_to_solver prep_state.prep_clauses;
  dbg D_solver (lazy "solver_check");
  if ((Prop_solver_exchange.solve ~soft:false ()) = PropSolver.Unsat)
  then 
    (
     raise Unsatisfiable_gr
    )
  else
    begin
      (* run solve on solver_sim to infer more units in solver_sim *)
      let solver_sim_result =(Prop_solver_exchange.solve ~solver_in:Prop_solver_exchange.solver_sim ()) in 
      assert (not (solver_sim_result = PropSolver.Unsat)); (* solver_sim should not be unsat if solver is not unsat *)
 
     (if (!current_options.prop_impl_unit_size > 0)
      then
        (
         let new_implied_units = get_all_new_implied_units () in
         dbg D_impl_units (lazy (Clause.clause_list_to_string new_implied_units));
         prep_state.prep_clauses <- 
           CSet.elements (CSet.union (CSet.of_list new_implied_units) (CSet.of_list prep_state.prep_clauses))
           (* new_implied_units@prep_state.prep_clauses *)
        )
      else ()
      )

    end
  
   
(* -------------------------------------- *)
let remove_true_false clause = 
  let changed = ref false in
  let f lit_rest lit = 
    let pred = Term.lit_get_top_symb lit in 
    let sign = Term.is_pos_lit lit in 
    let is_true_atom = (pred == Symbol.symb_true) in
    let is_false_atom = (pred == Symbol.symb_false) in
    match (sign, is_true_atom, is_false_atom) with
(* true lit *)
    | (true, true, _) | (false,_,true) -> 
	raise Eliminated
	  
(* false lit *)
    | (false,true,_) | (true,_,true) ->
	changed:= true;
	lit_rest

    |_-> 
	lit::lit_rest
  in
  let new_lits = Clause.fold f [] clause in
  if !changed 
  then 
    let tstp_source = Clause.tstp_source_true_false clause in
    let new_clause = create_clause tstp_source new_lits in 
    check_empty_clause new_clause; 
    new_clause
  else
    clause

(* can raise Eliminated *)
let get_sim_self_fun_list ~before_eq_axioms = 
  let o =  !current_options in
  [
   remove_true_false;

   if (before_eq_axioms  && o.prep_unflatten) then Simplify.equality_resolution else id_fun; 

   Simplify.equality_resolution_simp; (* fine with eq axioms *)
   Simplify.tautology_elim;   

   if before_eq_axioms then Simplify.eq_tautology_elim else id_fun;

(*--prop subs-*)
   if o.prep_gs_sim  then Simplify.forward_prop_subsume else id_fun;
 ]
    

let sim_self_clauses ~before_eq_axioms clauses = 
  let sim_self_fun_list = get_sim_self_fun_list ~before_eq_axioms in
  let f rest c = 
    try
      let new_c = fold_left_fun_list sim_self_fun_list c in   
      new_c::rest
    with 
      Eliminated -> 
	rest
  in 
  List.fold_left f [] clauses
 
(*
  let prop_simp clause_list = 
  (* debug *)
  (* List.iter 
     (fun c -> 
     Format.printf "Prep: %a@.\n" (TstpProof.pp_clause_with_source false) c; 	
     Prop_solver_exchange.add_clause_to_solver c;
     )
     clause_list;
   *)

  List.iter 
  Prop_solver_exchange.add_clause_to_solver clause_list;
  (if ((Prop_solver_exchange.solve ()) = PropSolver.Unsat)
  then 
  ((* Format.eprintf "Unsatisfiable after solve call in Preprocess.prop_sim@."; *)
  (* Raise separate exception, since BMC1 must continue if
     simplified and must not continue if solver is in invalid state *)
  (* raise PropSolver.Unsatisfiable *)
  raise Unsatisfiable_gr
  )
  else ());
  let simplify_clause rest clause = 
  (Prop_solver_exchange.prop_subsumption clause)::rest
  in
  List.fold_left simplify_clause [] clause_list
 *)  

    

(*------Non-equational to Equational (based on input options)-----------*) 

module SymbKey = 
  struct
    type t    = symbol
    let equal = (==)
    let hash  = Symbol.get_fast_key 
  end 

module PredToFun = Hashtbl.Make (SymbKey)
    

let pred_to_fun_symb pred_to_fun_htbl pred = 
  try 
    PredToFun.find pred_to_fun_htbl pred
  with 
    Not_found ->
      let new_symb_name = ("$$iProver_FunPred_"^(Symbol.get_name pred)) in
      let new_type = 
	match (Symbol.get_stype_args_val pred) with
	|Def(old_args, old_val) ->
	    Symbol.create_stype old_args Symbol.symb_bool_type
	|Undef -> 
	    Symbol.create_stype [] Symbol.symb_default_type    
      in
      let fun_symb = 
	Symbol.create_from_str_type_property
	  new_symb_name new_type Symbol.FunPred in
      let added_fun_symb = SymbolDB.add_ref fun_symb symbol_db_ref in
      PredToFun.add pred_to_fun_htbl pred added_fun_symb;
      added_fun_symb

	
let pred_to_fun_atom pred_to_fun_htbl atom =
  match atom with 
  |Term.Fun (pred,args,_) -> 
      if not (pred == Symbol.symb_typed_equality)
      then 
	let fun_symb = pred_to_fun_symb pred_to_fun_htbl pred in
	let fun_term = add_fun_term_args fun_symb args in 
	let eq_term  = add_typed_equality_sym Symbol.symb_bool_type fun_term top_term in
	eq_term
      else
	atom
  |_ -> failwith "pred_to_fun_atom should not be var"


let pred_to_fun_lit pred_to_fun_htbl lit =
  let new_lit = Term.apply_to_atom (pred_to_fun_atom pred_to_fun_htbl) lit in 
  TermDB.add_ref new_lit term_db_ref
    
    

let pred_to_fun_clause pred_to_fun_htbl clause = 
  let new_lits = 
    List.map
      (pred_to_fun_lit pred_to_fun_htbl)
      (Clause.get_literals clause) in
  let tstp_source = Clause.tstp_source_non_eq_to_eq clause in		
  let new_clause = create_clause tstp_source new_lits in
  (* Clause.assign_non_eq_to_eq_history new_clause clause; *)
  
  new_clause



(* *)
let res_prep_options () = 
  {!current_options
  with 
   (*----Resolution---------*)
   
   resolution_flag = true;
   
   res_prop_simpl_new = 
   if (is_ver_epr ()) 
   then 
     false
   else
     true;

   res_prop_simpl_given = 
   if (is_ver_epr ()) 
   then 
     false
   else
     true;
   res_passive_queue_type = PQT_PriorityQueues;
   res_passive_queues =
   [
    [Cl_Num_of_Lits false; Cl_Num_of_Symb false]
  ];
   res_passive_queues_freq = [150];
   
   res_forward_subs = Subs_Full;
   res_backward_subs = Subs_Full;
   res_forward_subs_resolution = true;
   (*  res_forward_subs_resolution    = true; exp later for sat *)
   (* res_backward_subs_resolution   = false; *)
   res_backward_subs_resolution = true;
   res_time_limit = 60.0;
 }


(*------------- res_preprocess ---------*)
let res_preprocess clause_list = 
  let old_options = !current_options in 
  current_options := res_prep_options ();
  let res_state = res_create_state ~res_prep_only:true in
  res_add_clause_list res_state clause_list;
  let preprocessed_clauses = res_preprocess res_state in     
  current_options := old_options;
  preprocessed_clauses



(*------------- EPR domain tautology -----------------------------*)
    (* EPR *)
(* C\/ x=c1 \/...\/ x=cn  is taut;  where c1 .. cn are exactly all domain constants (of the same type); (e.g.  the problem is EPR with eq)  *)

(* domain_const_set_map: type -> all constants of this type *)


let add_var_const_map var const v_cset_map =   
  let cset =  
    try
      TMap.find var v_cset_map  
    with 
      Not_found -> TSet.empty 
  in
  let new_cset = TSet.add const cset in 
  TMap.add var new_cset v_cset_map

let add_stype_const_map const type_cset_map = 
  let ctype = Term.get_term_type const in 
  let cset =  
    try
      SMap.find ctype type_cset_map  
    with 
      Not_found -> TSet.empty 
  in
  let new_cset = TSet.add const cset in 
  SMap.add ctype new_cset type_cset_map
    
let is_const_domain_tautology domain_const_set_map clause = 
  if (Clause.has_eq_lit clause) 
  then 
    let lits = Clause.get_lits clause in
    (* get clause map: var-> const set *)
    let f rest lit = 
      match (term_eq_view_type_symb lit) with  (* should occur as positive eq *)
      |Def (Eq_type_symb (symb, t1, t2)) ->           
          if (Term.is_var t1) && (Term.is_const_term t2) || (Term.is_var t2) && (Term.is_const_term t1)
          then
            let var, const = 
              if (Term.is_var t1) && (Term.is_const_term t2)
              then
                (t1, t2) 
              else
                (t2, t1)
            in
            add_var_const_map var const rest
          else
            rest
      |Undef -> rest            
    in
    let v_cset_map = List.fold_left f TMap.empty lits in

(* check if one of the vars has the whole domain *)
    let g v clause_cset = 
      let v_type = Term.get_term_type v in       
      try 
        let domain_cset = SMap.find v_type domain_const_set_map in 
        if (TSet.equal clause_cset domain_cset) 
        then 
          (
           dbg D_dom_taut (lazy (Clause.to_string clause));
           true
          )
        else
          false
      with 
        Not_found -> false 
    in
    TMap.exists g v_cset_map
  else (* no eq lits *)
    false
      

(* ! asssume EPR ! *)
let ext_const_domain_lit domain_const_set_map lit = 
  let atom = Term.get_atom lit in
  let relevant_args = 
    match (term_eq_view_type_symb atom) with 
    |Def (Eq_type_symb (symb, t1, t2)) ->           
        [t1;t2]
    |Undef -> 
        (match atom with 
        |Term.Fun (stype, args, _) -> Term.arg_to_list args
        | Term.Var _ -> failwith "ext_const_domain: atom should not be var"
        )   
  in
  let f rest t = 
    assert ((Term.is_var t) || (Term.is_const_term t));
    if (Term.is_const_term t) 
    then 
      add_stype_const_map t rest 
    else
      rest
  in 
  List.fold_left f domain_const_set_map relevant_args

let ext_const_domain_cl domain_const_set_map cl = 
  Clause.fold ext_const_domain_lit domain_const_set_map cl

let get_domain_const_set_map clause_list = 
  List.fold_left ext_const_domain_cl SMap.empty clause_list

(* ! asssume EPR ! *)
let elim_const_domain_tautologies clause_list = 
  let domain_const_set_map = get_domain_const_set_map clause_list in 
  List.filter (fun c ->  not (is_const_domain_tautology domain_const_set_map c)) clause_list 

(*------------------  Prep sem filter -------------------------*)
(*     out_str "\n\n\n Before Filtering \n\n\n ";              *)

let prep_sem_filter prep_state =       
  let out_progress = true in
  let start_sf_time = Unix.gettimeofday () in     
  if !current_options.prep_sem_filter_out
  then
    (
     
     (*-------------------------------------------------*)
     out_str (pref_str^"Semantic Filtering...\n");
     (*-------------------------------------------------*)

     out_str (pref_str^"Input cluases sem filter:\n");
     Clause.out_clause_list_tptp prep_state.prep_clauses;
   	 
     (*	 out_str (pref_str^"Semantically Preprocessed Clauses:\n");*)
     
(*     let side_clauses = (get_side_clauses ()) in *)
     let side_clauses = prep_state.prep_side_clauses in
     let side_atoms = prep_state.prep_side_atoms in 
     let filtered_state =
       Prep_sem_filter_unif.sem_filter_unif (prep_state.prep_clauses) ~side_clauses ~side_atoms
     in
     let filtered_in_clauses =
       filtered_state.Prep_sem_filter_unif.filtered_in in
       
     out_str ("\n\n"^pref_str^"Semantically Preprocessed Clauses:\n");
     
     Clause.out_clause_list_tptp filtered_in_clauses;
     
     dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Filtered in clauses: \n"));
     dbg D_sem_filter  (lazy  (Clause.clause_list_to_string filtered_in_clauses));
     dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Filtered out clauses: \n"));
     
     dbg D_sem_filter  (lazy  
                          (Clause.clause_list_to_string 
                             (Instantiation_env.inst_pm_get_clauses filtered_state.Prep_sem_filter_unif.filtered_out_inst_pre_model)
                          )
                       );
     
     dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Side clauses: \n"));
     dbg D_sem_filter  (lazy (Clause.clause_list_to_string side_clauses ));

     dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Side atoms: \n"));
     dbg D_sem_filter  (lazy (Term.term_list_to_string side_atoms ));

	 
     out_str "\n\n";
(*     out_str (Proof_search_schedule.unknown_str ()); *)
     out_str "% SZS status Unkown";
     out_stat ();
     exit(0);
     (* raise SZS_Unknown *)
    )
  else
    (
	 (* if (!current_options.prep_sem_filter &&
	    (not (Symbol.is_input Symbol.symb_equality)))
	  *)
     (* was as above but equality should be ok, *)
     
     (* problem with bmc1 *)
     

     if ((!current_options.prep_sem_filter != Sem_Filter_None)
(*
	   &&
	 (not (val_of_override !current_options.bmc1_incremental))
	   &&
	 (match !current_options.schedule with
	     | Schedule_verification_epr_old
	     | Schedule_verification_epr_tables
	     | Schedule_verification_epr
	       -> false
	     | _ -> true

	 )
	  *) 
	)
     then

       (
	(*-------------------------------------------------*)
(*	out_str (pref_str^"Semantic Filtering...\n"); *)
	(*-------------------------------------------------*)
	
	    (*	  out_str "\n\n\n!!!! Fix Sem Filter for Finite models and BMC1 !!!!!!\n\n\n";*)
	    (*          current_clauses := Prep_sem_filter.filter !current_clauses)*)
(*	    	  current_clauses := List.sort Clause.cmp_num_lits !current_clauses; *)
	
	(* let side_clauses = get_side_clauses () in *)


        if out_progress then (print_string " sf_s "; flush stdout;);

        let side_clauses = prep_state.prep_side_clauses in 
        let side_atoms = prep_state.prep_side_atoms in 
(*
  dbg_env D_sem_filter 
              (fun () ->
               let neg_filter_clauses = 
                 !current_options.prep_sem_filter <- Options.Sem_Filter_Neg;
                 Prep_sem_filter_unif.sem_filter_unif !current_clauses side_clauses               
               in
               let exh_filter_clauses = 
                 !current_options.prep_sem_filter <- Sem_Filter_Exhaustive;
                 Prep_sem_filter_unif.sem_filter_unif !current_clauses side_clauses               
               in
               let neg_filter_set = CSet.of_list neg_filter_clauses.Prep_sem_filter_unif.filtered_in in 
               let exh_filter_set = CSet.of_list exh_filter_clauses.Prep_sem_filter_unif.filtered_in in 
               if (CSet.equal neg_filter_set  exh_filter_set) 
               then 
                 (dbg D_sem_filter  (lazy  ("NEG and EXH are equal "));)
               else
                 (dbg D_sem_filter  (lazy  ("NEG and EXH are diff  "));)
              );
*)

        dbg D_sem_filter (lazy ("----------- Input cluases sem filter ----------\n"
                          ^(Clause.clause_list_to_string prep_state.prep_clauses)));

        dbg D_sem_filter (lazy ("----------- Side cluases sem filter ----------\n"
                          ^(Clause.clause_list_to_string prep_state.prep_side_clauses)));

        dbg D_sem_filter (lazy ("----------- Side atoms sem filter ----------\n"
                          ^(Term.term_list_to_string prep_state.prep_side_atoms)));
        
	let filtered_state =
	  Prep_sem_filter_unif.sem_filter_unif prep_state.prep_clauses ~side_clauses ~side_atoms
	in
	 (*   current_clauses := filtered_clauses.Prep_sem_filter_unif.filtered_in; *)
         (* normalise; not sure why but works better than non-normalised for erp non-horn eq *)
	prep_state.prep_clauses <- (CSet.elements (CSet.of_list filtered_state.Prep_sem_filter_unif.filtered_in)); 

(*
	    filtered_out_inst_pre_model_ref :=
	      filtered_clauses.Prep_sem_filter_unif.filtered_out_inst_pre_model;
*)

        let filtered_out_inst_pre_model = filtered_state.Prep_sem_filter_unif.filtered_out_inst_pre_model in
        prep_state.prep_inst_pre_model <-  
          Instantiation_env.inst_pre_model_union 
            prep_state.prep_inst_pre_model filtered_out_inst_pre_model;

	
        dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Filtered in clauses: "
                                      ^(string_of_int (List.length filtered_state.Prep_sem_filter_unif.filtered_in))
                                      ^"\n"));
	dbg D_sem_filter  (lazy  (Clause.clause_list_to_tptp filtered_state.Prep_sem_filter_unif.filtered_in));
	dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Filtered out clauses: "
                                  ^(string_of_int (BCMap.cardinal filtered_out_inst_pre_model))
                                  ^"\n"));
	dbg D_sem_filter  (lazy  (Clause.clause_list_to_tptp (Instantiation_env.inst_pm_get_clauses filtered_out_inst_pre_model)));
(*
	dbg D_sem_filter  (lazy  ("\n\n"^pref_str^"Filtered out clauses: "
                                  ^(string_of_int (BCMap.cardinal  prep_state.prep_inst_pre_model))
                                  ^"\n"));
	dbg D_sem_filter  (lazy  (Clause.clause_list_to_tptp (Instantiation_env.inst_pm_get_clauses  prep_state.prep_inst_pre_model)));
  *)
      
        let end_sf_time = Unix.gettimeofday () in         
        let sf_time_int = truncate (end_sf_time -. start_sf_time) in
        
        if out_progress then
          (
           print_string (" rm: "^ (string_of_int (BCMap.cardinal filtered_out_inst_pre_model)));
           print_string (" "^ (string_of_int (sf_time_int))^"s ");
           print_string " sf_e "; flush stdout;      
          );
       )
	 else ()
    )
(*; 
 
 (* TODO: move to iProver *)
	    (
	     if (!current_options.sat_mode || !current_options.sat_finite_models ||
	     !current_options.schedule = Schedule_sat)
	     then
	       (

		let filtered_clauses =
		  Prep_sem_filter_unif.sem_filter_unif
		    !current_clauses_no_eq (List.rev_append !gen_equality_axioms side_clauses)
		in
		
		current_clauses_no_eq :=
		  filtered_clauses.Prep_sem_filter_unif.filtered_in;

                filtered_out_inst_pre_model_ref :=
                  filtered_clauses.Prep_sem_filter_unif.filtered_out_inst_pre_model;

	       )
	     else ()
	    )
	   )
	 else ()
    )
  *)
    
(*--------------End sem filter---------------------------*)

  let get_side_preds prep_state = 
    let f rest atom = 
      let pred = Term.get_top_symb atom in
      SSet.add pred rest
    in
    List.fold_left f SSet.empty prep_state.prep_side_atoms
      

(*--------------------- Pred Elim -----------------------------*)

let prep_pred_elim problem_properties clause_list ~side_preds = 

  dbg D_pred_elim (lazy ("prob prop:" ^(Problem_properties.prob_props_to_string problem_properties)^"\n"));

  let (init_pred_elim_set', _not_used_num_occur_map) = 
    PredElim.get_most_preds_to_eliminate (Clause.CL_List (clause_list)) in     
  
  dbg D_pred_elim (lazy ("init_pred_elim_set':" ^(Symbol.list_to_string (SSet.elements init_pred_elim_set')^"\n")));
  let init_pred_elim_set = SSet.diff init_pred_elim_set' side_preds in 
  
  dbg D_pred_elim (lazy ("init_pred_elim_set:" ^(Symbol.list_to_string (SSet.elements init_pred_elim_set)^"\n")));
  
  Statistics.assign_int_stat (SSet.cardinal init_pred_elim_set) Statistics.pred_elim_cands;
  
  let cmp_num_occ num_occur_map p1 p2 = 
    try
      let get_occ_num pred = 
	(SMap.find pred num_occur_map)
      in
      Pervasives.compare (get_occ_num p1)  (get_occ_num p2)
    with 
      Not_found -> 0 
	  (* if one of them of the pred is not found
	     (it can happen when elimination set contains predicates that are not in the map/simplified cluase set) *) 
  in       
  
(* order by aig depth *)
(* high depth first which corresponds to inputs (invert depth in preprocess in reasoning or not ?) *)

  let cmp_depth_inv_fun p1 p2 = 
    if (is_ver_epr ())
    then
      Pervasives.compare (get_pred_depth p2) (get_pred_depth p1) 
    else
      0
  in  
  let pred_elim_cmp_fun context = 
    let (pred_elim_set, num_occur_map) = 
      PredElim.get_most_preds_to_eliminate (Clause.CL_Context (context)) in     
    

    (if (val_of_override !current_options.bmc1_incremental)
    then 
      lex_combination [cmp_depth_inv_fun; (cmp_num_occ num_occur_map)] 
    else
      (cmp_num_occ num_occur_map)
    )

  in

  let num_of_input_clauses = (Statistics.get_val_stat num_of_input_clauses) in

  let pred_elim_options = 
    {
     pe_has_eq = (has_eq problem_properties); 
     pe_estim_num_of_lits = 1000; (* 1000; *)

(*
  (if (is_ver_epr ())
  then
  if  (num_of_input_clauses < 1000000 (* 100 000 *))
  then
  45
  else
  25  (*260*) (* 25 *) (* 45 *) (* 65 *) (*85*) (* 65 *)
  else
  40 (* 1000 *)
  );
 *)

     pe_conclusion_limit_test = 
     (fun c -> 
       (Clause.num_of_symb c) < 1000
     );
     
     pe_preprocess_conclusion_extern = (fun c -> c); (* identity *) 

(*
  pe_clause_length_limit = 
  (if  (is_ver_epr ())
  then
  20  (* 8 *) (* 26 *) (* 13*)
  else
  50
  ); 
 *)
(*100;*)
(*	(if  (is_ver_epr ())
  then
  13  (* 8 *) (* 26 *) (* 13*)
  else
  8 (* 8 *) (* 50 *)
  );
 *)
(* not evaluated on aigs *)
     pe_keep_elim =  
     (fun ~elim_symb ~clauses_before_elim ~clauses_after_elim ->           
       let num_cl_before = (List.length clauses_before_elim) in 
       let num_cl_after  = (List.length clauses_after_elim) in
       let keep_res = 
         if num_cl_after = 0 
         then 
           ( 
             dbg D_pred_elim (lazy ("pe_keep_elim: all clauses are simplified" ));
             true
            )
         else 
           begin
             let get_num_of_symb cl_list = 
               List.fold_left (fun rest c -> (Clause.num_of_symb c) + rest) 0 cl_list 
             in 
             let get_num_of_lits cl_list =
               List.fold_left (fun rest c -> (Clause.length c) + rest) 0 cl_list 
             in 
             
             let num_symbs_before = get_num_of_symb clauses_before_elim in 
             let num_symbs_after = get_num_of_symb clauses_after_elim in 
             
             let num_lits_before = get_num_of_lits clauses_before_elim in 
             let num_lits_after = get_num_of_lits clauses_after_elim in 
             

             
             assert (num_cl_before > 1);
             let cl_max_vars_before = list_find_max_element Clause.cmp_num_var clauses_before_elim in 
             let cl_max_vars_after = list_find_max_element Clause.cmp_num_var clauses_after_elim in 
             
(*  TODO: experiment with let num_vars_clause c = VSet.cardinal (Clause.get_var_set c) in *)
(*        but note that this can undo splitting nvd *)
(*             let num_vars_clause c = VSet.cardinal (Clause.get_var_set c) in *)
             let num_vars_clause c = Clause.num_of_var c in  (* num of var occurrences *)

(* varible square mesure per clause cl = \sum (num var lits)^2 *)
             let get_norm_vars cl_list = 
               List.fold_left 
                 (fun rest c -> 
                   let num_c_vars = (num_vars_clause c)
                   in num_c_vars*num_c_vars + rest) 0 cl_list 
             in
             
             let num_norm_vars_before = get_norm_vars clauses_before_elim in
             let num_norm_vars_after  = get_norm_vars clauses_after_elim in
             let num_eq_lits_cl cl = 
               if (Clause.has_eq_lit cl) 
               then 
                 Clause.fold 
                   (fun num_eq_lits lit -> 
                     if (Term.is_eq_lit lit) then (num_eq_lits+1) else num_eq_lits)
                   0 cl
               else 
                 0
             in
             let num_eq_lits cl_list =   
               List.fold_left 
                 (fun rest c -> 
                   (num_eq_lits_cl c) + rest
                 )
                 0 cl_list 
             in
             let num_eq_lits_before = num_eq_lits clauses_before_elim in
             let num_eq_lits_after  = num_eq_lits clauses_after_elim in
             

             let cl_max_lits_before = list_find_max_element Clause.cmp_num_lits clauses_before_elim in 
             let cl_max_lits_after = list_find_max_element Clause.cmp_num_lits clauses_after_elim in 
             
             dbg D_pred_elim (lazy ("pe_keep_elim: cl_max_vars: before: "^(Clause.to_string cl_max_vars_before)
                                    ^" after: "^(Clause.to_string cl_max_vars_after)));
             
             dbg D_pred_elim (lazy ("pe_keep_elim: num_cl: before: "^(string_of_int num_cl_before)
                                    ^" after: "^(string_of_int num_cl_after)));

             dbg D_pred_elim (lazy ("pe_keep_elim: num_symbs: before: "^(string_of_int num_symbs_before)
                                    ^" after: "^(string_of_int num_symbs_after)));
             
             dbg D_pred_elim (lazy ("pe_keep_elim: num_lits: before:  "^(string_of_int num_lits_before)
                                    ^" after: "^(string_of_int num_lits_after)));
             
             dbg D_pred_elim (lazy ("pe_keep_elim: num_eq_lits: before:  "^(string_of_int num_eq_lits_before)
                                    ^" after: "^(string_of_int num_eq_lits_after)));
             
             dbg D_pred_elim (lazy ("pe_keep_elim: num_norm_vars: before: "^(string_of_int num_norm_vars_before)
                                    ^" after: "^(string_of_int num_norm_vars_after)));

             dbg D_pred_elim (lazy ("pe_keep_elim: cl_max_num_lits: before: "
                                    ^(string_of_int (Clause.length cl_max_lits_before))
                                    ^" after: "^(string_of_int (Clause.length cl_max_lits_after))));
             
             dbg_env D_pred_elim_keep
               (fun () -> 
                 if(

                   num_norm_vars_after  <=  num_norm_vars_before
                     &&
(*                     
                       num_lits_after <=  num_lits_before
                       &&
 *)                   
                   num_symbs_after <=  num_symbs_before
                     &&
                   num_lits_after >  num_lits_before
                     (*                 
                                        (Clause.length cl_max_lits_after) >  (Clause.length cl_max_lits_before)
                      *)
(*
  &&
  (num_cl_after > num_cl_before) 
 *)
                  )
                 then
                   (
                    dbg D_pred_elim_keep (lazy "\n ");
                    dbg D_pred_elim_keep (lazy "Clauses before elim: ");
                    out_str (Clause.clause_list_to_string clauses_before_elim);
                    dbg D_pred_elim_keep (lazy "Clauses after elim: ");
                    out_str (Clause.clause_list_to_string clauses_after_elim);
                   )
                 else
                   ()
               );
             (*----------------*)     
(*               (num_cl_after <= num_cl_before) &&  *)
             
             (*  num_symbs_after <=  num_symbs_before *)

(* 
   exp 1239
   num_lits_after <=  num_lits_before                 
   &&
   (Clause.cmp_num_var cl_max_vars_before cl_max_vars_after) >= 0                 
 *)

             ( 
               (*(Clause.cmp_num_var cl_max_vars_before cl_max_vars_after) >= 0    
                 &&
                *)
               (*
                 num_symbs_after <=  num_symbs_before 
                 &&
                *)


               (
(*                
                  num_norm_vars_after  <=  num_norm_vars_before 
                  &&
                  num_lits_after <=  num_lits_before
 *)

(* exp 1246 *)
(*
  num_norm_vars_after  <=  num_norm_vars_before
  &&
  num_lits_after <=  num_lits_before

 *)
(*

  num_norm_vars_after  <=  num_norm_vars_before
  &&
 *)
(*  
    num_lits_after <=  num_lits_before
    &&
 *)
(*

  num_symbs_after <=  num_symbs_before
  &&
  num_norm_vars_after  <=  num_norm_vars_before
 *)

(*

  num_cl_after <= num_cl_before
  &&
  num_lits_after <=  num_lits_before
  &&
  (num_vars_clause cl_max_vars_after) <= (num_vars_clause cl_max_vars_before)
 *)

                
                (
                 num_norm_vars_after  <  num_norm_vars_before
               ||
                 (num_norm_vars_after =  num_norm_vars_before
                    &&
                  num_symbs_after <= num_symbs_before                 
                 )
                   
)                  
                  

(*
  &&

  (Clause.length cl_max_lits_after) <=  (Clause.length cl_max_lits_before)
 *)
(*
  &&

  (num_cl_after <= num_cl_before) 
 *)
(*                    &&
                      num_eq_lits_after <=  num_eq_lits_before 
 *)
(*
  &&
  num_symbs_after <=  num_symbs_before
  &&
  num_eq_lits_after <=  num_eq_lits_before
 *)
(*

  num_norm_vars_after  <=  num_norm_vars_before
  &&
  num_symbs_after <=  num_symbs_before
 *)
(*                    &&
                      num_eq_lits_after <=  num_eq_lits_before
 *)


                  (*     num_eq_lits_after <=  num_eq_lits_before
                         &&
                   *)
(*
  (
  num_norm_vars_after  <  num_norm_vars_before
  ||
  (num_norm_vars_after =  num_norm_vars_before
  &&
  num_lits_after <= num_lits_before                 
  )
  
  )
  

 *)              
                  
               )
              )
           end
       in
       dbg D_pred_elim (lazy ("pe_keep_elim: keep ?: "^(string_of_bool keep_res)));
(*          out_warning (" preprocess: pred_elim: keep_res replaced by true "); *)
(*          true *)
       

       keep_res  

     ); 
     
     (* (if (is_ver_epr ())   *)
     (* then *)
     (*   (fun ~num_cl_before ~num_cl_after ->  *)
     (*     (num_cl_after <= num_cl_before)  || (num_cl_after <= 2)) (\* (num_cl_after <= 6) ) *\) *)
     (* else *)
     (*   (fun ~num_cl_before ~num_cl_after ->  *)
     (*     (num_cl_after <= num_cl_before) (\* ||  (num_cl_after <= 6)*\) ) *)
     (* ); *)

     pe_elim_order_cmp_fun = pred_elim_cmp_fun; (* NOT USED *)
     pe_elimination_set = init_pred_elim_set; 
     
(* 1/4 of the remaining time *)
     pe_time_limit = prep_time_limit ();
(*
     (let total_timeout = 
       let timeouts = [!current_options.time_out_real; !current_options.time_out_virtual] in
       let timeouts_pos = List.filter (fun a -> a > 0.) timeouts in
       if timeouts_pos = [] 
       then -1. 
       else
         list_find_min_element Pervasives.compare timeouts_pos 
     in
     let pe_time_lim =

       (if (total_timeout > 0.)
       then          
         let time_limit = 
           (total_timeout -. (iprover_running_time ())) *. !current_options.time_out_prep_mult           
         in
         if (time_limit > 10.)
         then 
           (  
              time_limit 
             )
         else 
           20.
(*           (!current_options.time_out_real -. (iprover_running_time ()))/. 6. *)
       else
         -1.
       ) 
     in
     dbg D_pred_elim (lazy ("pe_time_limit: "^(string_of_float pe_time_lim)));
     pe_time_lim
     );
*)

(* simplifications *)

(*	subs_cl_to_cl_limit = 100000; *)
     subs_cl_to_cl_limit = 200000;  


(* sim prop *)
     prop_glb_subs =  
     (if (is_ver_epr ())
     then
       if (num_of_input_clauses < 10000 )
       then
	 true  (* prop global subsumtion changed for finite models exp. *)
       else
	 false
     else
       true  (* false *)
(*
  if (!current_options.qbf_mode)
  then 
  false
  else
  true (* false *)
 *)
     );
     
(* sim local *) 
     
     lcl_add_to_sub_index_test = 
     (fun c ->
       (((Clause.num_of_var c) <= 20) && ((Clause.num_of_symb c) <= 1000))
     );

     (* Options.res_subs_type: type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int *)
     
     lcl_fwd_subs = (* true; *)
     (if  (is_ver_epr ())
     then
       if (num_of_input_clauses < 200000)
       then
	 true
       else
	 false
     else
       true  (* false *)
     );

     lcl_fwd_subs_res = (* false; *)

     (if  (is_ver_epr ())
     then
       if (num_of_input_clauses < 100000 (* 100000*))
       then
	 true
       else
	 false
     else
       true (*  false *)
     );


     lcl_bwd_subs     = (* Subs_Full; *)
(*  Subs_By_Length(2); *)
     (if (is_ver_epr ())
     then
       if  (num_of_input_clauses < 100000) (* (num_of_input_clauses < 400000)*)
       then
	 Subs_By_Length(1) (* Subs_By_Length(1) *)
       else
	 Subs_Subset
	   
	   (* Subs_Subset*)  (*(Subs_By_Length(1)) *) (* Subs_Full *)
     else
       (* Subs_Full*)  Subs_By_Length(20) (* Subs_Subset *)(* (Subs_By_Length(2)) *) (* (Subs_Full) *)
     );

     lcl_bwd_subs_res =  (* Subs_Subset; *) (* Subs_Full;*)
     (if  (is_ver_epr ())
     then
       if (num_of_input_clauses < 100000 (* 100000*))
       then
	 Subs_By_Length(1)
       else
	 Subs_Subset
	   
	   (* Subs_Subset*) (*  (Subs_By_Length(1)) *)(* Subs_Full *)
     else
       (* Subs_Full *)  (Subs_By_Length(20))  (* Subs_Subset *)(* (Subs_By_Length(2))*) (* (Subs_Full) *)
     );

     
(* sim global *)

     glb_add_to_sub_index_test = 
     (fun c ->
       ((Clause.num_of_var c) <= 20)  && ((Clause.num_of_symb c) <= 1000));
     
     glb_fwd_subs = (* true;*)
     (if (is_ver_epr ())
     then
       if (num_of_input_clauses < 100000 (*200000 *))
       then
	 true
       else
	 false
     else
       true  (* false *)
     );
     
     glb_fwd_subs_res = (* false; *)
     (if (is_ver_epr ())
     then
       if (num_of_input_clauses < 100000 (* 100000 *) )
       then
	 true
       else
	 false
     else
       true  (* false; *) 
     );

     glb_bwd_subs     = (* Subs_Full; *)
     (if (is_ver_epr ())
     then
       if (num_of_input_clauses < 100000 (*200000*))
       then
	 Subs_By_Length(1)
       else
	 Subs_Subset (*  Subs_By_Length(1) *)  (*Subs_Full*)
     else
       (* Subs_Full; *) (* Subs_Subset *)   Subs_By_Length(10);   (* Subs_By_Length(2); *)
     );
     
     glb_bwd_subs_res = (* Subs_Subset; *)(* Subs_Full;*)
     (if (is_ver_epr ())
     then
       if (num_of_input_clauses < 100000 (* 200000 *))
       then
	 Subs_By_Length(1)
       else
	 Subs_Subset (* Subs_By_Length(1) *)(* Subs_Full*)
     else
       (* Subs_Full; *) (* Subs_Subset *)  Subs_By_Length(10);  (* Subs_By_Length(2); *) (*Subs_Full; *)
     );

   }
  in
  (*let fixed_point_reached = ref false in*)
  (* out_str (Clause.clause_list_to_string !current_list); *)

  let new_clauses = PredElim.predicate_elimination pred_elim_options (Clause.CL_List (clause_list)) in
  new_clauses

(*--------------- bc_imp_inh cone --------------------------*)

let bc_imp_inh_cone clause_list = 
  dbg_env D_cone_symb
    (fun () ->
      
      let is_relevant_symb symb = 
	(not (symb == Symbol.symb_ver_next_state)) 	  
      in    
      dbg D_cone_symb (lazy ("start full_rel: init clauses: "^(string_of_int (List.length clause_list))^"\n"));
      let start_time = Unix.gettimeofday () in
      let full_rel = Cone_symb.create_full_rel_cl_list ~is_relevant_symb clause_list in 
      let end_time = Unix.gettimeofday () in
      dbg D_cone_symb (lazy ("end full_rel: time "^((string_of_float (end_time -. start_time)))));
      
      let depth_0_symb_set = SSet.of_list [Symbol.symb_ver_property] in
      dbg D_cone_symb (lazy ("start compute cone: "));
      let start_time = Unix.gettimeofday () in
      let cone = Cone_symb.compute_cone full_rel ~terminating_symb_set:SSet.empty ~depth_0_symb_set in 
      let end_time = Unix.gettimeofday () in
      let depth =  (* 4*)  -1  in (* all reach clauses *) 
      let cone_clauses = CSet.elements (Cone_symb.get_cone_clauses cone ~depth) in 
      dbg D_cone_symb (lazy ("end compute cone: size "^(string_of_int (List.length cone_clauses))
			     ^" time "^((string_of_float (end_time -. start_time)))));
      Cone_symb.out_cone ~symbs:false  ~clauses:false ~stats:true cone;

      out_warning ("preprocess cone-reduced clause set restricted to depth "^(string_of_int depth)^"\n\n ");
      (* current_list:= cone_clauses; *) (* experiment with cone reductions; single reduction is incomplete  *)
      
    );
(*--------- cone bc_imp_inh ---------*)
  (
   if (bc_imp_inh_exists !current_options BCI_conj_cone) 
   then
     (* TODO move non-prolific *)
     
     let symb_fill_num_of_occ_clause occ_smap cl = 
       let f (curr_occ_smap, counted_sset) symb =  (* each symb is counted only once per cluase*)
	 if (not (SSet.mem symb counted_sset))
	 then 
	   try 
	     let old_num_occ = SMap.find symb curr_occ_smap in 
	     let new_smap = SMap.add symb (old_num_occ+1) curr_occ_smap in 
	     let new_counted_sset = SSet.add symb counted_sset in 
	     (new_smap, new_counted_sset)
	   with 
	     Not_found ->
	       (SMap.add symb 1 curr_occ_smap, SSet.add symb counted_sset)
	 else
	   (curr_occ_smap, counted_sset) 
       in
       let (fill_occ_smap,_counted) =  Clause.fold_sym f (occ_smap,SSet.empty) cl in 
       fill_occ_smap
     in
     let symb_num_of_occ_map = List.fold_left symb_fill_num_of_occ_clause SMap.empty clause_list in

     (* get into list and order by priority *)
     dbg_env D_cone_symb 
       (fun () ->
	 let symb_num_occ_list =
	   SMap.fold (fun symb n rest -> ((symb, n):: rest)) symb_num_of_occ_map []
	 in
	 let sorted_num_occ_list =
	   List.sort (fun (_, d1) (_, d2) -> compare d1 d2) symb_num_occ_list 
	 in	
	 out_str ("num occ symbols: "^(string_of_int (List.length sorted_num_occ_list))^"\n\n");
	 dbg_env D_cone_symb_full 
	   (fun () ->
	     List.iter
	       (fun (symb, depth) ->
		 out_str ((Symbol.to_string symb)^": "^(string_of_int depth)))
	       sorted_num_occ_list
	   )
       );

(*
  let prolific_frac = 0.1 in 

  let num_of_clauses = List.length !current_list in 
  let prolific_bound =  (int_of_float (prolific_frac *. (float_of_int num_of_clauses))) in
  let is_prolific symb = 
  try 
  let num_of_occ = SMap.find symb symb_num_of_occ_map in	 
  dbg_env D_cone_symb 
  (fun () -> 
  if  prolific_bound <= num_of_occ	
  then
  dbg D_cone_symb (lazy ("prolific symb: "^(Symbol.to_string symb)^" num occ: "^(string_of_int num_of_occ)^"\n"))
  );

  prolific_bound <= num_of_occ	  
  with
  Not_found -> false
  in

  
  
  let is_relevant_symb symb = 
  (((not (is_special_symbol symb)) && (not (is_prolific symb)))
  || (symb == Symbol.symb_ver_property)) in    
 *)

     let pred_symb_only = false in (* false: all symbols not just predicates for general problems; for bmc1 ok true *)

     let tolerance = !current_options.conj_cone_tolerance in

     let is_relevant_symb symb = 
       ((not (Symbol.is_special_symb symb))
      || (symb == Symbol.symb_ver_property)) 
     in  
     
     dbg D_cone_symb (lazy
			("start full_rel: init clauses: "
			 ^(string_of_int (List.length clause_list))^"\n"));

     let start_time = Unix.gettimeofday () in
     let full_rel = Cone_symb.create_full_rel_cl_list ~tolerance ~symb_num_of_occ_map ~is_relevant_symb ~pred_symb_only  clause_list in 
     let end_time = Unix.gettimeofday () in
     dbg D_cone_symb (lazy ("end full_rel: time "^((string_of_float (end_time -. start_time)))));    

(* get conjecture relevant symbols *)
     let get_clause_rel_symbs clause = 
       if pred_symb_only
       then
	 Clause.find_all_pred ~is_relevant_pred:(fun _sign symb -> is_relevant_symb symb) clause 
       else
	 Clause.find_all_sym ~is_relevant_symb clause 
     in 

     let get_conj_cl_rel_symbs sset clause = 
       SSet.union (get_clause_rel_symbs clause) sset
     in
     let conj_preds = List.fold_left get_conj_cl_rel_symbs SSet.empty !(Parser_types.neg_conjectures) in
     
(*    let depth_0_symb_set = SSet.of_list [Symbol.symb_ver_property] in *)
     let depth_0_symb_set = SSet.add Symbol.symb_ver_property conj_preds in 
     dbg D_cone_symb (lazy ("start compute cone: "));
     let start_time = Unix.gettimeofday () in
     let cone = Cone_symb.compute_cone full_rel ~terminating_symb_set:SSet.empty ~depth_0_symb_set in 
     let end_time = Unix.gettimeofday () in
     dbg D_cone_symb (lazy ("end compute cone: time "^((string_of_float (end_time -. start_time)))));

     dbg_env D_cone_symb
       (fun () -> Cone_symb.out_cone ~symbs:false ~clauses:false ~stats:true cone;);
     
     dbg_env D_cone_symb_full 
       (fun () -> Cone_symb.out_cone ~symbs:true  ~clauses:true ~stats:true cone;);
     
(* asssign bc_imp_inh to clauses based on depth *)
     let bc_imp_inh_shift = get_bc_imp_inh_shift !current_options BCI_conj_cone in
(*    dbg D_cone (lazy (("bc_imp_inh_shift: ")^(string_of_int bc_imp_inh_shift )^"\n")); *)
     let symb_depth_map = Cone_symb.get_cone_symb_depth_map cone in
     let get_symb_depth symb =        
       try
	 SMap.find symb symb_depth_map
       with 
	 Not_found -> max_int 
     in
     let symb_to_clauses_full_rel = Cone_symb.get_symb_to_clauses full_rel in
     let is_trigger symb clause =
       try
	 let cset = SMap.find symb symb_to_clauses_full_rel in 
	 CSet.mem clause cset
       with
	 Not_found -> false
     in
     
     let get_min_symb_depth clause = 
       let f curr_min symb =
	 if (is_trigger symb clause)
	 then
	   let symb_depth = get_symb_depth symb in
	   if curr_min < symb_depth 
	   then 
	     curr_min
	   else
	     symb_depth
	 else
	   curr_min
       in
       Clause.fold_sym f max_int clause
     in
     let assign_bc_imp_inh clause = (* min depth of its preds *)
       let cl_depth = get_min_symb_depth clause in 
       if cl_depth = max_int 
       then ()
       else 
	 (
	  let c_importance = (cl_depth + bc_imp_inh_shift) in 
	  dbg D_cone_symb_full (lazy ((Clause.to_string clause)^" cl_depth: "^(string_of_int cl_depth)^"\n"));
	  Clause.assign_bc_imp_inh clause c_importance;
	 )
     in
     let depth = -1 in
     let cone_clauses = (Cone_symb.get_cone_clauses cone ~depth) in
     CSet.iter assign_bc_imp_inh cone_clauses 
(* note we do not assign cone clauses to current_list but just changing the priority of them *)
   else  
     (dbg D_cone_symb (lazy (" BCI_conj_cone is not in the !current_options \n"));)
  )
    

(*----------------------- get prep options ---------------*)

(* based on current options and modifications related to preprocessing *)

let prep_options problem_properties = 

(* Schedule_default: preprocessing options are modified based on property options *)
(* TODO: fix preprocessing for other schedules options *)

  let out_named_opts named_opts =
    out_str ((s_pref_str ())^" preprocesses with "^named_opts.options_name);      
    named_opts.Options.options
  in 
  let options_init =
    match !current_options.schedule with  
    |Schedule_default | Schedule_sat
      ->
        
        if (is_epr problem_properties) && 
            (not (is_horn problem_properties)) &&  
            (has_eq problem_properties)
        then 
          ( 
            out_named_opts (Options.named_option_epr_non_horn_eq ())
           )
        else
          if (is_epr problem_properties) && 
            (is_horn problem_properties) &&  (not (has_eq problem_properties))
          then
            (
              out_named_opts (Options.named_option_epr_horn_non_eq ())
            )
          else
            if (is_epr problem_properties) && 
              (not (is_horn problem_properties)) &&  
              (not (has_eq problem_properties))
            then 
              (
               out_named_opts (Options.named_option_epr_non_horn_non_eq ())
              )
            else
            (!current_options)

    | Schedule_smac_tmp -> 
        out_named_opts (Options.named_option_smac_tmp ())

    |_ ->
      (!current_options)
        
  in
  let opts_ver_modif = 
    (* TODO: to implement preprocessing for AIG/verification *)
    (if (!current_options.schedule != Schedule_smac_tmp) && (is_ver_epr ())
    then
      (
       let ver_options = 
         {options_init with          
	  prep_gs_sim = false;
	  res_sim_input = false;
	  prep_res_sim = false;
          
          (* symbol_type_check = !current_options.symbol_type_check; *)
	  symbol_type_check = false;
(*	  prep_sem_filter = Sem_Filter_None; *)

	  (* uncomment the following line to improve output for the DEMO *)
	  (* inst_out_proof = ValueCmd false; *)
	} in
       out_str ((s_pref_str ())^" preprocess verification option modifier ");
       ver_options;
      )
    else
      options_init
    ) 
  in
  let opts_prep = opts_ver_modif in 
  opts_prep

(*-------------------------*)
let non_eq_to_eq clause_list = 
  if !current_options.non_eq_to_eq 
  then 
     (
      let pred_to_fun_htbl = PredToFun.create (SymbolDB.size !symbol_db_ref) in      
      (List.map (pred_to_fun_clause pred_to_fun_htbl) clause_list)
     )
  else clause_list 

(*-------------------------------------------*)
let set_reduce clause_list =  BCSet.elements (BCSet.of_list clause_list)

let apply_to_clauses f prep_state = prep_state.prep_clauses <- f prep_state.prep_clauses

(* TODO split to frist; repeat last *)
let prep_fun_list ~before_eq_axioms problem_prop = 
  let o = !current_options in
  let a = apply_to_clauses in
  let pp_ref = ref problem_prop in
  let id _ = () in  
   [
    if ((is_epr !pp_ref) && (has_eq !pp_ref) && (not (is_ver_epr ()))) then (a elim_const_domain_tautologies) else id;
    if o.pure_diseq_elim then (a Eq_axioms.pure_dis_eq_elim) else id; 
    if o.prep_upred then (a Prep_unary_pred.prep_unary_pred) else id; (* for some problems performance worse; evaluate *)


    prep_solver_run;   (* do only once at the beginning *)

    (a (sim_self_clauses ~before_eq_axioms)); 

    (a set_reduce); 

(* splitting  (just for  experiment) *)
(*    (a (Splitting.splitting Definitions.def_env_glb ~out_progress:true));  *)

    prep_solver_run;  

    if (o.prep_def_merge (* && before_eq_axioms *)) then (a Bin_hyper_res.def_merge) else id; (* in some cases definitions appear after adding eq axioms so we do merge after adding axioms as well *)


    if o.prep_res_sim then (a res_preprocess) else id; 
    
(* TODO: clean *)

    (if (o.prep_sem_filter != Sem_Filter_None) 
    then 
      (fun prep_state ->  
        let new_prob_prop = get_prob_props prep_state.prep_clauses in 

(* TODO clean *)        
(* we need to recopute eq side clauses: due to unflattening some previously ommitted congr axioms in --eq_ax_congr_red, can be needed *)
        (if ((has_eq new_prob_prop) && before_eq_axioms (* && (not prep_state.prep_side_includes_eq)*))
        then
          (           
                      prep_state.prep_side_clauses <- 
                        CSet.elements (CSet.of_list ((Eq_axioms.eq_axiom_list prep_state.prep_clauses)@prep_state.prep_side_clauses));
                      prep_state.prep_side_includes_eq <- true;
                     )
        );

(*        if (not new_prob_prop.has_eq) || (new_prob_prop.has_eq && (not before_eq_axioms)) *)
(*        then *)
          (prep_sem_filter prep_state)
(*        else
          (
         
          )
*)
      )
    else 
      id 
    );

(*    if (o.prep_sem_filter != Sem_Filter_None) then prep_sem_filter else id; *)

(*    if o.pred_elim then (a (prep_pred_elim !pp_ref)) else id;  *)

    if (o.pred_elim && before_eq_axioms)
         (* can not use pred_elim after eq axioms since lifted resolution uses flattening/unflattening which implicitely           can eliminate congrunence axioms *)
    then 
      (fun prep_state ->  
        prep_state.prep_clauses <- 
          (prep_pred_elim (get_prob_props prep_state.prep_clauses) prep_state.prep_clauses ~side_preds:(get_side_preds prep_state)))
    else 
      (
    (* set reduce; useful for Bin_hyper_res.def_merge  *)
       a (fun cl_list -> BCSet.elements (BCSet.of_list cl_list));       
      );
    
  ]


let reuse_old_clauses ~old_cl_list ~new_cl_list = 
  let old_cl_set = BCSet.of_list old_cl_list in 
  let new_cl_set = BCSet.of_list new_cl_list in
  let f new_cl rest_list = 
    try 
      (BCSet.find new_cl old_cl_set)::rest_list 
    with 
      Not_found -> 
        new_cl::rest_list
  in
  BCSet.fold f new_cl_set []

 
(*-------------- preprocess_sim simplifying preprocessing ------------------*)    

let preprocess_sim ~before_eq_axioms prep_state =   
  out_str "\n";

  print_string ((s_pref_str ())^"Preprocessing...");
  flush stdout;
  
  let clauses_before_prep = prep_state.prep_clauses in
  
  let start_time = Unix.gettimeofday () in 
  let prep_running_time () = (Unix.gettimeofday ()) -. start_time in

  let problem_prop_ref = ref (get_prob_props prep_state.prep_clauses) in     

  let current_options_before_prep = !current_options in 
  current_options := prep_options !problem_prop_ref;
  
  dbg D_trace (lazy " \n");

  prep_solver_run prep_state; (* do only once *)
  
  let fixed_point_reached = ref false in

  let cycle_num = ref 1 in
  
  let time_limit = prep_time_limit () in
  dbg D_time (lazy (
               "iprover running time: "^(string_of_float (iprover_running_time ()))
               ^" prep time limit:"^(string_of_float time_limit)));

  let time_out_reached () = 
    (time_limit >=0. && ((prep_running_time ()) > time_limit))
  in 
  while (not !fixed_point_reached &&  (not (time_out_reached ())))
  do
    dbg D_trace (lazy (" start new cycle: "^(string_of_int !cycle_num)));
    Statistics.incr_int_stat 1 Statistics.prep_cycles;

    let num_of_clauses_before = List.length prep_state.prep_clauses in 
    dbg D_trace (lazy ("num_of_clauses_before: "^(string_of_int num_of_clauses_before)));
    let dbg_clause_set_before = ref BCSet.empty in    
    dbg_env D_rm_added (fun () -> dbg_clause_set_before := BCSet.of_list prep_state.prep_clauses);

   
    iter_fun_list (prep_fun_list ~before_eq_axioms !problem_prop_ref) prep_state;    


    let num_of_clauses_after = List.length prep_state.prep_clauses in    
    dbg D_trace (lazy ("num_of_clauses_after: "^(string_of_int num_of_clauses_after)));
    let dbg_clause_set_after = ref BCSet.empty in    
    dbg_env D_rm_added (fun () -> dbg_clause_set_after := BCSet.of_list prep_state.prep_clauses);
    dbg_env D_rm_added
      (fun () ->      
        let removed_clauses = BCSet.diff !dbg_clause_set_before !dbg_clause_set_after in
        let added_clauses = BCSet.diff !dbg_clause_set_after !dbg_clause_set_before in
        dbg D_rm_added (lazy ("--------------- removed clauses: "));
        dbg D_rm_added (lazy (Clause.clause_list_to_string (BCSet.elements removed_clauses)));
        dbg D_rm_added (lazy ("--------------- removed clauses end "));
        dbg D_rm_added (lazy ("--------------- added clauses: "));
        dbg D_rm_added (lazy (Clause.clause_list_to_string (BCSet.elements added_clauses)));
        dbg D_rm_added (lazy ("--------------- added clauses end "));        
      );


    (if (num_of_clauses_before <= num_of_clauses_after) 
    then 
      (
       dbg D_trace (lazy ("prep cycle fixed point reached"));
       fixed_point_reached:= true; (* exit from the loop *)
      )
    else
      (
       problem_prop_ref:= get_prob_props prep_state.prep_clauses
      )
    );
    cycle_num := !cycle_num + 1;
  done;
  
(* prep should not include sub-typting; apply subtypting after perp. *)
 prep_state.prep_clauses <- reuse_old_clauses ~old_cl_list:clauses_before_prep ~new_cl_list:prep_state.prep_clauses; 

(* restore options before preprocessing *)
  current_options := current_options_before_prep;

  let out_stats_after_prep () = 
     out_str (pref_str^" Statistics after preprocessing: \n");
     let problem_properties = (Problem_properties.get_prob_props prep_state.prep_clauses) in 
     Problem_properties.prob_props_to_statistics problem_properties;      
     out_stat();      
  in
  (if !current_options.preprocessed_stats
  then
    (
     out_str "\n";
     out_str ((s_pref_str ())^"Exiting after preprocessing");
     out_str (szs_unknown_str);
     out_stats_after_prep ();
     exit(0);
    )
  else
    if !current_options.preprocessed_out 
    then
      (
       out_str "\n";
       out_str ((s_pref_str ())^"Exiting after preprocessing");
       out_str (pref_str^" Preprocessed clauses: \n");
       Clause.out_clause_list_tptp prep_state.prep_clauses;
       out_str "\n";
     
       out_str (szs_unknown_str);
       out_stats_after_prep ();         
       exit(0);
      ) 
    else
      (
         (* continue with prep state *)
      )

  )


let retype_impl_units () =
  Prop_solver_exchange.apply_prop_lit_to_fof (fun fof_lit -> add_term_db (Parser_types.retype_lit fof_lit))

 
(*------------- preprocessing transformations: splitting, typing etc. ---------------*)

let prep_fun_list_trans () = 
  let o = !current_options in
  let a = apply_to_clauses in
  let id _ = () in  
  [

(* TODO: include ver with side clauses/literals *)
   if o.sub_typing && (not (is_ver_epr ())) 
   then
     (
      
      fun prep_state ->
        (
       (* we need to unflatten x!= y before subtyping *)
       (* if it was on in the options unflattening was applied above *)
  
         (a Inference_rules.unflatten prep_state); 
         (a Type_inf.sub_type_inf prep_state);
         (Prop_solver_exchange.init_gr_by ());
         (retype_impl_units ());
         Clause.assign_is_essential_input_symb (Clause.CL_List prep_state.prep_clauses);        

         dbg D_sub_typing (lazy "-----------After Subtyping:---------");	
         dbg D_sub_typing (lazy (Clause.clause_list_to_tptp prep_state.prep_clauses));	
         dbg D_sub_typing (lazy "------------------------------------");                           
        )
     )
   else 
     id;
   
   (a (fun x -> bc_imp_inh_cone x; x)); (* need to return clauses rather than unit *)
   (a (Splitting.splitting Definitions.def_env_glb ~out_progress:true));
   if o.non_eq_to_eq then (a non_eq_to_eq) else id;
 ]

(* transformations like spliting, typing etc. *)
let preprocess_trans prep_state  = 
  out_str "\n";
  print_string ((s_pref_str ())^"Preprocessing...");
  flush stdout;

  let current_options_before_prep = !current_options in 
  current_options := prep_options (get_prob_props prep_state.prep_clauses);

(*--------- splitting etc. ---------*)
  iter_fun_list (prep_fun_list_trans ()) prep_state;
  current_options := current_options_before_prep
  

 
(*------------- OLD ------------------*)
(*    
let preprocess clause_list =
  
  let current_list = ref clause_list in

  print_string ((s_pref_str ())^"Preprocessing...");
  flush stdout;

  let problem_properties_before_prep = get_problem_props clause_list in 

  dbg D_trace (lazy ("problem_properties_before_prep: "^(problem_props_to_string problem_properties_before_prep)^"\n"));

  let before_prep_current_options = !current_options in 
  current_options := prep_options problem_properties_before_prep;

  (if problem_properties_before_prep.epr && problem_properties_before_prep.has_eq
  then  
    current_list := elim_const_domain_tautologies !current_list
  else
    ()
  );

  
  (* TODO: to implement preprocessing for AIG/verification *)
  
  (if !current_options.prep_upred 
  then 
    current_list := 
      Prep_unary_pred.prep_unary_pred !current_list;
  );

(*  splitting_nvd ();*)

  
  (if !current_options.non_eq_to_eq 
  then 
    (
     let pred_to_fun_htbl = PredToFun.create (SymbolDB.size !symbol_db_ref) in
     current_list := 
       (List.map (pred_to_fun_clause pred_to_fun_htbl) !current_list)
    )
  else ()
  ); 

  let sim_self_fun_list = get_sim_self_fun_list () in
  let simpl_sim rest c = 
    try
      let new_c = fold_left_fun_list sim_self_fun_list c in   
      new_c::rest
    with 
      Eliminated -> 
	rest
  in 
  current_list := List.fold_left simpl_sim [] !current_list;
  
(*
  (if  !current_options.prep_gs_sim 
  then 
  current_list := prop_simp !current_list
  else ());
 *)
(*  current_list := List.map unflatten !current_list;  
    out_str (" \n after unflat: \n"^(Clause.clause_list_to_string !current_list));
 *)
  
  (if !current_options.prep_res_sim 
  then
    current_list := res_preprocess !current_list
  else ()
  );

  (if !current_options.pred_elim 
  then
    (
     current_list:= prep_pred_elim problem_properties_before_prep !current_list;  
    )
  );
(*
  while (not !fixed_point_reached)
  do
(* optimisation for runs after first: make a flag whether pred_clauses got modified;*)
(* if  at the moment of elimination of a pred its pred_clauses was not modified we can immediatly abort this elimination *)
(* also the same pe_state can be used just need to reset the elimination queue *)

  let new_clauses = PredElim.predicate_elimination pred_elim_options (Cl_List (!current_list)) in
  Statistics.incr_int_stat 1 Statistics.pred_elim_cycles;
  let reduction = (List.length !current_list) - (List.length new_clauses)  in
  out_dbg ~g:1 (lazy ("------------------"));
  out_dbg ~g:1 (lazy ("has_eq: "^(string_of_bool pred_elim_options.pe_has_eq)));
  out_dbg ~g:1 (lazy ("before predelim: "^(string_of_int (List.length !current_list))));
  out_dbg ~g:1 (lazy (Clause.clause_list_to_string !current_list));
  out_dbg ~g:2 (lazy ("after predelim: "^(string_of_int (List.length new_clauses))
  ^" reduction: "^(string_of_int reduction)));
  out_dbg ~g:2 (lazy  (Clause.clause_list_to_string new_clauses));      
  out_dbg ~g:2 (lazy ("------------------"));
  fixed_point_reached:= reduction = 0;
  current_list:= new_clauses;
  done     
 *)

  
  dbg_env D_out_prep_clauses
    (
     fun () -> (
       let clause_list = !current_list in
       let (epr, non_epr) = List.partition Clause.is_epr clause_list in
       out_str ("% "^pref_str^"Clauses after preprocessing: "^(string_of_int (List.length clause_list))^"\n\n");
       out_str ("% "^pref_str^"EPR clauses: "^(string_of_int (List.length epr))^"\n\n");
       Clause.out_clause_list_tptp epr;
       out_str ("\n\n"^"% "^pref_str^"non-EPR clauses:"^(string_of_int (List.length non_epr))^" \n\n");
       Clause.out_clause_list_tptp non_epr;
       out_str "\n\n";
      )
    );


(*
(*--------- resets solver --------*)
  (
  if (!current_options.reset_solvers)
  then
  (
  dbg D_solver (lazy "start: reset");
  
  Prop_solver_exchange.reset_solvers (); 
  
  dbg D_solver (lazy "end: reset");

  dbg D_solver (lazy "start: add clauses");
  let start_time = Unix.gettimeofday () in
  
  List.iter 
  Prop_solver_exchange.add_clause_to_solver !current_list;
  
  let end_time = Unix.gettimeofday () in
  dbg D_solver (lazy ("end: add clauses: "^(string_of_float (end_time -. start_time))^"\n"));
  )
  else
  ()
  );
 *)
(*  
    dbg_env D_marshal
    (fun () ->
    dbg D_marshal (lazy ("start: Marshal clauses\n"));
    let start_time = Unix.gettimeofday () in
    let bytes = Marshal.to_bytes !current_list [] in
    let end_time = Unix.gettimeofday () in
    dbg D_marshal (lazy ("end: Byte length"^(string_of_int (Bytes.length bytes))
    ^" time: "^((string_of_float (end_time -. start_time)))
    ^"\n"))
    );
 *)

(*-----------------*)
  bc_imp_inh_cone !current_list;

(*-----------------*)
  current_list := Splitting.splitting Definitions.def_env_glb ~out_progress:true !current_list;

(*-----------------*)
  out_str "\n";

  dbg_env D_proof
    (fun () -> 
      let out_test c = not (Clause.is_ground c) in
      let f clause = 
        if (out_test clause)
        then 
          (
           dbg D_proof (lazy ("----------- Proof of -----------"));
           Format.printf "Clause: \n @[%a @]@."
             (Clause.pp_clause_with_source ~global_subsumption_justification_fun:None ~clausify_proof:true
             ) clause;       
           dbg D_proof (lazy ("--------------------------------"));

           let g parent_clause = 
             Format.printf "Clause: \n @[%a @]@."
               (Clause.pp_clause_with_source ~global_subsumption_justification_fun:None ~clausify_proof:true) parent_clause
           in  
           
           List.iter g (TstpProof.get_parents [clause]);
(*          out_str (Clause.clause_list_to_tptp (TstpProof.get_parents [clause])); *)

(*            
              Format.printf "Clause: \n @[%a @]@."
              (TstpProof.get_parents ~clausify_proof: true ) clause;
 *)
          )
        else
          ()
      in
      List.iter f !current_list;
    );

  (
   if !current_options.non_eq_to_eq 
   then 
     (
      let pred_to_fun_htbl = PredToFun.create (SymbolDB.size !symbol_db_ref) in
      current_list := 
        (List.map (pred_to_fun_clause pred_to_fun_htbl) !current_list)
     )
   else ()
  );

  (if !current_options.preprocessed_out 
  then
    (
     out_str (pref_str^" Preprocessed clauses: \n");
     Clause.out_clause_list_tptp !current_list;
     out_str "\n";
     exit(0);
    ) 
  else
    (
(* restore options before preprocessing *)
     current_options := before_prep_current_options;
     !current_list)
  )
    
*)
