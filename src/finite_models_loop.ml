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
open Finite_models

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_input
  | D_axs_eq
  | D_axs_domain
  | D_axs_diseq
  | D_flattening
  | D_unsat_core
  | D_lemmas 
  | D_preprocess

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_input -> "input"
  | D_axs_eq -> "axs_eq"
  | D_axs_domain -> "axs_domain"
  | D_axs_diseq -> "axs_diseq"
  | D_flattening -> "flattening"
  | D_unsat_core -> "unsat_core"
  | D_lemmas -> "lemmas"
  | D_preprocess -> "preprocess"

let dbg_groups =
  [
   D_trace;  
   D_axs_eq; 
   D_axs_domain; 
   D_axs_diseq;  
   D_flattening; 

   D_input;

   D_unsat_core;
   D_lemmas;

   D_preprocess; 
 ]
    
let module_name = "finite_models_loop"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(*---------------Finite Models-------------------------------*)

(* if there is no equality then we start with a model with the size = *)
(* to the number of constants, we aslo do not add disequalities and *)
(* use unit domain axioms *)
(* change relative to current clause set*)

let get_num_of_input_constants () =
  let f s i =
    (* is_constant can be true on types *)
    if (Symbol.is_constant s) && (Symbol.get_num_input_occur s) >0
    then
      i +1
    else i
  in
  SymbolDB.fold f !symbol_db_ref 0

(*TODO: change relative to current clause set; number of constants of specific types  !!!!!!*)


let no_input_eq () =
  false
(*  (Symbol.get_num_input_occur Symbol.symb_equality) = 0 *)


exception Skip_bound

(* can raise Unsatisfiable_gr_na *)
(*-------------------------------------------------------*)
let finite_models_loop input_clauses =

  !current_options.resolution_flag <- false;
  let model_bound = 1000 in
  out_str (pref_str^"Finite Models:\n");

(* do nvd split of the axioms *)

  (*--------- TODO -------*)
  let skip_until_bound = ref 0 in
  (if !skip_until_bound != 0 
  then 
    (
     out_str ("\n");
     out_warning ("fm_loop skip_until_bound"^(string_of_int !skip_until_bound)); 
     out_str ("\n");
    )
  );


(* TODO: experiment with preprocessing *)

(*
  let prep_clauses =   input_clauses in
*)

(*  out_warning "finite_models_loop.ml: preprocess swtiched off: properly treat eqaulity 1"; *)
(*
  let prep_clauses =  
(*  List.rev *)  (Preprocess.preprocess (* ~is_eq_problem:(Problem_properties.has_equality input_clauses) *)  input_clauses) in 
*)

  let prep_clauses = input_clauses in

  dbg D_input (lazy 
		 (
		  ("\n\n"^pref_str^"Finite Model input clauses:\n")
		  ^
		    (Clause.clause_list_to_tptp prep_clauses)^"\n\n"));
   
  
  (*  Finite_models.flat_signature ();*)
  
  let fm_state = Finite_models.init_fm_state prep_clauses in
  let flat_clauses = Finite_models.get_flat_clauses fm_state in
(* changes to flat_clauses should be propagated to fm_state or done in finite_model.ml *)

  let eq_axioms =
    if (!current_options.sat_epr_types) || (!current_options.sat_non_cyclic_types)
    then
      (Finite_models.get_non_flat_eq_axioms fm_state)
    else
      []
  in
 
  dbg D_axs_eq (lazy
		  ("\n---------Eq Axioms------------------\n"
		   ^(Clause.clause_list_to_tptp eq_axioms)
		   ^"\n------------------------\n"));
 
  dbg D_flattening (lazy
		      ("\n---------Flat clauses------------------\n"
		       ^(Clause.clause_list_to_tptp flat_clauses)
		       ^"\n------------------------\n"));
  
  let init_clauses =
    eq_axioms@flat_clauses
  in
  
  out_str (pref_str^"lit_activity_flag true\n");
  (*  Prop_solver_exchange.set_lit_activity_flag false;*)
  List.iter
    Prop_solver_exchange.add_clause_to_solver init_clauses;

  Prop_solver_exchange.clear_soft_assumptions ();
  (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
  then
    (* Raise separate exception, solver is not in an invalid state
       and can be satisfiable without assumptions *)
    (* raise PropSolver.Unsatisfiable *)
    raise Unsatisfiable_gr_na
  );
  (*  let dom_const_list = ref [] in*)

(*
  let bound_preds = ref [] in
  
  let model_size = ref
      (if no_input_eq ()
      then
	(out_str (pref_str^"No Equality\n");
	 let num_const = get_num_of_input_constants () in
	 if num_const > 0
	 then num_const
	 else 1
	)
	  (* there is equality we start with the size 1 *)
      else 1
      )
  in
  
  (* let model_size = ref 5 in
     out_str (pref_str^"Overwritting the model size to:"
     ^(string_of_int !model_size)^"\n");
   *)
  for i = 1 to !model_size
  do
    
    Finite_models.add_domain_constant_all_dom i
      (* in  dom_const_list := (!dom_const_list)@[new_dom_const]*)
  done;

*)

(* adjust options; TODO: move this later *)

  (if !current_options.sat_fm_lemmas
  then
    begin
      !current_options.pred_elim <- false; 
      !current_options.res_sim_input <- false;
      !current_options.prep_res_sim <- false;
      !current_options.inst_prop_sim_given <- false; 
      !current_options.inst_prop_sim_new <- false;
      !current_options.inst_start_prop_sim_after_learn <- 10000;
    end
  else()
  );

  let model_size = ref (get_domain_size (get_domain fm_state)) in

  if !model_size = 0 
  then (* there are no types that need to be extended (all types non-flattend) *)
    (
     let current_clauses = ref init_clauses in

     if (!current_options.abstr_ref = []) 
     then 
       (Proof_search_loop.ps_full_loop ~time_limit:Undef !current_clauses;)
     else
      (Abstr_ref_process.ar_loop
        ~time_limit:Undef !current_options.abstr_ref !current_clauses;)
       (* (Axiom_selection.axiom_selection_loop 
        *    ~time_limit:Undef !current_options.abstr_ref !current_clauses;) *)
(*
     if !current_options.abstr_ref_arg_filter
     then
       (Abstr_ref_arg_filter.abstr_ref_gr_filter_loop ~time_limit:Undef !current_clauses;)
     else  
       (Proof_search_loop.ps_full_loop ~time_limit:Undef !current_clauses;)
*)
    )
  else
    begin
(*--------------main loop ------------------*)
  while !model_size < model_bound
  do
    try
      assert (Prop_solver_exchange.soft_assumptions_is_empty ());
      out_str "";
      out_str (pref_str^"Trying domains of size >= : "
	       ^(string_of_int !model_size));

      
      (* let new_bound_pred = Finite_models.create_bound_pred !model_size in *)
      
      let active_range_axioms = (get_active_range_axioms (get_domain fm_state)) in (* TODO triangular *)
      
      dbg D_axs_domain (lazy 	
			("\n--------- Active range axioms------------------\n"
			 ^(Clause.clause_list_to_tptp active_range_axioms)
			 ^"\n------------------------\n"));
       

      (* diseq axioms only added for equational types *)
      let dis_eq_axioms =  get_diseq_axioms (get_domain fm_state) in

      dbg D_axs_diseq (lazy 
			 ("\n---------Diseq Axioms------------------\n"
			  ^(Clause.clause_list_to_tptp dis_eq_axioms)
			  ^"\n------------------------\n"));
      
      (*
	let domain_axioms =
	if no_input_eq ()
	then
	Finite_models.domain_axioms_unit new_dom_pred !dom_const_list
	else
	Finite_models.domain_axioms_triangular new_dom_pred !dom_const_list
       *)
      
      let axioms = active_range_axioms@dis_eq_axioms in

      let lemmas_all = get_lemmas fm_state in 

      let lemma_size_bound = 16 in      

      let lemmas_small = List.filter (fun c -> (Clause.length c) <= lemma_size_bound) lemmas_all in 
      
     (* out_str ("lemma size bound: "^(string_of_int lemma_size_bound)); *)

      dbg D_lemmas (lazy "\n\n ---------- Lemmas -------- \n\n");
      dbg D_lemmas (lazy (Clause.clause_list_to_string lemmas_small));

(*      out_warning (" finite models lemmas are switched off ");*)


      let clauses_before_prep = (lemmas_small@axioms@init_clauses) in

      (*
      let all_clauses = 
	if !current_options.sat_fm_prep 
	then 
	  begin
	    dbg D_preprocess (lazy 
				("\n\n ------- Before Preprocessing ------- \n\n"
				 ^(Clause.clause_list_to_string clauses_before_prep)));
	    
	    
	    
	    Prop_solver_exchange.assign_solver_assumptions [];
	    Prop_solver_exchange.assign_sim_adjoint_lits [];

      (* adjust prep options *)
	    !current_options.prep_res_sim <- false; 
	    !current_options.prep_unflatten <- false;
	    !current_options.prep_gs_sim <- false;
	    !current_options.res_sim_input <-false;
	    !current_options.prep_sem_filter <- Options.Sem_Filter_None;
	    !current_options.sub_typing <- false;
(* fix is_eq_problem too include only non-flattened eq types ! *)

            out_warning "finite_models_loop.ml: preprocess swtiched off: properly treat eqaulity 2";
(*
	    let prep_clauses =  
	      Preprocess.preprocess (* ~is_eq_problem:(Problem_properties.has_equality input_clauses)  *) clauses_before_prep in
*)
            let prep_clauses =  clauses_before_prep in
	    
	    dbg D_preprocess (lazy 
				("\n\n ------- After Preprocessing ------- \n\n"
				 ^(Clause.clause_list_to_string prep_clauses)));
	    
	    
	    prep_clauses 
	  end
	else
      
	  clauses_before_prep
      in
      let clauses_ref = ref all_clauses in 
*)


      let clauses_ref = ref clauses_before_prep in 

      (* out_str ("\n-----------------------------\n"
	 ^(Clause.clause_list_to_tptp clauses)^"\n");
       *)
      
      List.iter
	Prop_solver_exchange.add_clause_to_solver axioms;

(*      let neg_bound_pred = add_neg_atom new_bound_pred in   *)
      

      let (assumptions_list, adjoint_assumptions_list) =  get_domain_assumptions (get_domain fm_state) in 
      
      Prop_solver_exchange.assign_solver_assumptions assumptions_list;
      Prop_solver_exchange.assign_sim_adjoint_lits adjoint_assumptions_list;

(*      Prop_solver_exchange.assign_solver_assumptions (neg_bound_pred::!bound_preds); *)

      
      (* new_dom_pred is added for all simplified claues *)

 (*     Prop_solver_exchange.assign_adjoint_preds [new_bound_pred];*)

      (*(neg_domain_pred::(!domain_preds));*)
      (* bound_preds := new_bound_pred::!bound_preds;*)


      dbg D_trace (lazy ("fm_loop before solver"));
      
(*      List.iter Prop_solver_exchange.add_clause_to_solver !clauses_ref; *)

(*---------ADDED now --------*)
      if (!model_size < !skip_until_bound )
      then 
        raise Skip_bound
      else
        begin
          Prop_solver_exchange.clear_soft_assumptions ();
          (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
          then
	    raise Unsatisfiable_gr
          );
  
          dbg D_trace (lazy ("fm_loop after solver"));            
     
          (*      let prover_functions = Proof_search_loop.create_provers_current_options !clauses_ref in *)
          if (!current_options.abstr_ref != [])
          then
            (Abstr_ref_process.ar_loop ~time_limit:Undef !current_options.abstr_ref !clauses_ref;)
            (* (Axiom_selection.axiom_selection_loop 
             *    ~time_limit:Undef !current_options.abstr_ref !clauses_ref;) *)
          else
(*
          if !current_options.abstr_ref_arg_filter
          then
            (Abstr_ref_arg_filter.abstr_ref_gr_filter_loop ~time_limit:Undef !clauses_ref;)
          else 
*) 
            begin
             (if !current_options.sat_fm_prep 
	     then 
	       begin             
                 let prep_state = 
                   Preprocess.prep_create_state ~clause_list:(!clauses_ref) ~extra_side_atoms:[]
                 in

           (* TODO: fix add inst_pre_model *)
                 Preprocess.preprocess_sim ~before_eq_axioms:false prep_state;

                 let old_subtyping_flag = !current_options.sub_typing in
                 !current_options.sub_typing <- false; (* types should be fixed; *)

                 Preprocess.preprocess_trans prep_state; 
                 !current_options.sub_typing <- old_subtyping_flag;

                 clauses_ref := Preprocess.prep_get_clauses prep_state;
                 dbg D_preprocess (lazy 
				     ("\n\n ------- After Preprocessing ------- \n\n"
				      ^(Clause.clause_list_to_string !clauses_ref)));	  
               end
             else ());

              Proof_search_loop.ps_full_loop ~time_limit:Undef !clauses_ref;
            end
        end
    with
      
      (* |Discount.Unsatisfiable *)
   (* | Instantiation.Unsatisfiable
    | Prop_solver_exchange.Unsatisfiable *)
      
(* Unsatisfiable_gr_na is left uncaght here *)
(*    |Unsatisfiable_gr_na -> failwith "dbg: finite_models_loop Unsatisfiable_gr_na" *)
    | Unsatisfiable_gr_na ->
(*
        failwith "finite_models_loop: Unsatisfiable_gr_na"
*)
	dbg D_trace (lazy ("Unsatisfiable_gr_na"));
	raise Unsatisfiable_gr_na
	  
    |Unsatisfiable_gr
      -> 
	(
         assert (Prop_solver_exchange.soft_assumptions_is_empty ());	 
	 dbg D_trace (lazy ("Unsatisfiable_gr"));  
	 let unsat_core = ref (Undef) in 
	 let unsat_core_parents = ref (Undef) in 
	
	 let get_unsat_core () = 
	   match !unsat_core with 
	   | Undef ->
	       let uc = Prop_solver_exchange.get_unsat_core ~soft:false () in
	       let unsat_core_clauses = UnsatCore.get_clauses uc in
	       dbg_env D_unsat_core
  		 (fun () -> 
		   
		   (						
			  (* Print unsat core *)
			  Format.printf
 			   "@\n%sUnsat core has size %d@\n@\n%a\n\n@."
			    pref_str
			    (List.length unsat_core_clauses)
			    (pp_any_list Clause.pp_clause_tptp "\n") unsat_core_clauses;						
			  
			 );
		 );
	       
	       unsat_core :=  (Def(unsat_core_clauses));
	       unsat_core_clauses
		 
	  |Def(uc) -> uc
	 in
	 
	let get_unsat_core_parents () = 
	  match !unsat_core_parents with
	  | Undef -> 
	      
              (* let unsat_core_leaves = TstpProof.get_leaves unsat_core_clauses in *)
	      let unsat_core_parent_clauses = (Clause.remove_bc_duplicates (TstpProof.get_parents (get_unsat_core()))) in
	      
	      dbg_env D_unsat_core
		(fun () ->
		  
		  (						
			 (* Print unsat core *)
			 Format.printf
			   "@\n%sUnsat leaves have size %d@\n@\n%a\n\n@."
			   pref_str
			   (List.length unsat_core_parent_clauses)
			   (pp_clause_list_with_source ~global_subsumption_justification_fun:None ~clausify_proof:false)
			   unsat_core_parent_clauses;						
			);
		);
	      unsat_core_parents := (Def(unsat_core_parent_clauses));
	      unsat_core_parent_clauses
	  | Def(ucp) -> ucp
	in
	
	(
	 if !current_options.sat_fm_uc_incr 
	 then 
	   if  !current_options.sat_fm_prep 
	   then (* we need to include all parents if using preprocessing  *)
	     begin
	      dbg D_unsat_core (lazy "\n finite_models_loop:  unsat_core_all_parents");
	       incr_domain_unsat_core (get_domain fm_state) (get_unsat_core_parents ()); 
	     end
	   else
	     begin 
	       dbg D_unsat_core (lazy "\n finite_models_loop:  unsat_core (no parents)");
	       incr_domain_unsat_core (get_domain fm_state) (get_unsat_core ());  
	    end
	 else
	   begin	  
	     dbg D_unsat_core (lazy "\n finite_models_loop: uniform incrementing\n");
	     assign_all_fp_ranges (get_domain fm_state) (!model_size+1); 
	   end
	);
	
	(
	if !current_options.sat_fm_lemmas
	then
	  (
	   
	   add_lemmas fm_state (get_unsat_core ());
	   (* add lemmas without parents, need to assume also that preprocessing and  resolution-based 
             simplifications are off *) 
	  )
	else ()
	);
	
	(* Instantiation.clear_after_inst_is_dead (); *)
(*	Proof_search_loop.provers_clear_and_remove_all (); *)
	
	model_size:= (get_domain_size (get_domain fm_state));
        )	
    | Skip_bound -> 
        (
         assign_all_fp_ranges (get_domain fm_state) (!model_size+1);         
         model_size:= (get_domain_size (get_domain fm_state));
        )
   
	
      done;
      out_warning ("Model Bound exceeded: "^(string_of_int model_bound)^"\n")

    
    end
 
