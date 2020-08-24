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
open Parser_types



(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_input
  | D_sde
  | D_flat
  | D_eq_ax

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_input -> "input"
  | D_sde -> "sde"
  | D_flat -> "flat"
  | D_eq_ax -> "eq_ax"

let dbg_groups =
  [
   D_trace; 
   D_input; 
   D_sde; 
   D_flat;  
   D_eq_ax 
 ]
    
let module_name = "eq_axioms"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)

    
type sym_set = Symbol.sym_set

type csig = Clause.clause_signature

let get_sym_types sym = Symbol.get_stype_args_val_def sym


let less_map_ref = Parser_types.less_map
let range_map_ref = Parser_types.range_map
let is_ess_less_range symb =
  (Symbol.is_essential_input symb)
    &&
  ((SMap.mem symb !less_map_ref) || (SMap.mem symb !range_map_ref))

let neg_symb = Symbol.symb_neg
(*let equality_symb = Symbol.symb_equality*)
let typed_equality_symb = Symbol.symb_typed_equality

let v0 = Var.get_first_var Symbol.symb_type_types
let v1 = Var.get_next_var v0
let v2 = Var.get_next_var v1
let v3 = Var.get_next_var v2
let v4 = Var.get_next_var v3

(* creates term from var and adds to term_db*)
(* let term_var var = TermDB.add_ref (Term.create_var_term var) term_db_ref *)

let tv0 = add_var_term v0
let tv1 = add_var_term v1
let tv2 = add_var_term v2
let tv3 = add_var_term v3
let tv4 = add_var_term v4

let term_var_typed vtype vval =
  add_var_term (Var.create vtype vval)


(*
  let add_fun_term symb args =
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref
 *)

(*
  let equality_term t s =
  let args = [t; s] in
  add_fun_term equality_symb args
 *)


(*
  let typed_equality_term stype_term t s =
  let args = [stype_term; t; s] in
  add_fun_term typed_equality_symb args

  let typed_equality_term_sym eq_type_sym t s =
  let eq_type = (add_fun_term eq_type_sym []) in
  typed_equality_term eq_type t s

  let neg_atom atom =
  let args = [atom] in
  add_fun_term neg_symb args

(*
  let dis_equality t s =
  neg_atom (equality_term t s)
 *)

  let dis_typed_equality stype t s =
  neg_atom (typed_equality_term stype t s)
 *)

(*
  let assign_eq_ax_param ax =
  Clause.assign_is_eq_axiom true ax;
(*	Clause.set_bool_param true Clause.input_under_eq ax;*) (* not used now*)
  (* Clause.assign_axiom_history Clause.Eq_Axiom ax *)
  Clause.assign_tstp_source_axiom_equality ax
 *)


let create_eq_ax_clause ax_lits =
  let tstp_source = Clause.tstp_source_axiom_equality in 
  let ax_clause = create_clause tstp_source ax_lits in
  Clause.assign_is_eq_axiom true ax_clause;
  ax_clause

(*
  let reflexivity_axiom () =
  let reflex_term = equality_term tv0 tv0 in
  let refl_ax = Clause.create [reflex_term] in
  assign_eq_ax_param refl_ax;
  refl_ax

(* axiom x0=x1 & x2 = x1 => x2=x0 is equiv to trans & symmetry *)
  let trans_symmetry_axiom () =
  let x01 = dis_equality tv0 tv1 in
  let x21 = dis_equality tv2 tv1 in
  let x20 = equality_term tv2 tv0 in
  let trans_sim_ax = Clause.create [x01; x21; x20] in
  assign_eq_ax_param trans_sim_ax;
  trans_sim_ax
 *)

(*-----typed versions--------*)
(* universal axioms over all types *)
(* we can preinstantiate for types occuring in the problem *)

(*-------reflexifity-------*)
let typed_reflexivity_axiom_var context =
  let reflex_term = add_typed_equality_term tv0 tv1 tv1 in
  let refl_ax = create_eq_ax_clause [reflex_term] in
  refl_ax

(* some times it is useful to have instantiatied eq axioms *)
let typed_reflexivity_axiom_type eq_type_sym =
  let eq_type = (add_fun_term eq_type_sym []) in
  let ttv0 = term_var_typed eq_type_sym 0 in
  let reflex_term = add_typed_equality_term eq_type ttv0 ttv0 in
  let refl_ax = create_eq_ax_clause [reflex_term] in
  refl_ax

let typed_reflexivity_axiom_type_set eq_type_set =
  let f eq_type rest =
    (typed_reflexivity_axiom_type eq_type):: rest
  in
  SSet.fold f eq_type_set []

(*---------trans_symmetry---------*)

let typed_trans_symmetry_axiom_var () =
  (* tv3 is used for types *)
  (*  let type_var_term = tv3 in *)
  let x01 = add_typed_disequality_term tv0 tv1 tv2 in
  let x21 = add_typed_disequality_term tv0 tv3 tv2 in
  let x20 = add_typed_equality_term tv0 tv3 tv1 in
  let trans_sim_ax = create_eq_ax_clause [x01; x21; x20] in
  trans_sim_ax

let typed_trans_symmetry_axiom_type eq_type_sym =
  let eq_type = (add_fun_term eq_type_sym []) in
  (* tv3 is used for types *)
  (*  let type_var_term = tv3 in *)
  let ttv0 = term_var_typed eq_type_sym 0 in
  let ttv1 = term_var_typed eq_type_sym 1 in
  let ttv2 = term_var_typed eq_type_sym 2 in
  
  let x01 = add_typed_disequality_term eq_type ttv0 ttv1 in
  let x21 = add_typed_disequality_term eq_type ttv2 ttv1 in
  let x20 = add_typed_equality_term eq_type ttv2 ttv0 in
  let trans_sim_ax = create_eq_ax_clause [x01; x21; x20] in
  trans_sim_ax

let typed_trans_symmetry_axiom_type_set eq_type_set =
  let f eq_type rest =
    (typed_trans_symmetry_axiom_type eq_type):: rest
  in
  SSet.fold f eq_type_set []

(*-------symmetry----------*)
(* used in finite_models *)
let typed_symmetry_axiom_sym eq_type_sym =
  let eq_type = (add_fun_term eq_type_sym []) in
  let ttv0 = term_var_typed eq_type_sym 0 in
  let ttv1 = term_var_typed eq_type_sym 1 in
  let neg_eq_x0_x1 = add_typed_disequality_term eq_type ttv0 ttv1 in
  let eq_x1_x0 = add_typed_equality_term eq_type ttv1 ttv0 in
  let sym_ax = create_eq_ax_clause [neg_eq_x0_x1; eq_x1_x0] in
  sym_ax

(*--------------typed version--------------*)
(* congruence axioms: given a hash table of types *)
(*(types with which sorted_euqality occurs)       *)
(* and a function f(x_1,..,x_n) we add congrunce axiom w.r.t. to the types table *)

(* congruence reduction based on flat args *)


let typed_congruence_axiom congr_type_set flat_arg_flags symb =
  match (Symbol.get_stype_args_val symb) with
  | Def (type_args, type_value) ->
      if type_args = []
      then
	(None)
      else				
	let fresh_vars_env = Var.init_fresh_vars_env () in
	let rec get_args_dis_lits
	    current_type_args current_flat_arg_flags args1 args2 dis_eq_lits =
	  (match (current_type_args, current_flat_arg_flags) with
	  | (h:: tl, fa::fa_tl) ->
	      (*     out_str ("h: "^(Symbol.to_string h)^"\n");*)
	      if (SSet.mem h congr_type_set)  && (not fa) 
	      then
		begin
		  let fresh_var1 = Var.get_next_fresh_var fresh_vars_env h in
		  let fresh_var2 = Var.get_next_fresh_var fresh_vars_env h in
		  let fresh_var_term1 = (add_var_term fresh_var1) in
		  let fresh_var_term2 = (add_var_term fresh_var2) in
		  
		  get_args_dis_lits										
		    tl fa_tl
		    (fresh_var_term1:: args1)
		    (fresh_var_term2:: args2)
		    ((add_typed_disequality_term
			(add_fun_term h [])
			fresh_var_term1
			fresh_var_term2):: dis_eq_lits)
		end
	      else
		(* same varaibles *)
		begin
		  let fresh_var = Var.get_next_fresh_var fresh_vars_env h in
		  let fresh_var_term = (add_var_term fresh_var) in
                  Statistics.incr_int_stat 1 Statistics.num_eq_ax_congr_red;
		  get_args_dis_lits
		    tl fa_tl
		    (fresh_var_term:: args1)
		    (fresh_var_term:: args2)
		    dis_eq_lits
		end
	  |([],[]) ->
	      ((List.rev args1), (List.rev args2), (List.rev dis_eq_lits))
          |_-> failwith "typed_congruence_axiom: should not happen"
	  )
	in
	let (args1, args2, dis_eq_lits) =
	  get_args_dis_lits
	    type_args flat_arg_flags [] [] [] in
	if (dis_eq_lits = [])
	then
	  (None)
	else
	  if (Symbol.is_pred symb)
	  then
	    let pred = add_fun_term symb args1 in
	    let neg_pred = add_neg_atom (add_fun_term symb args2) in
	    let pred_congr_ax = create_eq_ax_clause  (pred:: neg_pred:: dis_eq_lits)
	    in
	    Some(pred_congr_ax)
	  else
	    (let pos_part =
	      let t = add_fun_term symb args1 in
	      let s = add_fun_term symb args2 in
	      add_typed_equality_term (add_fun_term type_value []) t s
	    in
	    let fun_congr_ax = create_eq_ax_clause (pos_part:: dis_eq_lits) in
	    Some(fun_congr_ax)
	    )
  | Undef ->
      (None)

(* congruence types are colsure of eq types under function application:
   1. eq_types \subseteq congr_types
   2. for each f(t_1,..t_n) (t_i - type of ith arg of f),  
      if t_i is in congr_types then val_type of f is also in congr_types *)

module SymbReach = MakeReach (Symbol) (SMap) (SSet)

(* maps t_i -> all_vals_set *)
let get_arg_to_val_types_map csig = 
  let f symb map_f = 
    let (arg_types, val_type) = get_sym_types symb in
    if (SSet.mem symb csig.Clause.sig_eq_types) 
    then
      ( 
        map_f (* we do not need to add val eq types since they are by default are congr_types *)
       )
    else
      (
       let g map_g arg_t = 
        
        (* add val type to arg *)
        let val_t_set = 
          try 
            SMap.find arg_t map_g 
          with 
            Not_found -> SSet.empty
        in
        let new_val_t_set = SSet.add val_type val_t_set in 
        SMap.add arg_t new_val_t_set map_g 
       in
       List.fold_left g map_f arg_types
      )
  in
  SSet.fold f csig.Clause.sig_fun_preds SMap.empty
    
(*----*)
let get_congr_types csig = 
  let arg_to_val_types_map = get_arg_to_val_types_map csig in
  let succ_rel symb_type = 
    try
      SMap.find symb_type arg_to_val_types_map
    with 
      Not_found -> SSet.empty
  in
  let eq_types = csig.Clause.sig_eq_types in
  let reach_map = SymbReach.compute_reachability_set ~succ_rel eq_types in 
  let congr_types = (* domain of reach map *)
    let f symb_type _rech_depth congr_set = 
      SSet.add symb_type congr_set
    in
    SMap.fold f reach_map eq_types 
  in
  dbg D_eq_ax (lazy ("congr_types: "^(Symbol.list_to_string (SSet.elements congr_types))));
(*  let congr_no_bool = SSet.remove Symbol.symb_bool_type congr_types in *) (* bool_type can not occur as argument 
  congr_no_bool  *)
  congr_types (* keep bool type for the future cases when it might occur as an argument *)

    

(* typed_congr_axiom_list_sym_set *)
(* generic function for getting congruence based on csig.eq_type_set             *)

let typed_congr_axiom_list congr_types csig =
  (* we close eq_type_set first *)
  (*  let closed_eq_type_set = ref csig.Clause.sig_eq_types in*)
(*
  let rec f symb =
    if (SSet.mem symb csig.Clause.sig_eq_types)
    then ()
    else
      begin
	let (arg_types, val_type) = get_sym_types symb in
	List.iter f arg_types;
	let arg_is_in_closed_eq_type_set =
	  (List.exists
	     (fun arg_sym -> (SSet.mem arg_sym csig.Clause.sig_eq_types))
	     arg_types
	  )
	in
	if (arg_is_in_closed_eq_type_set) && (not (val_type == Symbol.symb_bool_type))
	then
	  (csig.Clause.sig_eq_types <- SSet.add val_type csig.Clause.sig_eq_types
	  )
	else ()
      end
  in
  SSet.iter f csig.Clause.sig_fun_preds;
  *)

  (*  let uf_eq_types = UF_ST.create 301 in *)

  let get_flat_arg_flags csig symb = (* TODO: skip if no equality types or no !current_options.eq_ax_congr_red *)
    if !current_options.eq_ax_congr_red 
    then
      try 
        SMap.find symb csig.Clause.sig_flat_arg_flags
      with 
        Not_found ->
          let (arg_types, _val_type) = get_sym_types symb in
          List.map (fun _ -> true) arg_types (* flat by default *)
    else
      let (arg_types, _val_type) = get_sym_types symb in
      List.map (fun _ -> false) arg_types (* non-fat by default *)
  in

  let f symb rest =
    let flat_arg_flags = get_flat_arg_flags csig symb in
    match (typed_congruence_axiom congr_types flat_arg_flags symb) with
    | Some ax ->
	(* out_str ("ax: "^(Clause.to_string ax)^"\n --------------\n");*)
	ax:: rest
    | None -> rest
  in
  SSet.fold f csig.Clause.sig_fun_preds []


(*-----------*)
let typed_eq_axioms_sig csig =
  if (SSet.is_empty csig.Clause.sig_eq_types)
  then
    []
  else
    (

     let eq_types = csig.Clause.sig_eq_types in
     let congr_types = get_congr_types csig in
     dbg D_eq_ax (lazy ("eq types: "^(Symbol.list_to_string (SSet.elements eq_types))));
     dbg D_eq_ax (lazy ("congr_types: "^(Symbol.list_to_string (SSet.elements congr_types))));

     let typed_reflexivity_ax =
      typed_reflexivity_axiom_type_set congr_types in 

     dbg D_eq_ax (lazy ("typed_reflexivity_ax:"));
     dbg D_eq_ax (lazy (Clause.clause_list_to_string typed_reflexivity_ax));

      (* in typed_reflexivity_ax we need congr_types not just eq_types  *)
      (* indeed : consider P(a,f(u)); ~P(a,f(v)); u=v *)
      (* where both args of P are congr but not eq (e.g. they have the same type) and the first arg of f is eq and congr *)
      (* then we need an instance of reflexifity a=a; together with cong ax: P(X,Y) <- P(X',Y') & X!=X' & Y!=Y'*)
     

     let typed_trans_symmetry_ax =
       typed_trans_symmetry_axiom_type_set eq_types in

     dbg D_eq_ax (lazy ("typed_trans_symmetry_ax:"));
     dbg D_eq_ax (lazy (Clause.clause_list_to_string typed_trans_symmetry_ax));

     let typed_cong_ax_list = typed_congr_axiom_list congr_types csig in

     dbg D_eq_ax (lazy ("typed_cong_ax_list:"));
     dbg D_eq_ax (lazy (Clause.clause_list_to_string typed_cong_ax_list));

     let eq_axioms =
       ((typed_reflexivity_ax)@((typed_trans_symmetry_ax)@typed_cong_ax_list)) in
     eq_axioms
    )


(*----------------------------------------------------------------------------------------*)
(*------ Replace pure disequalities with special symbol; should be done after typing -----*) 

(*
let add_pos_neg_eq_types (pos_eq_types, neg_eq_types) clause = 
  let f (pos_eq_types, neg_eq_types) lit =
      let atom = Term.get_atom lit in
      match (term_eq_view_type_symb atom) with 
      | Def(Eq_type_symb (eq_type, t,s)) -> 
	  if (Term.is_neg_lit lit)
	  then 
	    (pos_eq_types, (SSet.add eq_type neg_eq_types))	
	  else
	    ((SSet.add eq_type pos_eq_types), neg_eq_types)
      | Undef ->  (pos_eq_types, neg_eq_types)	
  in
  Clause.fold f (pos_eq_types, neg_eq_types) clause

(* returns a set of all eq type terms which  *)
let get_pure_diseq_types clause_list =
  List.fold_left add_pos_neg_eq_types (SSet.empty, SSet.empty) clause_list
*)


type spec_dis_eq_env = (* sde_env *)
    {
     mutable sde_symbs : symbol SMap.t; (* map from types to sde_symb of this type *)
   }

let create_sde_symb sde_env sde_type = 
  let symb_name = "$$iProver_spec_dis_eq_"^(Symbol.to_string sde_type) in
  let symb_type = create_stype  [sde_type;sde_type]  Symbol.symb_bool_type in 
  let sde_symb = create_symbol symb_name symb_type in 
  sde_env.sde_symbs <- SMap.add sde_type sde_symb sde_env.sde_symbs;
  sde_symb
      
let get_sde_symb sde_env sde_type = 
  try 
    SMap.find sde_type sde_env.sde_symbs 
  with 
    Not_found -> 
      create_sde_symb sde_env sde_type

let create_sde_atom sde_env sde_type s t = 
  add_fun_term (get_sde_symb sde_env sde_type) [s;t]
    
let create_sde_lit sde_env sign sde_type s t = 
  let atom = create_sde_atom sde_env sde_type s t in
  if sign 
  then 
    atom 
  else 
    add_compl_lit atom

let sde_process_lit sde_env lit =  
  let atom = Term.get_atom lit in
  match (term_eq_view_type_symb atom) with 
  | Def(Eq_type_symb (eq_type, s,t)) -> 
      (
       if (SMap.mem eq_type sde_env.sde_symbs) 
       then 
	 (
	  assert (Term.is_neg_lit lit);	  

(* add diseq  as a positive lit *)
	  create_sde_atom sde_env eq_type s t 
	 )
       else lit 
      )
  | Undef -> lit	
	    
  
let sde_process_clause sde_env clause = 
  let is_changed = ref false in 
  let f rest lit = 
    let new_lit = sde_process_lit sde_env lit in 
    (if (new_lit == lit)
    then ()
    else 
       (is_changed:=true)
    );
    (new_lit::rest)
  in
  let new_lits = Clause.fold f [] clause in 
  if !is_changed 
  then 

    let tstp_source = Clause.TSTP_inference_record (Clause.Dis_eq_elim, [clause]) in
    let new_clause = create_clause tstp_source new_lits in
    dbg D_sde (lazy (" old clause: "^(Clause.to_string clause)));
    dbg D_sde (lazy (" new clause: "^(Clause.to_string new_clause)));
    new_clause
  else
    clause

let create_sde_irref_axiom sde_type sde_symb = 
  (* ~deq_sde_type(X0,X0) *)
  let x0 = term_var_typed sde_type 0 in 
  let atom = add_fun_term sde_symb [x0;x0] in 
  let irref_lit = add_neg_atom atom in 
  let tstp_source = Clause.tstp_source_axiom_irref in 
  let irref_ax = create_clause tstp_source [irref_lit] in 
  dbg D_sde (lazy (" irref ax: "^(Clause.to_string irref_ax)));
  irref_ax

let sde_process_clause_list csig clause_list = 
  if (SSet.empty == csig.Clause.sig_pure_dis_eq_types) 
  then clause_list
  else 
    begin
      dbg D_sde (lazy (" pure_dis_types: \n "
		       ^(list_to_string Symbol.to_string (SSet.elements csig.Clause.sig_pure_dis_eq_types) "\n")));
      dbg D_sde (lazy (" input_clauses \n "^(Clause.clause_list_to_string clause_list)));
      Statistics.incr_int_stat (SSet.cardinal csig.Clause.sig_pure_dis_eq_types) Statistics.pure_diseq_elim;
      let sde_env = {sde_symbs = SMap.empty} in
      let fill_sde_env sde_env = 
	let f sde_type = ignore (create_sde_symb sde_env sde_type) in	  
	SSet.iter f csig.Clause.sig_pure_dis_eq_types
      in
      fill_sde_env sde_env;
      
      let f rest cl = (sde_process_clause sde_env cl)::rest in
      let processed_clauses =  List.fold_left f [] clause_list in 
      
      let irref_axioms =
	let f sde_type sde_symb rest = (create_sde_irref_axiom sde_type sde_symb)::rest in 
	SMap.fold f sde_env.sde_symbs []
      in
      irref_axioms@processed_clauses 
    end 

let pure_dis_eq_elim clause_list = 
  let csig = Clause.clause_list_signature clause_list in
  sde_process_clause_list csig clause_list


(*---------- eq_axioms -----------------------*)

(*module UF_ST = Union_find.Make(Symbol)*)

(* it should be closed under funct application later *)
(* returns (sym_set, eq_types_set) *)

let get_symb_and_type_eq_set_basic clause_list =
  let csig = Clause.clause_list_signature clause_list in
  csig

let eq_axiom_list clause_list =
  (*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  let csig = get_symb_and_type_eq_set_basic clause_list in
  typed_eq_axioms_sig csig

(*--------------------------------------------*)
let distinct_ax_list () =
  let default_type_term = (add_fun_term Symbol.symb_default_type []) in
  if (Symbol.is_essential_input Symbol.symb_typed_equality)
  then
    (
     let dist_axioms_one_term term term_list =
       let f rest cterm =
	 let dis_eq_term = (add_typed_disequality_term default_type_term term cterm) in
	 let tstp_source = Clause.tstp_source_axiom_distinct in
	 let dis_ax = create_clause tstp_source [dis_eq_term] in
	 (* Clause.assign_axiom_history Clause.Distinct_Axiom dis_ax; *)					
	 dis_ax:: rest
       in
       List.fold_left f [] term_list
     in
     let rec distinct_axioms_from_one_dist' rest_axs cur_term dist_terms_rest =
       let new_axs = (dist_axioms_one_term cur_term dist_terms_rest)@rest_axs in
       match dist_terms_rest with
       | h:: tl -> distinct_axioms_from_one_dist' new_axs h tl
       |[] -> new_axs
     in
     let distinct_axioms_from_one_dist rest_axs dist_term_list =
       match dist_term_list with
       | h:: tl -> distinct_axioms_from_one_dist' rest_axs h tl
       |[] -> rest_axs
     in
     List.fold_left distinct_axioms_from_one_dist [] !Parser_types.distinct
    )
  else
    []

(*------------ less range axioms -------------------------------*)
(* we do not need congruence axioms for less_i and range_i_j    *)

let bit_index_str i =
  "$$bitIndex"^(string_of_int i)

let stype_bit_index = (Symbol.create_stype [] Symbol.symb_ver_bit_index_type)

let bit_index_type_term () =
  add_fun_term Symbol.symb_ver_bit_index_type []

let bit_index_var vval = 
  Var.create Symbol.symb_ver_bit_index_type vval

let bit_index_var_term vval = 
  add_var_term (bit_index_var vval)


let bit_index_symb i =
  let symb =
    (Symbol.create_from_str_type (bit_index_str i) stype_bit_index)
  in
  SymbolDB.add_ref symb symbol_db_ref

let bit_index_term i =
  add_fun_term (bit_index_symb i) []

let bit_index_atom symb i =
  add_fun_term symb [(bit_index_term i)]

let get_max_bit_index () =
  let f_less symb i curr_max =
    if ((curr_max < i) && (Symbol.is_essential_input symb))
    then
      ((*out_str ("Symbol "^(Symbol.to_string symb)^" "^(string_of_int i)^"\n"); *)
	i)
    else
      curr_max
  in
  (* less does not include the ind_bound: +1 *)
  let max_less = (SMap.fold f_less !less_map_ref 0) - 1 in
  (* out_str ("\n max_less: "^(string_of_int max_less)^"\n");*)
  (* we assume bit-vector notation: biggest first (71,0) *)
  let f_range symb (i, j) curr_max =
    if ((curr_max < i) && (Symbol.is_essential_input symb))
    then
      i
    else
      curr_max
  in
  let max_less_range = SMap.fold f_range !range_map_ref max_less in
  (* out_str ("\n max_less_range: "^(string_of_int max_less_range)^"\n");*)
  max_less_range

(*
  let always_true_ax symb =
  Clause.create [(add_fun_term symb [tv0])]

  let always_false_ax symb =
  Clause.create [(neg_atom (add_fun_term symb [tv0]))]
 *)


(*----------------*)
let less_pos_axs symb max_pos_ind =
  let f rest i =
    (create_clause Clause.tstp_source_axiom_less [(bit_index_atom symb i)]):: rest in
  fold_down_interval f 0 (max_pos_ind -1) []

let less_neg_axs symb max_pos_ind max_ind =
  let f rest i =
    (create_clause Clause.tstp_source_axiom_less
       [(add_neg_atom (bit_index_atom symb i))]):: rest in
  fold_down_interval f max_pos_ind max_ind []

let less_eq_ax symb max_pos_ind =
  let bv0 = bit_index_var_term 0 in
  let f rest i =
    (add_typed_equality_term (bit_index_type_term ()) (bit_index_term i) bv0):: rest in
  let eq_terms = fold_down_interval f 0 (max_pos_ind -1) [] in
  let neg_less_term = add_neg_atom (add_fun_term symb [bv0]) in
  create_clause Clause.tstp_source_axiom_less (neg_less_term:: eq_terms)

(*-------------*)

let range_pos_axs symb min_int_ind max_int_ind =
  let f rest i =
    (create_clause Clause.tstp_source_axiom_range [(bit_index_atom symb i)]):: rest in
  fold_down_interval f min_int_ind max_int_ind []

let range_neg_axs symb min_int_ind max_int_ind max_ind =
  let f rest i =
    (create_clause Clause.tstp_source_axiom_range [(add_neg_atom (bit_index_atom symb i))]):: rest in
  let left = fold_down_interval f 0 (min_int_ind -1) [] in
  let right = fold_down_interval f (max_int_ind +1) max_ind [] in
  left@right

let range_eq_ax symb min_int_ind max_int_ind =
  let bv0 = bit_index_var_term 0 in
  let f rest i =
    (add_typed_equality_term (bit_index_type_term ()) (bit_index_term i) bv0):: rest in
  let eq_terms = fold_down_interval f min_int_ind max_int_ind [] in
  let neg_range_term = add_neg_atom (add_fun_term symb [bv0]) in
  create_clause Clause.tstp_source_axiom_range (neg_range_term:: eq_terms)

(*let range_axiom_via_less range_symb *)
(* less axioms should be added after the range axioms since mode less symbols can be added *)

(*
  let range_axiom_via_less range_symb
 *)

let less_axioms' max_ind =
  let f symb i rest =
    (* consider to uncomment later *)
    (* if (i = 0)
       then
       (always_false_ax symb):: rest
       else
       if (i = max_ind +1)
       then
       (always_true_ax symb):: rest
       else
     *)
    if (Symbol.is_essential_input symb)
    then
      (
       let symb_axs =
	 (less_eq_ax symb i):: ((less_pos_axs symb i)
				@(less_neg_axs symb i max_ind)) in
       symb_axs@rest
      )
    else
      rest
  in
  SMap.fold f !less_map_ref []

let less_axioms () =
  let max_ind = get_max_bit_index () in
  let less_axioms = less_axioms' max_ind in
  (* Clause.assign_axiom_history_cl_list Clause.Less_Axiom less_axioms; *)
  less_axioms

let range_axioms' max_ind =
  let f symb (max_int_ind, min_int_ind) rest =
    (* if uncommented then incorrect sat result on  *)
    (*Examples/attachments_2011_06_09_from_FMCAD2010_built_in_less_range/bpbimodalm_B2ConcreateClk_no_range_ax.cnf*)
    (*
      if (min_int_ind =0 && max_int_ind = max_ind)
      then
      (always_true_ax symb):: rest
      else
     *)
    if (Symbol.is_essential_input symb)
    then
      (
       ((range_eq_ax symb min_int_ind max_int_ind)::
	((range_pos_axs symb min_int_ind max_int_ind)
	   (*@(range_neg_axs symb min_int_ind max_int_ind max_ind)*)))@rest
      )
    else
      rest
  in
  SMap.fold f !range_map_ref []

let range_axioms () =
  let max_ind = get_max_bit_index () in
  let range_axioms = range_axioms' max_ind in
  (* Clause.assign_axiom_history_cl_list Clause.Less_Axiom range_axioms; *)
  range_axioms

let less_range_axioms () =
  (* out_str "\n\n out less map\n\n";
     SMap.iter (fun symb _ -> out_str (Symbol.to_string symb)) !less_map_ref;
     out_str "\n\n end out less map\n\n";
   *)
  let max_ind = get_max_bit_index () in
  
  (* out_str
     (Clause.clause_list_to_tptp (less_axioms' max_ind)); *)
  
  let less_range_axioms =
    (less_axioms' max_ind) @ (range_axioms' max_ind)
  in		
  less_range_axioms

(*--------------- Brand's transformation -------------------*)
(*--------------- Flattening -> no congrunce axioms --------*)



(*
(* move *)
  let rec get_max_var_term current_max_var_ref term =
  match term with
  | Term.Fun (_, args, _) ->
  Term.arg_iter (get_max_var_term current_max_var_ref) args
  | Term.Var (v, _) ->
  if (Var.compare v !current_max_var_ref) > 0
  then
  (current_max_var_ref := v)
  else ()

  let get_max_var clause =
  let var_ref = ref (Var.get_first_var ()) in
  Clause.iter (get_max_var_term var_ref) clause;
  !var_ref
 *)

(*---------Basic flattening------------------------*)
(* Flattening of a clause is done in two stages:                      *)
(* First, we build a hash table (var_env) mapping non-var term into bvars. *)
(* Second, we use var_env  to build flat terms.            *)
(* In "term_flattening_env var_env max_var_ref term"       *)
(* max_var is max var used                                 *)
(* the input term itself also added to the the var_env     *)
(* if a function term t statisfies add_term_to_def_test    *)
(* we do not need to go                                    *)
(* to subterms  but add 1. a definition t->x into env and  *)
(* 2. a definition into term_def_table (def. of all subterms of t are also added) *)
(* and later add  \neg R_t(x) to the clause *)

let b_orig  = 0 
let b_fresh = 1 (* bound for making vars fresh *)

let rec term_flattening_env renaming_env var_env term =
  match term with
  | Term.Var _ -> ()
  | Term.Fun (symb, args, _) ->
      if (THtbl.mem var_env term)
      then ()
      else
	(
	 (
	  (*
	    if (Symbol.is_fun symb)
	    && (add_term_to_def_test term)
	    then
	    ((* out_str ("Adding to add_term_def_table term: "
		^(Term.to_string term)^"\n");*)
	    add_term_def_table term)
	    else
	   *)
	  (Term.arg_iter (term_flattening_env renaming_env var_env) args)
	 );
	 (* if (Symbol.is_fun symb)
	    then
	  *)
	 (
	  let t_type = Symbol.get_val_type_def symb in 						
	  let ren_var = SubstBound.find_renaming renaming_env (b_fresh, (SubstBound.get_next_unused_var renaming_env t_type)) in
	  let ren_var_term = add_var_term ren_var in 
	  THtbl.add var_env term ren_var_term					
	 )
	   (*	 else ()*)
	)

let flat_term_to_var renaming_env var_env t =
  match t with 
  | Term.Var(v,_) -> 
    (*  let t_type = Var.get_type v in 	*)
(*      let ren_var = SubstBound.find_renaming renaming_env (b_orig, (SubstBound.get_next_unused_var renaming_env t_type)) in*)
      let ren_var = SubstBound.find_renaming renaming_env (b_orig, v) in
      add_var_term ren_var
  | Term.Fun (_,_,_) ->
      (			try
	(*     term_flattening_env var_env max_var_ref t;*)
	THtbl.find var_env t
      with Not_found -> failwith "flat_term_to_var: Not_found"
	 )
	
let flat_top renaming_env var_env term =
  match term with
  | Term.Fun (symb, args, _) ->
      Term.arg_iter (term_flattening_env renaming_env var_env) args;
      let new_args =
	Term.arg_map (fun t -> flat_term_to_var renaming_env var_env t) args in
      TermDB.add_ref (Term.create_fun_term_args symb new_args) term_db_ref
  | Term.Var _ -> flat_term_to_var renaming_env var_env term

let flat_lit_env renaming_env var_env lit =
  let f atom =
    match atom with
    | Term.Fun (symb, args, _) ->
	if (symb == Symbol.symb_typed_equality)
	then
	  match (Term.arg_to_list args) with
	  | [eq_type; t1; t2] ->
	      let new_t1 = flat_top renaming_env var_env t1 in
	      let new_t2 = flat_top renaming_env var_env t2 in
	      add_typed_equality_term eq_type new_t1 new_t2
	  | _ -> failwith "flat_lit_env 1"
		
	else
	  flat_top renaming_env var_env atom
    | Term.Var _ -> failwith "flat_lit_env 2"
  in
  TermDB.add_ref (Term.apply_to_atom f lit) term_db_ref

(*---------------------------------*)
let flat_clause clause =
  let renaming_env = SubstBound.init_renaming_env () in
  let var_env = THtbl.create 19 in
  let lit_list = Clause.get_literals clause in
  let flat_lits_without_neg_def =
    List.map (flat_lit_env renaming_env var_env) lit_list in
  (*let default_type_term = (add_fun_term Symbol.symb_default_type []) in*)
  let dis_eq_term t s =
    let t_type = Term.get_term_type t in 
    let t_type_term = (add_fun_term t_type []) in
    (add_typed_disequality_term t_type_term t s) 
  in
  let f t x rest =
    (dis_eq_term (flat_top renaming_env var_env t) x):: rest in
  let neg_def = THtbl.fold f var_env [] in
  let flat_clause = create_clause (Clause.tstp_source_flattening clause) (neg_def@flat_lits_without_neg_def) in
  dbg D_flat (lazy ("clause: "^(Clause.to_string clause)));
  dbg D_flat (lazy ("flat  : "^(Clause.to_string flat_clause)));
  flat_clause

let flat_clause_list clause_list = List.map flat_clause clause_list

let eq_axioms_flatting clause_list =
 let csig = get_symb_and_type_eq_set_basic clause_list in
  if (SSet.is_empty csig.Clause.sig_eq_types)
  then
    []
  else
    (
     let typed_reflexivity_ax =
       typed_reflexivity_axiom_type_set csig.Clause.sig_eq_types in
     
     let typed_trans_symmetry_ax =
       typed_trans_symmetry_axiom_type_set csig.Clause.sig_eq_types in

     typed_reflexivity_ax@typed_trans_symmetry_ax
    )
      
(*
let eq_axioms_flatting clause_list =
  if (Symbol.is_essential_input Symbol.symb_typed_equality)
  then
    (			
	let flat_clauses = List.map flat_clause clause_list in
	let eq_ax = [(typed_reflexivity_axiom_var ()); (typed_trans_symmetry_axiom_var ())] in
	eq_ax@flat_clauses
       )
  else
    clause_list
*)

(*-------------------------------------*)
(*-------- Bit-vector oprations -------*)
(*-------------------------------------*)

let bv_symb_map = Parser_types.bit_vector_name_map 
let bv_op_htbl  = Parser_types.bv_op_htbl

(*
let bv_add_map =  Parser_types.bv_add_map
let bv_sub_map =  Parser_types.bv_sub_map
*)

let bit_index_type = Symbol.symb_ver_bit_index_type
let state_type = Symbol.symb_ver_state_type
let bool_type = Symbol.symb_bool_type

(*module SMap = Symbol.Map*)

type bv_domain = 
    {
     bv_max_index : int;           (* max index in bv = size - 1  *)
     bv_index_list : term list;    (* ordered list of index terms  [0; .. ;max_index] *)
     bv_succ_symb : symbol;
     bv_succ_atom_list : term list (* ordered list of atoms [succ_m(b0,b1);..; succ_m(max_index-1,max_index)] *)
   } 

let bv_domain_map = ref IntMap.empty (* map from max_index -> bv_domain*)

(* creates bit index list from [0; .. ;max index] *)
let create_bit_index_list max_index = 
  let rec f i rest = 
    if i >= 0 
    then 
      let new_rest = (bit_index_term i)::rest in 
      let new_i = i-1 in
      f new_i new_rest
    else 
      rest
  in
  f max_index []

(*-----------create sussessor------------*)

let get_max_index_bv () = 
  SMap.fold (fun bv_symb size current_max -> 
    if (size > (current_max+1)) then (size-1) else current_max)       
    !bv_symb_map
    0


(* extend for several sizes of bv: several succ? or based on less and bounds ? *)    
let create_succ_symb max_ind = 
  let succ_type = create_stype  [bit_index_type; bit_index_type] bool_type in
  let succ_name = Symbol.add_iprover_pref ("bv_succ_"^(string_of_int max_ind)) in
  let succ_symb = create_symbol succ_name succ_type in
  Symbol.assign_is_essential_input true succ_symb;
  succ_symb

let create_succ_atom_int succ_symb i j = 
  add_fun_term succ_symb [(bit_index_term i); (bit_index_term j)]

let create_succ_atom_ind succ_symb ind_i ind_j = 
  add_fun_term succ_symb [ind_i; ind_j]

let create_succ_atom_terms succ_symb t1 t2 = 
  add_fun_term succ_symb [t1; t2]

let fill_bv_domain_map () = 
  let f bv_symb size = 
    if (size > 1) (* ignore bv of size 1 *)
    then
      begin
	let bv_max_index = size - 1 in
	if (IntMap.mem bv_max_index !bv_domain_map) 
	then ()
	else
	  (
	   let bv_index_list = create_bit_index_list bv_max_index in    
	   let bv_succ_symb = create_succ_symb bv_max_index in 
	   let bv_succ_atom_list = 
	     assert((List.length bv_index_list)>1);
	     let rec f acc bv_i_list = 
	       match bv_i_list with 
	       |ind_i::ind_j::tl -> 
		   let new_acc = (create_succ_atom_ind bv_succ_symb ind_i ind_j)::acc in
		   let new_tl = ind_j::tl in
		   f new_acc new_tl
	       |[_] (* failwith ("fill_bv_domain_map: list should not have one element: "^(Term.to_string i))*)
	       |[] -> List.rev acc
	     in		   
	     (f [] bv_index_list)
	   in
	   let bv_domain = 
	     {
	      bv_max_index = bv_max_index;
	      bv_index_list = bv_index_list;
	      bv_succ_symb = bv_succ_symb;
	      bv_succ_atom_list =  bv_succ_atom_list;
	    }
	   in
	   bv_domain_map := IntMap.add bv_max_index bv_domain !bv_domain_map    
	  )
      end
    else ()      
  in
  SMap.iter f !bv_symb_map

(* axioms of the form succ_m(bi_0,bi_1), .., succ_m(bi_m-1,bi_b) for each m in domain_map *)
let succ_atom_to_clause succ_atom_list = 
  List.map (fun succ_atom -> create_clause Clause.tstp_source_axiom_bv_succ [succ_atom]) succ_atom_list

(* should run fill_bv_domain_map () before *)
let get_succ_axioms () =
  let f _ bv_domain rest = 
    (succ_atom_to_clause bv_domain.bv_succ_atom_list)@rest
  in       
  IntMap.fold f !bv_domain_map []

(*----------------*)

(* bit-vectors are of four types: *)
(* 1. bv(state,ind) (full); *)
(* 2. bv(ind) (state independent); *)
(* 3. bv(state) (e.g. result of comparision of bv when at leat one arg is state dep.) *)
(* 4. bv (e.g. result of comparision when both args are state indep. ) *)

(* bit-vectors can be state dependent of the form bv(S,Ind) or *)
(* state independent (e.g. constant BV) of the form bv() *)

let create_bv_symb stype bv_name = 
  let bv_symb = create_symbol bv_name stype in
  Symbol.assign_is_essential_input true bv_symb; 
  bv_symb

(*
let create_bv_symb is_state_dep bv_name = 
  let stype =
    if is_state_dep 
    then 
      create_stype [state_type; bit_index_type] bool_type 
    else
      create_stype [bit_index_type] bool_type
  in
  (* should be added to bv_map in parser_types ?*)
  let bv_symb = create_symbol bv_name stype in
  Symbol.assign_is_essential_input true bv_symb; 
  bv_symb
 *)


(* we assume that bv_symb is a bit-vector symbol *)

let is_state_dep_bv_symb bv_symb = 
 let arg_types,_val_type = Symbol.get_stype_args_val_def bv_symb in 
 match arg_types with 
 | [state_type; _bit_ind_type] when (state_type == Symbol.symb_ver_state_type) -> true
 | [state_type] when (state_type == Symbol.symb_ver_state_type) -> true
 | _ -> false


(* creates atom of the from bv(state_term,ind_term) or bv(ind_term)/bv(state_term)/bv deepning on the type of symb *)

let create_bv_atom bv_symb state_term ind_term =
  let (arg_types, _val_type_bool) = Symbol.get_stype_args_val_def bv_symb in
  match arg_types with 
  |[state_type;bit_ind_type] 
      when (state_type == Symbol.symb_ver_state_type && bit_ind_type == Symbol.symb_ver_bit_index_type) ->
	add_fun_term bv_symb [state_term; ind_term]
  |[state_type]  
    when  (state_type == Symbol.symb_ver_state_type) -> 
      add_fun_term bv_symb [state_term]
  |[bit_ind_type] 
    when (bit_ind_type == Symbol.symb_ver_bit_index_type) -> 
      add_fun_term bv_symb [ind_term]
  |[] -> add_fun_term bv_symb []
  |_ -> failwith ("create_bv_atom: symbol "^(Symbol.to_string bv_symb)^(" is not of bit-vector type "))


(*
  if (is_state_dep_bv_symb bv_symb) 
  then
    add_fun_term bv_symb [state_term; ind_term]
  else
    add_fun_term bv_symb [ind_term]
*)

(* creates atom of the from bv(X0_state,X0_bitind) or bv(X0_bitind)/bv(X0_state)/bv deepning on the type of symb *)

let state_var_term i = term_var_typed state_type i
let bv_index_var_term i = term_var_typed bit_index_type i

let bv_create_var_atom bv_symb = 
 let state_v0 = state_var_term 0 in
 let index_v0 = bv_index_var_term 0 in 
 create_bv_atom bv_symb state_v0 index_v0 
 
let get_base_name name = Symbol.remove_iprover_pref name

let get_base_name_symb symb = get_base_name (Symbol.get_name symb)

(* --- bv_shl1 --- *)

(*
let create_bv_shift_symb bv_name = 
  let bv_shl1_name =  Symbol.add_iprover_pref ("bv_shl1_"^(get_base_name bv_name)) in
  create_bv_symb bv_shl1_name
*)
(*
  ~shift1_p(s,0) \andl 
  succ(j,i) & p(s,j) -> shft1_p (s,i) 
  succ(j,i) & ~p(s,j) -> ~shft1_p (s,i) 
*)

(*
let create_shiftl1_symb bv_symb = 
 let bv_base_name = get_base_name_symb bv_symb in
 let bv_shl1_symb = create_bv_shift_symb bv_base_name in
 *)

let bv_shl1_axs bv_domain shift_symb bv_symb_arg_list = 
  let bv_symb = 
    match bv_symb_arg_list with 
    |[symb] -> symb 
    |_-> failwith "bv_shl1_axs argument should contain one symbol"
  in
  let succ_symb = bv_domain.bv_succ_symb in
  let state_v0 = state_var_term 0 in

(* ~shift1_p(s,0) *)
  let shft_v0_i0 = create_bv_atom shift_symb state_v0  (bit_index_term 0) in      
  let neg_ax = create_clause  Clause.tstp_source_axiom_bv_shl1 [(add_neg_atom shft_v0_i0)] in (* ~shift1_p(s,0) *)

(* succ(iv0,iv1) & p(sv0,iv0) -> shft1_p (sv0,iv1) *)
  let index_v0 = bv_index_var_term 0 in 
  let index_v1 = bv_index_var_term 1 in
  let succ_atom_v0_v1 = create_succ_atom_terms succ_symb index_v0 index_v1 in
  let p_sv0_iv0 = create_bv_atom bv_symb state_v0 index_v0 in
  let shft1_p = create_bv_atom shift_symb state_v0 index_v1 in

(* succ(iv0,iv1) & p(sv0,iv0) -> shft1_p (sv0,iv1)   *)
  let shft1_p_ax_1 = create_clause Clause.tstp_source_axiom_bv_shl1 [(add_neg_atom succ_atom_v0_v1); (add_neg_atom p_sv0_iv0); shft1_p] in

(* succ(iv0,iv1) & ~p(sv0,iv0) -> ~shft1_p (sv0,iv1) *)
  let shft1_p_ax_2 = create_clause Clause.tstp_source_axiom_bv_shl1 [(add_neg_atom succ_atom_v0_v1);  p_sv0_iv0; (add_neg_atom shft1_p)] in
  [neg_ax; shft1_p_ax_1; shft1_p_ax_2]


(*---- bv_shr1 ---*)

let bv_shr1_axs bv_domain shift_symb bv_symb_arg_list = 
  let bv_symb = 
    match bv_symb_arg_list with 
    |[symb] -> symb 
    |_-> failwith "bv_shr1_axs argument should contain one symbol"
  in
  let succ_symb = bv_domain.bv_succ_symb in
  let max_index = bv_domain.bv_max_index in
  let state_v0 = state_var_term 0 in

  (* ~shift_p(s,max_index) *)
  let shft_v0_max = create_bv_atom shift_symb state_v0  (bit_index_term max_index) in      
  let neg_ax = create_clause  Clause.tstp_source_axiom_bv_shr1 [(add_neg_atom shft_v0_max)] in (* ~shift1_p(s,0) *)

  (* succ(iv0,iv1) & p(sv0,iv1) -> shft1_p (sv0,iv0) *)
  let index_v0 = bv_index_var_term 0 in 
  let index_v1 = bv_index_var_term 1 in
  let succ_atom_v0_v1 = create_succ_atom_terms succ_symb index_v0 index_v1 in
  let p_sv0_iv1 = create_bv_atom bv_symb state_v0 index_v1 in
  let shft1_p = create_bv_atom shift_symb state_v0 index_v0 in

(* succ(iv0,iv1) & p(sv0,iv1) -> shft1_p (sv0,iv0)   *)
  let shft1_p_ax_1 = create_clause Clause.tstp_source_axiom_bv_shr1 
      [(add_neg_atom succ_atom_v0_v1); (add_neg_atom p_sv0_iv1); shft1_p] in

(* succ(iv0,iv1) & ~p(sv0,iv1) -> ~shft1_p (sv0,iv0) *)
  let shft1_p_ax_2 = create_clause Clause.tstp_source_axiom_bv_shl1 
      [(add_neg_atom succ_atom_v0_v1);  p_sv0_iv1; (add_neg_atom shft1_p)] in
  [neg_ax; shft1_p_ax_1; shft1_p_ax_2]




(*------- create auxillary symbols like c_in/c_out/trigger_in/trigger_out used in several operations-----*)
(*------- ex: bv_create_aux_symb add_res_symb "bv_cin" ---*)
let bv_create_aux_symb bv_res_symb aux_str = 
  let bv_aux_name = Symbol.add_iprover_pref (aux_str^"_"^(get_base_name_symb bv_res_symb)) in
  let bv_aux_type = 
    if (is_state_dep_bv_symb bv_res_symb)
    then
      Symbol.create_stype [Symbol.symb_ver_state_type; Symbol.symb_ver_bit_index_type] Symbol.symb_bool_type 
    else
      Symbol.create_stype [Symbol.symb_ver_bit_index_type] Symbol.symb_bool_type 
  in
  create_bv_symb bv_aux_type bv_aux_name

(*    
let create_bv_cin_symbol bv_res_symb = 
  bv_create_aux_symb bv_res_symb "bv_cin"
    
let create_bv_cout_symbol bv_res_symb = 
  bv_create_aux_symb bv_res_symb "bv_out"
*)
 

(*--bv_add---------*)    

(* clausification by E prover see .org

(* needs to be added: cin = shl1 cout  *)

cnf(i_0_1,plain,(add(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|~cin(X1,X2))).
cnf(i_0_2,plain,(add(X1,X2)|p_x(X1,X2)|~p_y(X1,X2)|cin(X1,X2))).
cnf(i_0_3,plain,(add(X1,X2)|~p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))).
cnf(i_0_4,plain,(add(X1,X2)|~p_x(X1,X2)|~p_y(X1,X2)|~cin(X1,X2))).

cnf(i_0_5,plain,(~add(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))).
cnf(i_0_6,plain,(~add(X1,X2)|p_x(X1,X2)|~p_y(X1,X2)|~cin(X1,X2))).
cnf(i_0_7,plain,(~add(X1,X2)|~p_x(X1,X2)|p_y(X1,X2)|~cin(X1,X2))).
cnf(i_0_8,plain,(~add(X1,X2)|~p_x(X1,X2)|~p_y(X1,X2)|cin(X1,X2))).

cnf(i_0_9,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|)).
cnf(i_0_10,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|)).
cnf(i_0_11,plain,(~cout(X1,X2)|p_x(X1,X2)|cin(X1,X2))).
cnf(i_0_12,plain,(~cout(X1,X2)|p_x(X1,X2)|cin(X1,X2)|)).
cnf(i_0_13,plain,(~cout(X1,X2)|p_y(X1,X2)|cin(X1,X2))).
cnf(i_0_14,plain,(~cout(X1,X2)|p_y(X1,X2)|cin(X1,X2))).
cnf(i_0_15,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))).
cnf(i_0_16,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))).

cnf(i_0_17,plain,(cout(X1,X2)|~p_x(X1,X2)|~p_y(X1,X2))).
cnf(i_0_18,plain,(cout(X1,X2)|~p_x(X1,X2)|~cin(X1,X2))).
cnf(i_0_19,plain, (cout(X1,X2)|~p_y(X1,X2)|~cin(X1,X2))).

*)



let create_bv_add_axs bv_domain add_res_symb add_arg_symbs  = 
  
  let (p_x_symb, p_y_symb) = get_pair_from_list add_arg_symbs in
  let cin_symb = bv_create_aux_symb add_res_symb "bv_cin" in 
  let cout_symb = bv_create_aux_symb add_res_symb "bv_cout" in 

(* shif axioms *)
  let cin_shl1_out_axioms = bv_shl1_axs bv_domain cin_symb [cout_symb] in

 
(* literals *)
  let add = bv_create_var_atom add_res_symb in
  let p_x = bv_create_var_atom p_x_symb in
  let p_y = bv_create_var_atom p_y_symb in
  let cin = bv_create_var_atom cin_symb in
  let cout = bv_create_var_atom cout_symb in

  let nadd = add_neg_atom add in
  let np_x = add_neg_atom p_x in
  let np_y = add_neg_atom p_y in
  let ncin = add_neg_atom cin in
  let ncout = add_neg_atom cout in

  let c lits =  create_clause Clause.tstp_source_axiom_bv_add lits in
  let add_axioms = 
    [
     c [add; p_x;  p_y; ncin];   (* cnf(i_0_1,plain,(add(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|~cin(X1,X2))). *)
     c [add; p_x; np_y; cin];    (* cnf(i_0_2,plain,(add(X1,X2)|p_x(X1,X2)|~p_y(X1,X2)|cin(X1,X2))). *)
     c [add; np_x; p_y; cin];    (* cnf(i_0_3,plain,(add(X1,X2)|~p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))).*)
     c [add; np_x; np_y; ncin];  (* cnf(i_0_4,plain,(add(X1,X2)|~p_x(X1,X2)|~p_y(X1,X2)|~cin(X1,X2))).*)

     c [nadd; p_x;  p_y; cin];  (* cnf(i_0_5,plain,(~add(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))). *)
     c [nadd; p_x; np_y; ncin]; (* cnf(i_0_6,plain,(~add(X1,X2)|p_x(X1,X2)|~p_y(X1,X2)|~cin(X1,X2))).*)
     c [nadd; np_x; p_y; ncin]; (* cnf(i_0_7,plain,(~add(X1,X2)|~p_x(X1,X2)|p_y(X1,X2)|~cin(X1,X2))). *)
     c [nadd; np_x; np_y; cin]; (* cnf(i_0_8,plain,(~add(X1,X2)|~p_x(X1,X2)|~p_y(X1,X2)|cin(X1,X2))). *)

     c [ncout; p_x; p_y];        (* cnf(i_0_9,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|)). *)
     c [ncout; p_x; p_y];        (* cnf(i_0_10,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|)). *)
     c [ncout; p_x; cin];        (* cnf(i_0_11,plain,(~cout(X1,X2)|p_x(X1,X2)|cin(X1,X2))). *)
     c [ncout; p_x; cin];        (* cnf(i_0_12,plain,(~cout(X1,X2)|p_x(X1,X2)|cin(X1,X2)|)). *)
     c [ncout; p_y; cin];        (* cnf(i_0_13,plain,(~cout(X1,X2)|p_y(X1,X2)|cin(X1,X2))). *)
     c [ncout; p_y; cin];        (* cnf(i_0_14,plain,(~cout(X1,X2)|p_y(X1,X2)|cin(X1,X2))). *)
     c [ncout; p_x; p_y; cin];   (* cnf(i_0_15,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))). *)
     c [ncout; p_x; p_y; cin];   (* cnf(i_0_16,plain,(~cout(X1,X2)|p_x(X1,X2)|p_y(X1,X2)|cin(X1,X2))). *)

     c [cout; np_x; np_y];  (* cnf(i_0_17,plain,(cout(X1,X2)|~p_x(X1,X2)|~p_y(X1,X2))). *)
     c [cout; np_x; ncin];  (* cnf(i_0_18,plain,(cout(X1,X2)|~p_x(X1,X2)|~cin(X1,X2))). *)
     c [cout; np_y; ncin];  (* cnf(i_0_19,plain, (cout(X1,X2)|~p_y(X1,X2)|~cin(X1,X2))). *)  
   ]
  in
  let all_axs = cin_shl1_out_axioms@add_axioms in
  all_axs


(* ------- sub_axs ---------*)

(* s = x - y iff x = s + y *) 

let create_bv_sub_axs bv_domain sub_res_symb sub_arg_symbs = 
  let (p_x_symb, p_y_symb) = get_pair_from_list sub_arg_symbs in

(* since x can participate in e.g. several substructions we need a new symbol for s+y otherwise clash *)
(* in derived auxilary sumbols like in/out/trigger *)
  let aux_str_add_symb = 
    ((Symbol.to_string p_x_symb)^"_plus_"^(Symbol.to_string p_x_symb)) in
  let add_symb = bv_create_aux_symb sub_res_symb aux_str_add_symb in

(* add_axs*)
  let add_axs = create_bv_add_axs bv_domain add_symb  [sub_res_symb; p_y_symb] in

  let add = bv_create_var_atom add_symb in
  let p_x = bv_create_var_atom p_x_symb in
  
  let nadd = add_neg_atom add  in
  let np_x = add_neg_atom p_x in
  
  let c lits =  create_clause Clause.tstp_source_axiom_bv_sub lits in
  let sub_axs = 
    [
      
  (* add <-> p_x *)
     c [nadd; p_x];
     c [add;np_x];
   ]
  in
 let all_axs = add_axs@sub_axs in 
(* old: without new syb *) 
(* let all_axs = create_bv_add_axs bv_domain p_x_symb  [sub_res_symb; p_y_symb] in *)
  all_axs

  (* create_bv_add_axs bv_domain p_x_symb  [sub_res_symb; p_y_symb] *)

(*
  let bv_add_name = Symbol.add_iprover_pref ("bv_add_"^(get_base_name_symb sub_res_symb)) in
  let bv_add_symb = create_bv_symb (is_state_dep_bv_symb sub_res_symb) bv_add_name in
*)  


(*---------- p >/< q ------------*)

(* is_ugt flag is true if bvugt ">" and false if bvult "<" *)

let bv_bvugt_bvult_axs ~is_ugt bv_domain res_symb arg_symbs = 

(* symbols *)
  let (p_x_symb, p_y_symb) = get_pair_from_list arg_symbs in

  let trigger_in_symb = bv_create_aux_symb res_symb "bv_trigger_in" in 
  let trigger_out_symb = bv_create_aux_symb res_symb "bv_trigger_out" in 
  let res_in_symb = bv_create_aux_symb res_symb "bv_res_in" in 
  let res_out_symb = bv_create_aux_symb res_symb "bv_res_out" in 

(* axioms part 1*)

(* t_in = right_shift t_out *)
  let t_in_shr_out_axioms = bv_shr1_axs bv_domain trigger_in_symb [trigger_out_symb] in

(*r_in = right_shift r_out *)
  let r_in_shr_out_axioms = bv_shr1_axs bv_domain res_in_symb [res_out_symb] in

(* literals *)

  let p_x = bv_create_var_atom p_x_symb in
  let p_y = bv_create_var_atom p_y_symb in
  let r_in = bv_create_var_atom res_in_symb in
  let r_out = bv_create_var_atom res_out_symb in
  let t_in = bv_create_var_atom trigger_in_symb in
  let t_out = bv_create_var_atom trigger_out_symb in
  let res = bv_create_var_atom res_symb in

  let np_x = add_neg_atom p_x in
  let np_y = add_neg_atom p_y in
  let nr_in = add_neg_atom r_in in
  let nr_out = add_neg_atom r_out in
  let nt_in = add_neg_atom t_in in
  let nt_out = add_neg_atom t_out in
  let nres = add_neg_atom res in

(* for the final result we need r_out(X0_state, bind0) denoted r_out_ind0 *)
  let state_v0 = state_var_term 0 in
  let bit_ind0 = (bit_index_term 0) in
  let r_out_ind0  = create_bv_atom res_out_symb state_v0 bit_ind0 in      
  let nr_out_ind0 = add_neg_atom r_out_ind0 in 
  let tstp_source = 
    if is_ugt 
    then 
      Clause.tstp_source_axiom_bv_bvugt 
    else 
      Clause.tstp_source_axiom_bv_bvult 
  in
  let c lits = create_clause tstp_source lits in

  let cmp_axioms = 
    [ (* p is p_x and q is p_y *)    

(* \forall s \forall i [ ([p(s,i) <=>  ~q(s,i)] \orl t_in(s,i))=> t_out(s,i)]  (* trigger_out changed *) *)

     c [np_x; p_y; t_out];  (* 1. ~p(s,i) \/  q(s,i) \/ t_out(s,i) *)
     c [p_x; np_y; t_out];  (* 2. p(s,i) \/  ~q(s,i) \/ t_out(s,i) *)
     c [nt_in; t_out];      (* 3. ~t_in(s,i) \/ t_out(s,i) *)
     
(* \forall s \forall i [ ((p(s,i) <=>  q(s,i)) & \notl t_in(s,i)) => ~ t_out(s,i)] (* trigger_out unchanged *) *)

     c [np_x; np_y; t_in; nt_out];  (* 1. ~p(s,i) \/ ~q(s,i) \/t_in(s,i) \/ ~ t_out(s,i) *)
     c [p_x; p_y; t_in; nt_out];  (* 2. p(s,i) \/ q(s,i) \/t_in(s,i) \/ ~ t_out(s,i)   *)

(* ugt \forall s \forall i [ (~t_in(s,i) & t_out(s,i) & p(s,i) & ~q(s,i)) => r_out(s,i)]] (* first change in p,q; res true *) *)
(* lgt \forall s \forall i [ (~t_in(s,i) & t_out(s,i) & ~p(s,i) & q(s,i)) => r_out(s,i)]] (* first change in p,q; res true *) *)
      (if is_ugt 
      then
	c [t_in; nt_out; np_x; p_y; r_out]  (* ugt t_in(s,i) \/ ~t_out(s,i) \/ ~p(s,i) \/ q(s,i) \/ r_out(s,i) *)
      else
	c [t_in; nt_out; p_x; np_y; r_out]  (* lgt t_in(s,i) \/ ~t_out(s,i) \/ p(s,i) \/ ~q(s,i) \/ r_out(s,i) *)
      );
      
 (* ugt \forall s \forall i [ (~t_in(s,i) & t_out(s,i) & ~p(s,i) & q(s,i)) => ~r_out(s,i)] (* first change in p,q; res false *) *)
 (* lgt \forall s \forall i [ (~t_in(s,i) & t_out(s,i) &  p(s,i) & ~q(s,i)) => ~r_out(s,i)] (* first change in p,q; res false *) *)
      (if is_ugt
      then 
	c [t_in; nt_out; p_x; np_y; nr_out]  (* ugt t_in(s,i) \/ ~t_out(s,i) \/ p(s,i) \/ ~q(s,i) \/ ~r_out(s,i) *)
      else
	c [t_in; nt_out; np_x; p_y; nr_out]  (* lgt t_in(s,i) \/ ~t_out(s,i) \/ ~p(s,i) \/ q(s,i) \/ ~r_out(s,i) *)
      );

    (* \forall s \forall i [ (t_in(s,i) & t_out(s,i)) => (r_in(s,i) <=>r_out(s,i))] (* preserve the result*) *)

      c [nt_in; nt_out; nr_in; r_out];   (* 1. ~t_in(s,i) \/ ~t_out(s,i) \/ ~r_in(s,i) \/ r_out(s,i) *)
      c [nt_in; nt_out; r_in; nr_out]; (* 2. ~t_in(s,i) \/ ~t_out(s,i) \/  r_in(s,i) \/ ~r_out(s,i) *)
      
      c [t_out;nr_out];  (* \forall s \forall i [ ~t_out(s,i) => ~r_out(s,i)]  (* trigger_out not_changed; *) *)
       
    (* \forall s (r_out(s,ind0) <=>res_pq(s)) (* final result *) *)

     c [nr_out_ind0; res];  (* 1. ~r_out(s,ind0) \/ res_pq(s) *)
     c [r_out_ind0; nres]; (* 2. r_out(s,ind0) \/ ~res_pq(s) *)     
   
    ]
  in
  let all_axs = t_in_shr_out_axioms @ r_in_shr_out_axioms @ cmp_axioms in
  all_axs


(*----- p = q ------*)

let bv_bveq_axs bv_domain res_symb arg_symbs = 

  out_str " \n\n\n p=q\n\n\n";
(* symbols *)
  let (p_x_symb, p_y_symb) = get_pair_from_list arg_symbs in

  let trigger_in_symb = bv_create_aux_symb res_symb "bv_trigger_in" in 
  let trigger_out_symb = bv_create_aux_symb res_symb "bv_trigger_out" in 

(* literals *)

  let p_x = bv_create_var_atom p_x_symb in
  let p_y = bv_create_var_atom p_y_symb in
  let t_in = bv_create_var_atom trigger_in_symb in
  let t_out = bv_create_var_atom trigger_out_symb in
  let res = bv_create_var_atom res_symb in

  let np_x = add_neg_atom p_x in
  let np_y = add_neg_atom p_y in
  let nt_in = add_neg_atom t_in in
  let nt_out = add_neg_atom t_out in
  let nres = add_neg_atom res in

(* axioms part 1*)

(* t_in = right_shift t_out *)
  let t_in_shr_out_axioms = bv_shr1_axs bv_domain trigger_in_symb [trigger_out_symb] in

(* for the final result we need t_out(X0_state, bind0) denoted t_out_ind0 *)
  let state_v0 = state_var_term 0 in
  let bit_ind0 = (bit_index_term 0) in
  let t_out_ind0  = create_bv_atom trigger_out_symb state_v0 bit_ind0 in      
  let nt_out_ind0 = add_neg_atom t_out_ind0 in 

  let tstp_source = Clause.tstp_source_axiom_bv_bveq in
  let c lits = create_clause tstp_source lits in
  let eq_axioms = 
    [ (* p is p_x and q is p_y *)    
      
(* \forall s \forall i [ ((p(s,i) <=>  ~q(s,i)) \orl t_in(s,i))=> t_out(s,i)]  (* trigger_out changed *) *)
      
      c [np_x; p_y; t_out];  (* 1. ~p(s,i) \/  q(s,i) \/ t_out(s,i) *)
      c [p_x; np_y; t_out];  (* 2. p(s,i) \/  ~q(s,i) \/ t_out(s,i) *)
      c [nt_in; t_out];      (* 3. ~t_in(s,i) \/ t_out(s,i) *)
      
(* \forall s \forall i [ ((p(s,i) <=>  q(s,i)) & \notl t_in(s,i)) => ~ t_out(s,i)] (* trigger_out unchanged *) *)

      c [np_x; np_y; t_in; nt_out];  (* 1. ~p(s,i) \/ ~q(s,i) \/t_in(s,i) \/ ~ t_out(s,i) *)
      c [p_x; p_y; t_in; nt_out];    (* 2. p(s,i) \/ q(s,i) \/t_in(s,i) \/ ~ t_out(s,i)   *)

(* \forall s [~t_out(s,ind0) <-> eq_p_q(s)] (* eq def. *) *)

      c [t_out_ind0; res]; (* 1. t_out(s,ind0)\/ eq_p_q(s) *)
      c [nt_out_ind0; nres];(*  2. ~t_out(s,ind0)\/ ~eq_p_q(s) *)
    ]
  in
  let all_axioms = t_in_shr_out_axioms@eq_axioms in
  all_axioms


(*---------- p >=/<= q ------------*)

let bv_bvuge_bvule_axs ~is_uge bv_domain res_symb arg_symbs =

(* symbols *)

  let bv_strict_cmp_symb = 
    if is_uge 
    then
      bv_create_aux_symb res_symb "bv_bvugt" 
    else
      bv_create_aux_symb res_symb "bv_bvult" 
  in 

  let bv_eq_symb = bv_create_aux_symb res_symb "bv_bveq" in 

(* literals *)
 
  let scmp = bv_create_var_atom bv_strict_cmp_symb in 
  let eq = bv_create_var_atom bv_eq_symb in
  let res = bv_create_var_atom res_symb in
  
  let nscmp = add_neg_atom scmp in
  let neq = add_neg_atom eq in
  let nres = add_neg_atom res in

(* axioms scmp_axs *)
  let scmp_axs = bv_bvugt_bvult_axs ~is_ugt:is_uge bv_domain bv_strict_cmp_symb arg_symbs in
  
(* axioms eq_axs *) 
  let eq_axs = bv_bveq_axs bv_domain bv_eq_symb arg_symbs in

  let tstp_source = 
    if is_uge 
    then
      Clause.tstp_source_axiom_bv_bvuge 
    else
      Clause.tstp_source_axiom_bv_bvule 
  in
  let c lits = create_clause tstp_source lits in

  let res_axs = 
    [
     (* \forall s [bvuge(s) <-> (bvugt_pq(s) \/ eq_p_q(s))] *)

     c [nres; scmp; eq];  (* 1. ~bvuge(s) \/ bvugt_pq(s) \/ eq_p_q(s) *)
     c [res; nscmp];      (* 2. bvuge(s) \/ ~bvugt_pq(s) *)
     c [res; neq];        (* 3. bvuge(s) \/ ~eq_p_q(s) *)
   ]
  in
  let all_axs = scmp_axs@eq_axs@res_axs in
  all_axs

(*--- bv all axioms ----*)
(*
let bv_get_size bv_symb = 
  try
    SMap.find bv_symb !bv_symb_map 
  with Not_found -> 
    failwith ("not found size of a bit-vector operation symbol: "^(Symbol.to_string bv_symb))
*)

let get_bv_axioms () =
  fill_bv_domain_map ();
  let succ_axioms = get_succ_axioms () in

(* debug *)
(*
  out_str (" \n\n bv op succ axioms : \n"
	   ^"-------------\n\n"
	   ^(Clause.clause_list_to_string succ_axioms)^"\n\n"
	   ^ "-------------\n\n");
*)
(* debug *)
  let get_bv_op_axioms create_bv_axs_fun res_symb arg_name_list = 
    let find_symb symb_name = 
      try
	find_symbol symb_name
      with Not_found -> 
	failwith ("symbol was not declared: "^(Symbol.to_string res_symb))
    in
    let arg_symb_list = List.map find_symb arg_name_list in
(* size of the res_symb can be different from the size of the arguments -- *)
(* in comaprisions the size of the result is 1 *)
(* we assume that the size of the arguments is equal and of required size *)
    let size = 
      match arg_symb_list with 
      |[symb1; symb2] -> 
	  let size1 = bv_get_size symb1 in 
	  let size2 = bv_get_size symb2 in
	  if size1 = size2 
	  then 
              size1 
	  else
	    failwith 
	      ("arguments of bv operation: "^(Symbol.to_string res_symb)^" have different sizes: "
	       ^(Symbol.to_string symb1)^" size: "^(string_of_int size1)^"; " 
	       ^(Symbol.to_string symb2)^" size: "^(string_of_int size2))

      |[symb] -> bv_get_size symb

      |_-> failwith ("bv operation: "^(Symbol.to_string res_symb)^" should have two arguments ")
    in
    let max_index = size -1 in 
    let bv_domain = IntMap.find max_index !bv_domain_map in
    create_bv_axs_fun bv_domain res_symb arg_symb_list         
  in
  let get_bv_op_fun bv_op = 
    match bv_op with 
    | Parser_types.BV_add -> create_bv_add_axs
    | Parser_types.BV_sub -> create_bv_sub_axs 
    | Parser_types.BV_bvugt -> (bv_bvugt_bvult_axs ~is_ugt:true)
    | Parser_types.BV_bvuge -> (bv_bvuge_bvule_axs ~is_uge:true)
    | Parser_types.BV_bvult -> (bv_bvugt_bvult_axs ~is_ugt:false)
    | Parser_types.BV_bvule -> (bv_bvuge_bvule_axs ~is_uge:false)
    | Parser_types.BV_bveq ->  bv_bveq_axs 
    | Parser_types.BV_shl1 -> bv_shl1_axs
    | Parser_types.BV_shr1 -> bv_shr1_axs
(* failwith "bv operations: BV_bvugt, BV_bvuge, BV_bvult, BV_bvule, BV_bveq are not yet supported" *)
  in  	
  let f bv_op bv_symb_arg_names_map rest_bv_op_ax =
    let create_bv_axs_fun = get_bv_op_fun bv_op in
    let g res_symb arg_list rest_axs = 
      let new_axs = get_bv_op_axioms create_bv_axs_fun res_symb arg_list in
(* debug *)

      out_str (" \n\n bv op "^(Parser_types.bv_op_to_str bv_op)^" res symb: "^(Symbol.to_string res_symb)^"\n"
	       ^"-------------\n\n"
	       ^(Clause.clause_list_to_string new_axs)^"\n\n"
	       ^ "-------------\n\n");

(* debug *)
      (new_axs@rest_axs)
    in
    SMap.fold g bv_symb_arg_names_map rest_bv_op_ax
  in
  let all_bv_op_axioms =  Parser_types.BV_OP_Htbl.fold f bv_op_htbl [] in
  let all_axs =
    if all_bv_op_axioms != [] then      
      succ_axioms@all_bv_op_axioms 
    else
      []
  in
  all_axs
  
(* *)
(*
let get_bv_axioms () =
  try 
  fill_bv_domain_map ();
  let succ_axioms = get_succ_axioms () in
(*-- bv_add axioms -*)
  let f add_symb (p_x_name,p_y_name) rest = 
    let p_x_symb = find_symbol p_x_name in
    let p_y_symb = find_symbol p_y_name in   
    let size = SMap.find add_symb !bv_symb_map in
    let max_index = size -1 in 
    let bv_domain = IntMap.find max_index !bv_domain_map in
    let add_axs = create_bv_add_axs bv_domain.bv_succ_symb p_x_symb p_y_symb add_symb in 
  (*  out_str ((Clause.clause_list_to_string add_axs)^"\n\n");*)
    add_axs@rest
  in
  let add_axioms = SMap.fold f !bv_add_map [] in

(*-- bv_sub axioms --*)
  let f sub_symb (p_x_name,p_y_name) rest = 
    let p_x_symb = find_symbol p_x_name in
    let p_y_symb = find_symbol p_y_name in   
    let size = SMap.find sub_symb !bv_symb_map in
    let max_index = size -1 in 
    let bv_domain = IntMap.find max_index !bv_domain_map in
    let sub_axs = create_bv_sub_axs bv_domain.bv_succ_symb p_x_symb p_y_symb sub_symb in 
  (*  out_str ((Clause.clause_list_to_string sub_axs)^"\n\n"); *)
    sub_axs@rest
  in
  let sub_axioms = SMap.fold f !bv_sub_map [] in
  let all_axioms = succ_axioms@add_axioms@sub_axioms in 
(*  out_str ("All add/sub axioms:"^(Clause.clause_list_to_string all_axioms)^"\n\n");*)
  all_axioms

  with Not_found -> failwith "get_bv_axioms_test: Not_found"
*) 

 
(*
  out_str ("\n\n Succ axioms:\n "^(Clause.clause_list_to_string succ_axioms)^"\n\n");
  let test_shift_fun bv_symb size =     
    let max_index = size -1 in 
    let bv_domain = IntMap.find max_index !bv_domain_map in  
    let shift_symb = create_bv_shift_symb (get_base_name_symb bv_symb) in 
    let shift_axs = bv_shl1_axs bv_domain.bv_succ_symb shift_symb bv_symb in
    out_str ("shift ax for: "^(Symbol.to_string bv_symb)^"\n\n");
    out_str ((Clause.clause_list_to_string shift_axs)^"\n\n")
  in
  SMap.iter test_shift_fun !bv_symb_map;
  out_str ("\n\n BV addition axioms: \n\n");
  try
  let f add_symb (p_x_name,p_y_name) = 
    let p_x_symb = create_bv_symb p_x_name in
    let p_y_symb = create_bv_symb p_y_name in   
    let size = SMap.find add_symb !bv_symb_map in
    let max_index = size -1 in 
    let bv_domain = IntMap.find max_index !bv_domain_map in
    let add_axs = create_bv_add_axs bv_domain.bv_succ_symb p_x_symb p_y_symb add_symb in 
    out_str ((Clause.clause_list_to_string add_axs)^"\n\n");
  in
  SMap.iter f !bv_add_map  
  with Not_found -> failwith "get_bv_axioms_test: Not_found"
*)

(* assume that bit_index list is of the form [0;..; max_bit_index] and succ_sumbol corresponds to max_bit_index *)
(*let create_succ_axioms succ_symb bit_index_list = *)
  

(*----------------Commented Below---------------------*)

(*
(*---------------------*)
(* returns ([v_1;..;v_n],[v'_1;...;v'_n]) to be used in congruence axioms*)
  let rec get_two_vlists current_var n =
  if n = 0 then ([],[])
  else
  let next_var = Var.get_next_var current_var in
  let new_current_var = Var.get_next_var next_var in
  let (rest1, rest2) = get_two_vlists new_current_var (n -1) in
  ((term_var current_var):: rest1, (term_var next_var):: rest2)

  exception Arity_non_positive
  let congr_axiom symb =
  let arity = Symbol.get_arity symb in
  if arity <= 0 then raise Arity_non_positive
  else
  (let (vlist1, vlist2) = get_two_vlists v0 arity in
  let var_dis_part =
  List.rev_map2 dis_equality vlist1 vlist2
  in
  match (Symbol.get_type symb)
  with
  | Symbol.Fun ->
  let pos_part =
  let t = add_fun_term symb vlist1 in
  let s = add_fun_term symb vlist2 in
  equality_term t s
  in
  let fun_congr_ax =
  Clause.normalise term_db_ref
  (Clause.create (pos_part:: var_dis_part)) in
  assign_eq_ax_param fun_congr_ax;
  fun_congr_ax
  | Symbol.Pred ->
  let pred = add_fun_term symb vlist1 in
  let neg_pred = neg_atom (add_fun_term symb vlist2) in
  let pred_congr_ax =
  Clause.normalise term_db_ref
  (Clause.create (pred:: neg_pred:: var_dis_part))
  in
  assign_eq_ax_param pred_congr_ax;
  pred_congr_ax
  | _ -> failwith "eq_axioms: no congr_axiom for this type of symb "
  )

  let congr_axiom_list () =
  let f symb rest =
  if ((Symbol.is_input symb) & (not (symb == Symbol.symb_equality)))
  then
  match (Symbol.get_type symb) with
  | Symbol.Fun | Symbol.Pred ->
  if (Symbol.get_arity symb) >0
  then
  (congr_axiom symb):: rest
  else rest
  | _ -> rest
  else rest
  in
  SymbolDB.fold f !symbol_db_ref []

  let axiom_list () =
(*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  if (Symbol.is_input equality_symb)
  then
  let cong_ax_list = congr_axiom_list () in
  (reflexivity_axiom ()):: (trans_symmetry_axiom ()):: cong_ax_list
  else []

 *)
(*
  let sym_set = ref SSet.empty in
  let eq_type_set = ref SSet.empty in
  let rec get_type_eq_set_form_term t =
  match t with
  | Term.Fun(symb, args, _) ->
  let relevant_args =
  if (symb == Symbol.symb_typed_equality)
  then
  (
  let (eq_type, t1, t2) =
  get_triple_from_list (Term.arg_to_list args) in
  let eq_type_sym = Term.get_top_symb eq_type in
  eq_type_set:= SSet.add eq_type_sym !eq_type_set;
  Term.list_to_arg [t1; t2]
  )
  else
  (sym_set := SSet.add symb !sym_set;
  args
  )
  in
  Term.arg_iter get_type_eq_set_form_term relevant_args
  | Term.Var _ -> ()
  in
  let get_type_eq_set_form_lit lit =
  get_type_eq_set_form_term (Term.get_atom lit)
  in
  let get_type_eq_set_form_cl cl = Clause.iter get_type_eq_set_form_lit cl in
  List.iter get_type_eq_set_form_cl clause_list;
  (!sym_set,!eq_type_set)
 *)

(*

  let get_type_eq_term t =
  match t with
  | Term.Fun(symb, args, _) ->
  if (symb == Symbol.symb_typed_equality)
  then
  (
  match (Term.arg_to_list args) with
  | stype_term:: _ ->
  (match stype_term with
  | Term.Fun(stype_symb, args, _) -> Some stype_symb
  | _ -> failwith
  ("get_type_eq_term shouldn't happen" ^ Term.to_string t)
  )
  | _ -> failwith
  ("get_type_eq_term shouldn't happen\n" ^ Term.to_string t)
  )
  else
  None
  | _ -> None
 *)

(*
  let typed_congr_axiom_list () =
  let eq_type_table = SymbTbl.create 101 in

  let collect_essential_stypes = function

(* Symbol is a theory symbol (not a type symbol) that occurs in an
   input term *)
  | symb when
  (Symbol.is_essential_input symb) &&
  not (symb == Symbol.symb_typed_equality) ->

  (

(* Get type of arguments and type of result of symbol *)
  match Symbol.get_stype_args_val symb with

(* Type of arguments and result determined *)
  | Def (a, v) ->

(* Add all types to table of types except bool type $o *)
  List.iter
  (function

(* Do not generate axioms for bool type $o *)
  | s when (s == Symbol.symb_bool_type) -> ()

(* Generate axioms for all other types *)
  | s ->

(* Symbol not in table? *)
  if not (SymbTbl.mem eq_type_table s) then

(* Add symbol to table of types *)
  SymbTbl.add eq_type_table s s

  )
  (v :: a)

(* Skip if type is not known *)
  | Undef -> ()

  )

(* Symbol is declared only, but does not occur *)
  | _ -> ()

  in

(* Iterate symbol table to find types to generate axioms for *)
  SymbolDB.iter collect_essential_stypes !symbol_db_ref;

  out_str ("Types to generate congruence axioms for:\n");
  SymbTbl.iter
  (fun s _ -> out_str (Symbol.to_string s))
  eq_type_table;
 *)

(* It is not enough to consider the types in equations only, must
   take the types of all symbols in the input as above *)
(*
(* for $equality_sorted(type, t,s) add type to symb_table *)
  let add_eq_type t =

  match (get_type_eq_term t) with
  | Some symb ->
  if (Symbol.is_essential_input symb)
  then
  (SymbTbl.add eq_type_table symb symb)
  else ()
  | None -> ()
  in
  TermDB.iter add_eq_type !term_db_ref;

  let f symb rest =
  out_str ("eq_ax: "
  ^(Symbol.to_string symb)
  ^" is_essential_input: "
  ^(string_of_bool (Symbol.is_essential_input symb))
  ^" Symbol.is_signature_symb: "
  ^(string_of_bool (Symbol.is_signature_symb symb))^"\n");
  if
  (
  (Symbol.is_essential_input symb)
  &&
  (not (symb == Symbol.symb_typed_equality))
  &&
  (Symbol.is_signature_symb symb)
(* &&
(* We don't need congruence axioms for less and range symbols !*)
(* but slower that with the axioms... *)
   (not (is_less_range symb)) *)
  )
  then
  (
  match (typed_congruence_axiom eq_type_table symb) with
  | Some ax ->
  out_str ("ax: "^(Clause.to_string ax)^"\n --------------\n");
  ax:: rest
  | None -> rest
  )
  else rest
  in
  SymbolDB.fold f !symbol_db_ref []

(*
  out_str "\n----------------get_type_eq_term-------\n";
  out_str ((Symbol.to_string symb)^"\n");
 *)

 *)

(*
  let axiom_list () =
(*  out_str_debug (SymbolDB.to_string !symbol_db_ref);*)
  if (Symbol.is_essential_input Symbol.symb_typed_equality)
  then
  (
  let typed_cong_ax_list = typed_congr_axiom_list () in
  (typed_reflexivity_axiom ()):: (typed_trans_symmetry_axiom ()):: typed_cong_ax_list)
  else []
 *)
