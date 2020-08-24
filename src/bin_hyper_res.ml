(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2017 Konstantin Korovin and The University of Manchester. 
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

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_merge_def
  | D_impl_unit
  | D_mbd
  | D_in_out
  | D_tr_red

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_merge_def -> "merge_def"
  | D_impl_unit -> "impl_unit"
  | D_mbd -> "mbd"
  | D_in_out -> "in_out"
  | D_tr_red -> "tr_red"

let dbg_groups =
  [
   D_trace; 
   D_merge_def;
   D_impl_unit; 
   D_mbd;
   D_in_out; 
   D_tr_red;
 ]
    
let module_name = "bin_hyper_res"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)



(*--------------- SCC based on binary clauses -----------------------*)

(* module DGS = Graph.Imperative.Digraph.Concrete(Term.Key) *)

module DGS = Graph.Persistent.Digraph.Concrete(Term.Key) 

(* Strongly connected component *)
module DGS_SCC = Graph.Components.Make(DGS)

(* Basic graph operations; use for transitive reduction *)
 module DGS_OPER = Graph.Oper.P(DGS) 


(*  normilise terms by a map t -> s where s is a SCC represtative of [t] *)

(* init with binary clauses*)
(* for each clause a \/ b adds nodes ~a -> b; ~b -> a *)
let add_binary_clauses_bhr_graph bhr_graph clause_list  = 
  let f bhrg_rest c = 
    match (Clause.get_literals c) with 
    |[l1;l2] -> 
        let bhrg_1 = DGS.add_edge bhrg_rest (add_compl_lit l1) l2 in 
        let bhrg_2 = DGS.add_edge bhrg_1    (add_compl_lit l2) l1 in 
        bhrg_2          
    |_ -> bhrg_rest 
  in
  List.fold_left f bhr_graph clause_list

let init_bhr_graph clause_list = 
  add_binary_clauses_bhr_graph DGS.empty clause_list


(*--- init with impled lits (implied binary clauses) ---*)

(* TODO: check when solver (or solver_sim) has assumptions like in BMC or finite models *)

(*
exception Impl_Unit of term

let get_all_ass_implied_lit_but_first asserted_lit = 
  let impl_lits = ref [] in 
  dbg D_impl_unit (lazy ("asseretd lit: "^(Term.to_string asserted_lit)));
  try 
    begin

        let first_impl = 
          try
            Prop_solver_exchange.get_next_ass_implied_unit ~solver_in:Prop_solver_exchange.solver_sim  (* skip asserted *)
          with 
            Not_found ->  
              (
               (* can happen if  asserted_lit is implied without assumptions *)
               let compl_asserted_lit = add_compl_lit asserted_lit in 
               match (Prop_solver_exchange.fast_solve ~solver_in:Prop_solver_exchange.solver_sim [compl_asserted_lit]) with
               | PropSolver.FUnsat ->

                   raise (Impl_Unit(asserted_lit))

               | PropSolver.FSat | PropSolver.FUnknown ->
                   (
                    failwith "get_all_ass_implied_lit_but_first: asserted_lit is not in the impl units"
                   )
              )
        in
        
        (if (not (asserted_lit == first_impl))
        then 
          failwith ("get_all_ass_implied_lit_but_first: asseted literal in not the first implied: "
                    ^("assereted: "^(Term.to_string asserted_lit)^" first implied: "^(Term.to_string first_impl))
                   )
        );
        while true 
        do 
          try
            let next_unit = Prop_solver_exchange.get_next_ass_implied_unit ~solver_in:Prop_solver_exchange.solver_sim in
            dbg D_impl_unit (lazy ("next_unit: "^(Term.to_string next_unit)));
            Term.type_check next_unit;
            impl_lits:= next_unit::(!impl_lits)
          with 
            Term.Type_check_failed -> ()
        done; 
        !impl_lits
    end
  with     
    Not_found -> !impl_lits
    

let collect_all_implied_lit lit = 
  match (Prop_solver_exchange.fast_solve ~solver_in:Prop_solver_exchange.solver_sim [lit]) with
  | PropSolver.FUnsat ->
      (
       let compl_lit = add_compl_lit lit in 
       raise (Impl_Unit(compl_lit))
      )
  | PropSolver.FSat | PropSolver.FUnknown ->
      (get_all_ass_implied_lit_but_first lit)
*)

(*
let get_all_atoms clause_list = 
  let f atom_set lit = TSet.add (Term.get_atom lit) atom_set in 
  let g atom_set c = 
    let lits = Clause.get_lits c in 
    List.fold_left f atom_set lits 
  in
  List.fold_left g TSet.empty clause_list
*)

(* can raise Impl_Unit(lit) *)    
let add_impl_bhr_graph_lit is_eligible_impl bhr_graph lit = 
  let impl_lits = Implied_units.all_implied_lits lit in 
  let f bhr_graph_rest impl_lit = 
    if (is_eligible_impl impl_lit) 
    then
      let bhrg_1 = DGS.add_edge bhr_graph_rest lit impl_lit in
      let bhrg_2 = DGS.add_edge bhrg_1 (add_compl_lit impl_lit) (add_compl_lit lit) in
      bhrg_2
    else
      (
       dbg D_impl_unit (lazy ("not eligible_impl: "^(Term.to_string impl_lit)));
       bhr_graph_rest
      )
  in
  List.fold_left f bhr_graph impl_lits
  
  
let init_prop_impl_bhr_graph clause_list = 

  List.iter Prop_solver_exchange.add_clause_to_solver clause_list;

 (* let impl_unit_lits = ref TSet.empty in *) (* includes all unit clauses in clause_list and impl_unit lits; they are added separately *)
  let atoms_of_impl_units = ref TSet.empty in (* atoms of implied units; we do not add them to the graph *)
  
  let (clauses_units, clauses_no_units) = List.partition (fun c -> (Clause.length c)  = 1 ) clause_list in

  dbg D_impl_unit (lazy ("unit clauses: "^(string_of_int (List.length clauses_units)
                                           ^" non-unit clauses: "^(string_of_int (List.length clauses_no_units)))));

  let atoms = Clause.get_atoms_clause_list clauses_no_units in

  let add_unit_clause c = 
    let unit_lit = get_singleton_from_list (Clause.get_literals c) in      
    atoms_of_impl_units := TSet.add (Term.get_atom unit_lit) !atoms_of_impl_units 
  in
  List.iter add_unit_clause clauses_units;
  
  let is_eligible_atom atom = 
    not (TSet.mem atom !atoms_of_impl_units)
  in
  let is_eligible_impl impl_lit = TSet.mem (Term.get_atom impl_lit) atoms in (* restrict to atoms in the problem *)
    
  let add_bhr_graph_atom bhr_graph atom = 
    if (is_eligible_atom atom)
    then 
      try
        let neg_atom = add_neg_atom atom in    
        let bhrg_1 = add_impl_bhr_graph_lit is_eligible_impl bhr_graph atom in 
        let bhrg_2 = add_impl_bhr_graph_lit is_eligible_impl bhrg_1 neg_atom in 
        bhrg_2
      with 
        Implied_units.Impl_Unit(lit) -> 
          atoms_of_impl_units := TSet.add (Term.get_atom lit) !atoms_of_impl_units;
          bhr_graph
    else
      (
       dbg D_impl_unit (lazy ("not is_eligible_atom: "^(Term.to_string atom)));
       bhr_graph
      )
  in
  TSet.fold (fun atom bhr_graph -> add_bhr_graph_atom bhr_graph atom) atoms DGS.empty
  

(* select a normal form a def equiv class represeneted as a list of literals *)
(* we assume:
   1) that with each eq class, there is a daul class where polarity of each literal is inversed 
   2) there is no complementary literals in the class 
      (this is guaranteed if the set was propositionally sat; or can be check separately)

  We select atom of the first literal from the class as normal nf
  For each literal (including nf) take its atom and add to the nf_atom_map 
  a -> +/-nf; this also includes nf->nf

*)

type nf_map = term TMap.t

let cmp_top_symb_term t1 t2 = 
  Symbol.compare (Term.get_top_symb t1) (Term.get_top_symb t2)
  

let nf_map_to_string nf_map = 
  let f atom nf rest = 
    let nf_str = (Term.to_string atom)^"->"^(Term.to_string nf) in 
    nf_str::rest
  in
  let nf_str_list = TMap.fold f nf_map [] in 
  String.concat "\n" nf_str_list 

(*---------------*)

let split_non_recursive_defs lit_list = (* recursive: if top occurs more than 2 times *)
  let f (non_rec_defs_map, rec_defs_map) lit = (* non_rec: top -> term; rec: top -> term_list *)
    let top_symb = Term.lit_get_top_symb lit in 
    try 
      let rec_list = SMap.find top_symb rec_defs_map in 
      let new_rec_defs_map = SMap.add top_symb (lit::rec_list) rec_defs_map in 
      (non_rec_defs_map, new_rec_defs_map)
    with 
      Not_found -> 
        begin
          try    
            let old_lit = SMap.find top_symb non_rec_defs_map in             
            let new_non_rec_defs_map = SMap.remove top_symb non_rec_defs_map in   
            let new_rec_defs_map = SMap.add top_symb ([lit;old_lit]) rec_defs_map in 
            (new_non_rec_defs_map, new_rec_defs_map)
          with 
            Not_found -> 
              let new_non_rec_defs_map = SMap.add top_symb lit non_rec_defs_map in   
              (new_non_rec_defs_map, rec_defs_map)
        end
  in
  let (non_rec_defs_map, rec_defs_map) = List.fold_left f (SMap.empty, SMap.empty) lit_list in 

  let non_rec_defs_list = 
    let f top lit rest = lit::rest in
    SMap.fold f non_rec_defs_map []
  in
  let rec_defs_list = 
    let f top lit_list rest = lit_list@rest in 
    SMap.fold f rec_defs_map []
  in
  (non_rec_defs_list, rec_defs_list)


let select_nf def_equiv = 
  (* TODO experiment with different nf *)
  
(*  let nf_priority = [Lit_Prop true; Lit_Ground true; Lit_Num_of_Symb false] in *)

(*  let nf_priority = [Lit_Prop true; Lit_Ground true; Lit_Num_of_Var false; Lit_Num_of_Symb false;] in *)

(*  let nf_priority = [Lit_Prop true; Lit_Ground true; Lit_eq false;  Lit_Num_of_Var false; Lit_Num_of_Symb false;] in *)
 
  let nf_priority = [Lit_Prop true;  Lit_Ground true; Lit_eq false; Lit_Atom_depth false; Lit_Num_of_Symb false; Lit_Num_of_Var false;] in 

  let lit_cmp_fun_list = (List.map Term.lit_cmp_type_to_fun nf_priority)@[cmp_top_symb_term; Term.compare] in 
  let cmp_fun_atom = lex_combination lit_cmp_fun_list in 

(*  let cmp_fun_atom = (Term.lit_cmp_type_list_to_lex_fun nf_priority) in *)

  let cmp_lit l1 l2 = cmp_fun_atom (Term.get_atom l1) (Term.get_atom l2) in 
  list_find_max_element cmp_lit def_equiv
    

let use_rec_defs_flag = true
(* SW
let _ = out_warning ("use_rec_defs_flag: "^(string_of_bool use_rec_defs_flag))
*)

(* def_class_list is list of literals in the definition class *)
let extend_nf_map nf_map def_equiv = 
  let def_equiv_elig_nf = 
    let (non_rec_defs_list, rec_defs_list) = split_non_recursive_defs def_equiv in 
    dbg D_merge_def (lazy ("non_rec: "^(Term.term_list_to_string non_rec_defs_list)
                           ^" rec: "^(Term.term_list_to_string rec_defs_list)));             
    let non_rec_defs_no_eq = List.find_all (fun lit -> not (Term.is_eq_lit lit)) non_rec_defs_list in
    if (use_rec_defs_flag)
    then
      (
       if (non_rec_defs_no_eq != []) 
       then 
         non_rec_defs_no_eq
       else
         def_equiv
      )
    else
      non_rec_defs_list
  in
  match def_equiv with 
  |[] | [_] -> nf_map 
(*  |nf_lit::tl -> *)
  | _ when (def_equiv_elig_nf = []) -> nf_map
  | _ -> 

 (* two or more *)
 (* TODO: selet good nf: say max lit in some ordering *)
                  (* tl is not empty here *)

     
(* we can use both recursive and non-recursive *)
(*      let defs_to_use = if (non_rec_defs_list = []) then rec_defs_list else non_rec_defs_list in *)
      

      let nf_lit = select_nf def_equiv_elig_nf in
      let (nf_pol, nf_atom) = Term.split_sign_lit nf_lit in 
      if (TMap.mem nf_atom nf_map) 
      then
        nf_map (* we already considered the dual class *)
      else
        begin
          let nf_compl_atom = add_compl_lit nf_atom in 
          (
           dbg D_merge_def (lazy ("--------- def_equiv -------- "));
           
           dbg D_merge_def (lazy (" nf: "^(Term.to_string nf_lit)^" ["^(Term.term_list_to_string def_equiv)^"]\n"));
           
          );
          let f rest_nf_map def_lit = 
            let (def_pol, def_atom) = Term.split_sign_lit def_lit in 
            assert 
              (
               if (def_atom == nf_atom) 
               then 
                 def_pol = nf_pol 
               else 
                 (true)
            );
            if (nf_pol = def_pol)
            then           
              (
               dbg D_merge_def (lazy (" def_atom: "^(Term.to_string def_atom)^" -> nf_atom "^(Term.to_string nf_atom)));
               TMap.add def_atom nf_atom rest_nf_map
              )
            else
              (
               dbg D_merge_def (lazy (" def_atom: "^(Term.to_string def_atom)^" -> nf_compl_atom "^(Term.to_string nf_compl_atom)));
               TMap.add def_atom nf_compl_atom rest_nf_map
              )
          in
          List.fold_left f nf_map def_equiv
        end

(*----------  simple definition application ---------------------*)

let apply_nf_map_to_lit nf_map lit = 
  let (pol, atom) = Term.split_sign_lit lit in 
  try 
    let nf_lit = TMap.find atom nf_map in 
    let (nf_pol, nf_atom) = Term.split_sign_lit nf_lit in 
    if nf_atom == atom  (* atom is already notmalised *)
    then
      lit 
    else
      if pol = nf_pol 
      then
        nf_atom
      else
        add_compl_lit nf_atom
  with 
    Not_found -> lit


let apply_nf_map_to_clause nf_map clause = 
  let old_lits = Clause.get_literals clause in 
  let is_changed = ref false in 
  let f rest lit = 
    let new_lit = apply_nf_map_to_lit nf_map lit in 
    (if (not (lit == new_lit))
    then 
      (is_changed:= true)
    );
    new_lit::rest
  in   
  let new_lits = List.fold_left f [] old_lits in 
  if !is_changed
  then 
    let tstp_source = Clause.tstp_source_def_merge clause in	 
    let new_clause = create_clause tstp_source new_lits in 
    Clause.inherit_conjecture clause new_clause;
    dbg D_merge_def (lazy (""));
    dbg D_merge_def (lazy ("old_clause: "^(Clause.to_string clause)));
    dbg D_merge_def (lazy ("new_clause: "^(Clause.to_string new_clause)));
    Statistics.incr_int_stat 1 Statistics.merged_defs_ncl;
    new_clause
  else 
    clause

let apply_nf_map_to_clause_list nf_map clause_list = 
  let f rest clause =
    let new_clause = apply_nf_map_to_clause nf_map clause in 
    try 
      (Simplify.tautology_elim new_clause)::rest
    with 
      Eliminated -> rest
  in
  List.fold_left f [] clause_list 

(* TODO: experiemnt with different axioms: 1) now: lit<->nf; 2) circular l1->l2->..->l1 for each class 3) other ?  *)
let get_nf_axioms nf_map = 
  let f def_atom nf_lit rest_ax = 
    if (def_atom == nf_lit) (* ignore: nf -> nf *)
    then 
      rest_ax 
    else
      (
       let tstp_source = Clause.tstp_source_def_merge_axiom in	 
       let ax1 = create_clause tstp_source [add_compl_lit def_atom; nf_lit] in 
       let ax2 = create_clause tstp_source [def_atom; add_compl_lit nf_lit] in 
       dbg D_merge_def (lazy ("nf_axioms 1: "^(Clause.to_string ax1)));
       dbg D_merge_def (lazy ("nf_axioms 2: "^(Clause.to_string ax2)));
       ax1::ax2::rest_ax
      )
  in
  let nf_axioms = TMap.fold f nf_map [] in 
  dbg D_merge_def (lazy ("number of nf_axioms :"^(string_of_int (List.length nf_axioms))));
  nf_axioms



(*--------- matching-based def application (alternative to simple def. appl)-----------*)

type matching = 
    { (* represents maching of atom by def_atom in nf_map *)
  (*   match_subst  : Subst.subst;*)
     nf_match     : term; (* def_atom -> nf in nf_map; atom = def_atom*\match_subst; nf_match = nf*\match_subst *)
     nf_free_vars : VSet.t; (* 'vars(nf*\match_subst)\ \vars(atom)  *)
   }

module SubsIndex = SubsumptionIndex.SCFVIndex

type mbd_state = 
    {
     mbd_nf_map       : term TMap.t; (* nf_map as constructed above; does not change *)
     mbd_subs_index   : SubsIndex.index;
     mutable mbd_matching_map : matching TMap.t; (* atom  -> { def_atom*\match_subst = atom);..}  *)
   }

 (* as currently subs index is based on clauses rather than terms we need to create dummy unit clauses *)
 (* TODO: subsumption/matching index based on terms (or lists of terms) *)
 
let create_dummy_clause lit_list = 
  Clause.create_clause_raw Clause.tstp_source_tmp lit_list

let create_mbd_state nf_map = 
  let subs_index = SubsIndex.create () in 
  let matching_map = ref TMap.empty in

  let f def_atom nf = 
    if (def_atom == nf) (* do not add nf into subs index; or matching_map *)
    then ()
    else 
      (
  (* fill subsumtion index based on nf_map *)
       let def_clause = create_dummy_clause [def_atom] in 
       SubsIndex.add_clause subs_index def_clause;
       
(* extend mbd_matching_map with trival subst. *)
       let matching = 
         {
          nf_match = nf; 
          nf_free_vars = VSet.diff (Term.get_var_set nf) (Term.get_var_set def_atom); 
        }
       in
       matching_map := TMap.add def_atom matching !matching_map;
      )
  in
  TMap.iter f nf_map;
  let mbd_state = 
    {
     mbd_nf_map = nf_map;
     mbd_subs_index = subs_index;
     mbd_matching_map = !matching_map;
   }
  in
  mbd_state

let mbd_extend_atom mbd_state atom = 
  if (TMap.mem atom mbd_state.mbd_matching_map) 
  then ()
  else 
    begin
      let atom_clause = create_dummy_clause [atom] in
      match (SubsIndex.is_subsumed mbd_state.mbd_subs_index atom_clause) with 
      | Some(by_def_cl, subst) -> 
          let def_atom = get_singleton_from_list (Clause.get_literals by_def_cl) in 
          let nf = 
            try 
              TMap.find def_atom mbd_state.mbd_nf_map
            with 
              Not_found -> failwith "mbd_extend_atom: def_atom should be in mbd_nf_map"
          in  
          let nf_match = Subst.apply_subst_term term_db_ref subst nf in 
          let nf_free_vars = VSet.diff (Term.get_var_set nf_match) (Term.get_var_set atom) in

          dbg D_mbd (lazy (" matching: "^( Term.to_string atom)
                           ^" by: "^(Term.to_string def_atom)
                           ^" nf_match: "^(Term.to_string nf_match)
                           ^" nf_free_vars: "^(Var.var_list_to_string (VSet.elements nf_free_vars))
                          ));
          dbg D_mbd (lazy ("substitution:"^(Subst.to_string subst)));
          let matching = 
            {
             nf_match = nf_match;
             nf_free_vars = nf_free_vars;
           }
          in
          mbd_state.mbd_matching_map <- TMap.add atom matching mbd_state.mbd_matching_map
      | None -> ()  
    end
     
let rename_free_vars_away fresh_vars_env term free_var_set = 
(*  let fresh_vars_env = Var.init_fresh_vars_env_away (Set.elements away_var_set) in *)
(*  let rename_subst = Subst.create () in *)
  let f free_var rename_subst = 
(* since free vars are from set we do not need to check whether we already added it to subst *)
    let fresh_free_var = Var.get_next_fresh_var fresh_vars_env (Var.get_type free_var) in
    let fresh_free_var_term = add_var_term  fresh_free_var in
    Subst.add free_var fresh_free_var_term rename_subst 
  in
  let rename_subst = VSet.fold f free_var_set (Subst.create ()) in
  Subst.apply_subst_term term_db_ref rename_subst term

      

let apply_mbd_to_clause mbd_state clause = 
  let old_lits = Clause.get_literals clause in 
  let is_changed = ref false in 
  let clause_vars = Clause.get_var_set clause in 
  let fresh_vars_env = Var.init_fresh_vars_env_away (VSet.elements clause_vars) in
  let f rest lit = 
    let (pol, atom) = Term.split_sign_lit lit in 
    try 
      let matching = TMap.find atom mbd_state.mbd_matching_map in 
      is_changed:= true;
      let (nfm_pol, nfm_atom) = Term.split_sign_lit matching.nf_match in 
      let nfm_renamed_atom = 
        if (VSet.is_empty matching.nf_free_vars) 
        then 
          nfm_atom
        else
          rename_free_vars_away fresh_vars_env nfm_atom matching.nf_free_vars
      in
      let new_lit = 
        if pol = nfm_pol 
        then
          nfm_renamed_atom 
        else
          add_compl_lit nfm_renamed_atom
      in
      new_lit::rest      
    with 
      Not_found -> lit::rest 
  in
  let new_lits = List.fold_left f [] old_lits in 
  if !is_changed
  then 
    let tstp_source = Clause.tstp_source_def_merge clause in	 
    let new_clause = create_clause tstp_source new_lits in 
    Clause.inherit_conjecture clause new_clause;
    dbg D_merge_def (lazy (""));
    dbg D_merge_def (lazy ("mbd: old_clause: "^(Clause.to_string clause)));
    dbg D_merge_def (lazy ("mbd: new_clause: "^(Clause.to_string new_clause)));
    Statistics.incr_int_stat 1 Statistics.merged_defs_ncl;
    new_clause
  else 
    clause


let apply_mbd_to_clause_list mbd_state clause_list = 
  let f rest clause =
    let new_clause = apply_mbd_to_clause mbd_state clause in 
    try 
      (Simplify.tautology_elim new_clause)::rest
    with 
      Eliminated -> rest
  in
  List.fold_left f [] clause_list 

let mbd_init_and_apply_to_clause_list nf_map clause_list = 
  let mbd_state = create_mbd_state nf_map in 
  let all_atoms = Clause.get_atoms_clause_list clause_list in 
  TSet.iter (mbd_extend_atom mbd_state) all_atoms;
  apply_mbd_to_clause_list mbd_state clause_list

(*------------ transitive reduction/closure --------*)


let get_nf_impl_graph nf_map impl_graph  = 
  let f lit_1 lit_2 nf_graph =     
    let nf_lit_1 = apply_nf_map_to_lit nf_map lit_1 in 
    let nf_lit_2 = apply_nf_map_to_lit nf_map lit_2 in 
    if (not (nf_lit_1 == nf_lit_2))
    then 
      DGS.add_edge nf_graph nf_lit_1 nf_lit_2 
    else 
      nf_graph
  in
  DGS.fold_edges f impl_graph DGS.empty

let transitive_reduction nf_graph = DGS_OPER.transitive_reduction nf_graph

let transitive_closure nf_graph = DGS_OPER.transitive_closure nf_graph
    
let nf_impl_axioms nf_impl_graph = 
  let f nf_lit_1 nf_lit_2 impl_axs_set =     
    let tstp_source = Clause.tstp_source_def_merge_nf_impl in	 
    let ax = create_clause tstp_source [add_compl_lit nf_lit_1; nf_lit_2] in 
    BCSet.add ax impl_axs_set 
  in
  let ax_set = DGS.fold_edges f nf_impl_graph BCSet.empty in 
  BCSet.elements ax_set 
  
    

  
(*------------------------------------------*)

(*
let def_merge_mbd_flag = true 

let _ = out_warning ("def_merge_mbd_flag: "^(string_of_bool def_merge_mbd_flag))
*)

(* move to preprocess
let reuse_old_clauses old_cl_list new_cl_list = 
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
*)

let def_merge_tr_red_non_prop_flag = true 

(* SW
let _ = out_warning ("def_merge_tr_red_non_prop_flag: "^(string_of_bool def_merge_tr_red_non_prop_flag))
*)


let def_merge clause_list =
  dbg D_in_out  (lazy (" ----------------- "));
  dbg D_in_out  (lazy ((" input clauses: ")^(string_of_int (List.length clause_list))^"\n"));
  dbg D_in_out  (lazy ("\n"^(Clause.clause_list_to_string clause_list)));
  dbg D_in_out  (lazy ("----- end input clauses ------------ "));
(*
  List.iter 
    Prop_solver_exchange.add_clause_to_solver clause_list; 
  (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
  then
    raise Unsatisfiable_gr
  else ()
  );
*)
  let used_prop_impl_graph_flag = ref false in 
  let bhr_graph = 
    if (!current_options.prep_def_merge_prop_impl)  && (Prop_solver_exchange.is_empty_assumptions ()) (* for now apply impl only when there is no assumptions *)
    then
      (
       used_prop_impl_graph_flag:=true;
       init_prop_impl_bhr_graph clause_list 
      )
    else 
      init_bhr_graph clause_list 
  in
  let def_equiv_list = DGS_SCC.scc_list bhr_graph in (* scc components list *)
  let f rest_nf_map def_equiv = 
    let size_def_equiv = (List.length def_equiv) in
    if size_def_equiv > 1 
    then 
      (
       Statistics.incr_int_stat (size_def_equiv -1) Statistics.merged_defs;
       dbg D_merge_def (lazy (Term.term_list_to_string def_equiv));
       extend_nf_map rest_nf_map def_equiv
      )
    else 
      rest_nf_map
  in
  let nf_map = List.fold_left f TMap.empty def_equiv_list in 
  if ((DGS.is_empty bhr_graph) || 
  ((nf_map = TMap.empty) && 
   (not !current_options.prep_def_merge_tr_red) && (not !current_options.prep_def_merge_tr_cl)))
     (* we can apply tr_red even without def; just on the binary (implied) clauses *)
  then 
    (
     dbg D_merge_def (lazy "nf_map: empty");
     clause_list
    )
  else 
    (
     dbg D_merge_def (lazy "nf_map:");
     dbg D_merge_def (lazy (nf_map_to_string nf_map));

     let new_clause_list = 
       let tr_transformed_cl_list = (* either transitive reduction or closure *)
(*       let tr_reduced_cl_list = *)
         assert ((not !current_options.prep_def_merge_tr_red) || (not !current_options.prep_def_merge_tr_cl));
         if !current_options.prep_def_merge_tr_red || !current_options.prep_def_merge_tr_cl
         then 
           let (clauses_binary, clauses_not_binary) = List.partition (fun c -> (Clause.length c)  = 2) clause_list in

           let bin_impl_graph = 
             if ((!used_prop_impl_graph_flag) && def_merge_tr_red_non_prop_flag)
             then
               init_bhr_graph clause_list                
             else
               bhr_graph
           in
           let nf_impl_graph = get_nf_impl_graph nf_map bin_impl_graph in
           let nf_impl_graph_reduced = 
             if !current_options.prep_def_merge_tr_red
             then
               (
                dbg D_tr_red  (lazy (" transitive reduction "));                
                transitive_reduction nf_impl_graph 
               )
             else
               if !current_options.prep_def_merge_tr_cl
               then
                 (
                  dbg D_tr_red  (lazy (" transitive closure "));
                 transitive_closure nf_impl_graph 
                 )
               else
                 failwith "here should be either: --prep_def_merge_tr_red true or --prep_def_merge_tr_cl true"
           in 
           let new_binary = nf_impl_axioms nf_impl_graph_reduced in

           dbg D_tr_red  (lazy (" ----------------- "));
           dbg D_tr_red (lazy ("old binary clauses: "^(string_of_int (List.length clauses_binary))^"\n"
                               ^(Clause.clause_list_to_string clauses_binary)));
           dbg D_tr_red  (lazy (" ----------------- "));
           dbg D_tr_red (lazy ("new binary clauses: "^(string_of_int (List.length new_binary))^"\n"
                               ^(Clause.clause_list_to_string new_binary)));
           new_binary@clauses_not_binary
         else
           clause_list
       in
       if (nf_map = TMap.empty)
       then
         tr_transformed_cl_list
       else
         if !current_options.prep_def_merge_mbd
         then 
           mbd_init_and_apply_to_clause_list nf_map tr_transformed_cl_list         
         else
           apply_nf_map_to_clause_list nf_map tr_transformed_cl_list 
     in

     let nf_axioms = get_nf_axioms nf_map in 
     let all_new_clauses = nf_axioms@new_clause_list in

     dbg D_in_out  (lazy (" ----------------- "));
     dbg D_in_out  (lazy ((" new clauses: ")^(string_of_int (List.length all_new_clauses))^"\n"));
     dbg D_in_out  (lazy ("\n"^(Clause.clause_list_to_string all_new_clauses)));
     dbg D_in_out (lazy ("----- end new clauses ------------ "));
(*    reuse_old_clauses clause_list all_new_clauses *)
     all_new_clauses 
    )

(*
let def_merge_test clause_list =
  out_warning "dbg def_merge_test";
  let bhr_graph = init_bhr_graph clause_list in
  let scc_list = DGS_SCC.scc_list bhr_graph in
  let f ssc_class = 
    let size_ssc_class = (List.length ssc_class) in
    if size_ssc_class > 1 
    then 
      (
       Statistics.incr_int_stat (size_ssc_class -1) Statistics.merged_defs;
       dbg D_merge_def (lazy (Term.term_list_to_string ssc_class));
      )
    else 
      ()
  in
  List.iter f scc_list

*)
