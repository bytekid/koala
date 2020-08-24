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




(*
type qbf_symbs = 
    {
     mutable qbf_sk_e_preds = .t
       
   }
 *)

open Lib
open Options
open Logic_interface 
open Qbf_env


(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_prep_qbf

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_prep_qbf -> "prep_qbf"

let dbg_groups =
  [
   D_trace; 
   D_prep_qbf;
 ]

let module_name = "qbf_fof"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)



module PV=Prop_var
(* can not open both prop modules and Logic_interface since many name clashes *)

module PVMap = PV.VMap
module PVSet = PV.VSet

type pvar = PV.var
type plit = PV.lit
type qbf_cnf = Qbf_env.qbf_cnf

let bool_type = Symbol.symb_bool_type
let prop_type = Symbol.symb_bool_fun_type (* Symbol.symb_default_type *)
let true_fun_term = SystemDBs.true_fun_term
let false_fun_term = SystemDBs.false_fun_term


(*-----------------------------------*)
type qbf_sk_env = (* sk involve only existential vars *)
    {
     mutable sk_e_preds : symbol PVMap.t;
     mutable sk_e_atoms : term PVMap.t;
     mutable sk_a_atoms : term PVMap.t (* later replace *)
   }

let create_qbf_sk_env () = 
  {
   sk_e_preds = PVMap.empty;
   sk_e_atoms = PVMap.empty;
   sk_a_atoms = PVMap.empty;
 }

(*-------------*)
let create_sk_e_pred pvar arity = 
  let stype = create_stype (list_create prop_type arity) bool_type in
  let pred_name = ("$$iProver_qbf_sKE_"^(PV.var_to_string pvar)) in 
  create_symbol pred_name stype 

let pvar_to_fvar pvar =
  Var.create prop_type (PV.get_var_id pvar)

let pvar_to_fterm pvar = 
  let fvar = pvar_to_fvar pvar in 
  add_var_term fvar

let create_sk_e_atom sk_pred pvlist = 
(*  let arity = Symbol.get_arity sk_pred in
  assert(arity = (List.length pvlist));
  let atom_symb = create_sk_e_pred pvar arity in *)
  let atom_args = List.map pvar_to_fterm pvlist in
  add_fun_term sk_pred atom_args

(*-------------*)
(* unary predicate for a vars *)
let create_sk_a_pred () = (* TODO move to a global ref. *)
  let stype = create_stype [prop_type] bool_type in
  let pred_name = ("$$iProver_qbf_sKA") in 
  create_symbol pred_name stype
 
let create_sk_a_atom pvar = 
  let atom_symb = create_sk_a_pred () in 
  let atom_args = [(pvar_to_fterm pvar)] in 
  add_fun_term atom_symb atom_args

(*--------------------*)
(* p(true); ~p(false) *)
(*
let term_prop_true () =
  let stype = create_stype [] prop_type in
  let pred_name = ("$$iProver_prop_true") in 
  let true_symb = create_symbol pred_name stype in 
  add_fun_term true_symb []

let term_prop_false () =
  let stype = create_stype [] prop_type in
  let pred_name = ("$$iProver_prop_false") in 
  let false_symb = create_symbol pred_name stype in 
  add_fun_term false_symb []
*)

(*-------------*)

let fill_qbf_sk_env_e qbf_sk_env var_dep_map = 
  let f pvar pvar_set = 
    let pvar_list = PVSet.elements pvar_set in
    let arity = List.length pvar_list in 
    let sk_e_pred = create_sk_e_pred pvar arity in 
    let sk_e_atom = create_sk_e_atom sk_e_pred pvar_list in
    qbf_sk_env.sk_e_preds <-PVMap.add pvar sk_e_pred qbf_sk_env.sk_e_preds;
    qbf_sk_env.sk_e_atoms <-PVMap.add pvar sk_e_atom qbf_sk_env.sk_e_atoms;
  in
  PVMap.iter f var_dep_map


(*-------------*)
let clause_prop_to_fof qbf_cnf qbf_sk_env prop_clause = 
  let f (univ_subst, fof_lits)  plit = 
    let (pol, pvar) = PV.lit_to_var plit in 
    let quant = 
      if (PVMap.mem pvar qbf_cnf.qbf_dvar_map) 
      then 
        D
      else
        let (_lvl,quant) =  PVMap.find pvar qbf_cnf.qbf_var_level in
        quant 
    in
    match quant with 
    |E | D ->         
        let fof_e_atom = 
          (try 
              PVMap.find pvar qbf_sk_env.sk_e_atoms 
          with 
            Not_found -> failwith "qbf_fof: clause_prop_to_fof: pvar is not in qbf_sk_env.sk_e_atoms"
          )
        in
        let fof_e_lit = if pol then fof_e_atom else (add_compl_lit fof_e_atom) in
        let new_fof_lits = fof_e_lit::fof_lits in
        (univ_subst,new_fof_lits)
    |A -> 
        if (!current_options.qbf_elim_univ)
        then        
          let fof_a_var = pvar_to_fvar pvar in
          let subs_term = 
            if pol 
            then 
              (false_fun_term)
            else 
              (true_fun_term)
          in
          let new_univ_subst = Subst.add fof_a_var subs_term univ_subst in 
          (new_univ_subst, fof_lits)          
        else
          let fof_a_atom =
            (try 
              PVMap.find pvar qbf_sk_env.sk_a_atoms
            with
              Not_found -> 
                let sk_a_atom = create_sk_a_atom pvar in 
                qbf_sk_env.sk_a_atoms <- PVMap.add pvar sk_a_atom qbf_sk_env.sk_a_atoms;
                sk_a_atom 
            )
          in 
          let fof_a_lit =  if pol then fof_a_atom else (add_compl_lit fof_a_atom) in
          let new_fof_lits = fof_a_lit::fof_lits in
          (univ_subst,new_fof_lits)
  in
  let (univ_subst, fof_e_lits) = List.fold_left f ((Subst.create ()),[]) (Prop_env.clause_get_lits prop_clause) in
  let fof_e_lits_subst = List.map (Subst.apply_subst_term term_db_ref univ_subst) fof_e_lits in 
  let tstp_source = Clause.tstp_source_input "qbf_prop_to_fof" "qbf" in (*TODO change tstp_source_input *)
  create_clause tstp_source fof_e_lits_subst
    
  
let qbf_a_domain_axs () = 
  if (!current_options.qbf_elim_univ)
  then 
    []
  else
    let a_pred = create_sk_a_pred () in 
    let pos_ax_lit = add_fun_term a_pred [true_fun_term] in
    let neg_ax_lit = add_neg_atom_symb a_pred [false_fun_term] in
    let tstp_source = Clause.tstp_source_input "qbf domain" "qbf" in (*TODO change tstp_source_input *)
    let pos_ax = create_clause tstp_source [pos_ax_lit] in 
    let neg_ax = create_clause tstp_source [neg_ax_lit] in 
    [pos_ax;neg_ax]

let qbf_to_fof_sk qbf_cnf var_dep =
(* 
  let var_dep = 
    if (!current_options.qbf_sk_in (* && (PVMap.is_empty qbf_cnf.qbf_dvar_map)*))
    then 
      qbf_inner_var_dep qbf_cnf
    else
      qbf_outer_var_dep qbf_cnf
  in
*) 
  let qbf_sk_env = create_qbf_sk_env () in 
  fill_qbf_sk_env_e qbf_sk_env var_dep;

(* 
 let prop_cl_to_fof = 
    if (!current_options.qbf_elim_univ)
    then 
      clause_prop_to_fof_univ_elim_outer 
    else
      clause_prop_to_fof_outer
  in      
*)
  let fof_qbf_clauses = List.map (clause_prop_to_fof qbf_cnf qbf_sk_env) qbf_cnf.qbf_clauses in
  let fof_a_dom_axs = qbf_a_domain_axs () in
 
  let all_fof_clauses =  fof_a_dom_axs@fof_qbf_clauses in
  dbg D_trace (lazy ("Input QBF clauses translated to EPR:\n "));
  dbg_env D_trace 
    (fun () ->
      out_str (Clause.clause_list_to_string all_fof_clauses)
    );
  all_fof_clauses

(*-------------------------*)

(* TODO add to options *)
(*
let preprocess_qbf qbf = 
  qbf_q_resolve qbf;  
  qbf_split_clauses !current_options.qbf_split qbf 
*)

let qbf_to_fof_channel ch_name in_channel = 
  try
    print_string ((s_pref_str ())^"Parsing QBF... ");
    flush stdout;
    let qbf = qbf_parse_in_channel ch_name in_channel in 
    out_str "successful\n";
    let var_dep = Qbf_preprocess.preprocess_qbf qbf 
(*
      if (PVMap.is_empty qbf.qbf_dvar_map)
      then 
        (Qbf_preprocess.preprocess_qbf qbf)
      else 
        (Qbf_preprocess.preprocess_dqbf qbf)
*)
    in
    dbg_env D_prep_qbf 
      (fun () ->
        dbg D_prep_qbf (lazy (""));
        dbg D_prep_qbf (lazy ("c iProver preprocessed QBF: \n\n"));
        out_qbf qbf;
      );
      let fof_clauses = qbf_to_fof_sk qbf var_dep in 
    fof_clauses
  with 
    Prop_env.Unsatisfiable _ -> 
      let tstp_source = Clause.tstp_source_input "qbf_prop_to_fof" "qbf" in (*TODO change tstp_source_input *)
      let empty_clause = create_clause tstp_source [] in 
      raise (Empty_clause (empty_clause))
 

let qbf_parse_to_fof_file file_name = 
  let in_channel = open_in file_name in
  let fof_clauses = qbf_to_fof_channel file_name in_channel in 
  close_in in_channel;
  fof_clauses

let qbf_parse_to_fof_stdin () = 
  let ch_name = "stdin" in 
  let in_channel = stdin in 
  let fof_clauses = qbf_to_fof_channel ch_name in_channel in 
  fof_clauses

let parse_and_process_qbf () = 
  let clause_list =
    if !current_options.stdin then
      (
(* print_string "from stdin...";
       flush stdout;*)
       qbf_parse_to_fof_stdin ()
      )
    else
      (
(* print_string "...";
       flush stdout;*)
       let input_file = (List.hd !current_options.problem_files) in 
       (if ((List.length !current_options.problem_files) > 1) 
       then 
         out_warning ("QBF processing only first file; the rest are ignored");
       );
       qbf_parse_to_fof_file input_file
      )
  in
  Parser_types.parsed_clauses := clause_list
