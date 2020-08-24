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




(* non-variable disjoint (nvd) splitting  *)

open Lib
open Logic_interface
open Definitions 

(* basic splitting *)

type sp_cl_part = (lit list) list 

(*
let create_new_split_atom vset = 
  let vlist = VSet.elements vset in
  let arg_types = List.map Var.get_type vlist in
  let pred_symb = 
    SymbolDB.create_new_split_symb
      symbol_db_ref
      (Symbol.create_stype arg_types Symbol.symb_bool_type)  
  in
  let args = List.map add_var_term vlist in
  let atom = add_fun_term pred_symb args in
  atom
*)

let parition_lits part_size lits =
  list_partition part_size lits 

(*let create_split_clauses max_var part_ll = *)
let split_lits_once def_env parent_clause sp_part_size lits (* parent_cl*) = (* TODO: add parents *) 
  let part_ll = parition_lits sp_part_size lits in 
  assert (not (part_ll == []));
  let f (sp_atoms,split_def_cls) part_lits = 
    let vlist = List.fold_left  (fun rest l -> (Term.get_vars l)@rest) [] part_lits in 
    let vset = VSet.of_list vlist in 

    let (sp_atom, sp_clause) = 
      add_def def_env ~parent:parent_clause (VSet.elements vset) part_lits in
  (*           
    let sp_atom = create_new_split_atom vset in
    let sp_lit = add_neg_atom sp_atom  in (* ~sp(X) \/ part_lits *)
    let tstp_source = Clause.tstp_source_split [sp_atom] [parent_clause] in	 
    let sp_clause = create_clause tstp_source (sp_lit::part_lits) in 
    Clause.inherit_conjecture parent_clause sp_clause;  
*)
    (sp_atom::sp_atoms, (sp_clause::split_def_cls))
  in  
  let (sp_atoms, sp_def_cls) = List.fold_left f ([], []) part_ll in 
  (* let sp_pos_cl = clause_create (List.map (var_to_lit true) sp_vars) P_Input in*) (* TODO: change P_Input to P_Split *)
  (sp_atoms, sp_def_cls)


let split_lits def_env parent_clause sp_part_size lits_to_split = 

  assert (sp_part_size >= 2);
  (* split recursively until sp_pos_cl size is less than sp_part_size *)
  let rec f lits_to_split sp_def_cls = 
(*    *)
    if (List.length lits_to_split) < 2*sp_part_size 
    then 
      (lits_to_split, sp_def_cls)
    else
      let (new_sp_atoms, next_sp_def_cls) = split_lits_once def_env parent_clause sp_part_size lits_to_split in 
      let new_sp_def_cls = next_sp_def_cls@sp_def_cls in
      f new_sp_atoms new_sp_def_cls     
  in
  let (lits_remainder, sp_def_clauses) = f lits_to_split [] in

  let sp_pos_clause = create_def_reduced_clause ~parent:parent_clause lits_remainder in
(*
  let tstp_source = Clause.tstp_source_split [] [parent_clause] in	 
  let sp_pos_clause = create_clause tstp_source lits_remainder in 
  Clause.inherit_conjecture parent_clause sp_pos_clause;  
*)

  let sp_clauses = sp_pos_clause::sp_def_clauses in
(*  Clause.assign_replaced_by (Def(Clause.RB_splitting sp_clauses)) parent_clause; *)
(*  List.iter (Clause.inherit_conjecture parent_clause) sp_clauses; *)
  sp_clauses

let split_clause def_env sp_part_size clause = 
  let lits =  (Clause.get_literals clause) in
  if ((List.length lits) >= 2*sp_part_size)
  then
    split_lits def_env clause sp_part_size (Clause.get_literals clause)
  else
    [clause]

let split_clause_list def_env sp_part_size clause_list = 
  let f rest clause = (split_clause def_env sp_part_size clause)@rest in
  List.fold_left f [] clause_list
    
