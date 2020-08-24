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


(* clause definitions *)
open Lib
open Logic_interface


let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

	
let dbg_groups =
  [
   D_trace
 ]
    
let module_name = "definitions"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)


module VLKey = 
  struct
    type t              = var list (* assume that var list are always sorted *)
    let compare vl1 vl2 = list_compare_lex Var.compare vl1 vl2
  end

module VLMap = Map.Make(VLKey)


module TLKey = 
  struct
    type t              = term list (* assume that var list are always sorted *)
    let compare vl1 vl2 = list_compare_lex Term.compare vl1 vl2
  end

module TLMap = Map.Make(TLKey)


(* definitions used in splitting *)
(* definitons are of the from C(X,Y) \/ ~p(X) *)
(* since we have different definition restrictions with subsets of the clause vraiables  *)

(* def *)

type def = 
    {
     def_atom : term;
     def_clause : clause;
     def_vars : var list;
   }

type def_var_restr_map = def VLMap.t

(* def_pre_map: maps from pre-def clauses C into varible list map which repersent variable restriction of the definiton
  (def VLMap.t) (map pred_def clauses unot ) *)

type def_env = 
    {
(*     mutable def_clauses : CSet.t; *)
     mutable def_map : def_var_restr_map TLMap.t;
   }

let create_def_env () = 
  {
   def_map = TLMap.empty
 }

let def_env_glb = create_def_env ()

let sort_lits lits = List.sort Term.compare lits
let sort_vars vars = List.sort Var.compare vars


let create_new_split_atom sorted_vars = 
  let arg_types = List.map Var.get_type sorted_vars in
  let pred_symb = 
    SymbolDB.create_new_split_symb
      symbol_db_ref
      (Symbol.create_stype arg_types Symbol.symb_bool_type)  
  in
  let args = List.map add_var_term sorted_vars in
  let atom = add_fun_term pred_symb args in
  atom

let create_def ~parent sorted_vars sorted_lits = 
  let def_atom = create_new_split_atom sorted_vars in
  let neg_def_atom = add_neg_atom def_atom in

(*  let tstp_source = Clause.tstp_source_split [neg_def_atom] [parent] in	 *)
  let tstp_source = Clause.tstp_source_split [def_atom] [parent] in	(* Geoff does not like neg atoms in the tstp_source *)
  let def_clause = Clause.create_clause_raw tstp_source (sorted_lits@[neg_def_atom]) in 
(*  let def_clause = create_clause tstp_source ((* neg_def_atom *) def_atom::sorted_lits) in *)
  Clause.inherit_conjecture parent def_clause;
  dbg D_trace (lazy ("def clause: renamed_list: "^(Term.term_list_to_string sorted_lits)));  
  dbg D_trace (lazy ("def clause: sorted_vars: "^(Var.var_list_to_string sorted_vars)));  
  dbg D_trace (lazy ("def clause: "^(Clause.to_string def_clause)));  
  let def = 
    {
(*     def_atom = neg_def_atom; (* def_atom; *) *)
     def_atom = def_atom; 
     def_clause = def_clause;
     def_vars = sorted_vars;
   }
  in
  def

let create_def_reduced_clause ~parent lits = 
  let tstp_source = Clause.tstp_source_split [] [parent] in	 
  let red_clause = create_clause tstp_source lits in 
  Clause.inherit_conjecture parent red_clause;
  red_clause


(* returns definition: C(X,Y) \/ ~p(X) and def atom p(X), restricted to var_list *)
(* first checks if already there *)
let add_def de ~parent var_list lit_list = 
  dbg D_trace (lazy (" lit_list: "^(Term.term_list_to_string lit_list))); 
  dbg D_trace (lazy (" var_list: "^(Var.var_list_to_string var_list))); 
  let (renamed_lits, renaming) = Clause.normalise_lit_list_renaming term_db_ref lit_list in    
  let renamed_vars = Var.apply_renaming_vlist renaming var_list in  
  let sorted_vars = sort_vars renamed_vars in

  let var_restr_map = 
    try 
      TLMap.find renamed_lits de.def_map
    with 
      Not_found -> 
        VLMap.empty
  in
  let def = 
    try
      (
       let existing_def = VLMap.find sorted_vars var_restr_map in 
       dbg D_trace (lazy (" reused: "^(Clause.to_string existing_def.def_clause)));
       Statistics.incr_int_stat 1 Statistics.num_of_reused_defs;
       existing_def
      )
    with
      Not_found ->      
        (
         create_def ~parent sorted_vars renamed_lits      
        )
  in
  let new_var_restr_map = VLMap.add sorted_vars def var_restr_map in
  de.def_map <- TLMap.add renamed_lits new_var_restr_map de.def_map;

  (* reverse renaming in def atom *)
  let rev_renaming = Var.reverse_renaming renaming in
  let rev_ren_subst = Subst.var_renaming_to_subst term_db_ref rev_renaming in
  let ren_def_atom = Subst.apply_subst_term  term_db_ref rev_ren_subst def.def_atom in
  dbg D_trace (lazy (" ren_def_atom: "^(Term.to_string ren_def_atom)));
   
  (ren_def_atom, def.def_clause)
