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


(* unification index of clauses for inst/res implementation *)

open Lib
open Options
open Statistics
open Logic_interface

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_trace
  | D_filter_mu

let dbg_gr_to_str = function
  | D_trace -> "trace"
  | D_filter_mu -> "filter_mu"

let dbg_groups =
  [
(*    D_trace; *)
   D_filter_mu;
 ]

let module_name = "clause_unif_index"


(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(*---------------------------------------------------------*)
(* choose an appropriate unificiation index implementation *)
(*---------------------------------------------------------*)

 module UnifIndex = UnifIndexDiscrTree 

(* let ()= out_str "\n\n !!!!!! clauseUnifIndex module UnifIndex = UnifIndexDebug !!!!!!!!!!\n\n"*)

(* module UnifIndex = UnifIndexDebug *)

(* module UnifIndex = UnifIndexMap *)
(* module UnifIndex = UnifIndexDebug *)

type t = {
  mutable unif_index : clause UnifIndex.t;
}

(* create unification index: i/r *)
let create () =
  {
   unif_index = (UnifIndex.create ());
 }

(* clear unification index: i/r, like create *)
let clear ui = UnifIndex.clear ui.unif_index

(* add clause with given selection literal: i/r *)
let add_clause_with_sel ui sel_lit main_clause =
  dbg D_trace (lazy ("Add: lit: "^(Term.to_string sel_lit)^", clause: "^(Clause.to_string main_clause)));
  UnifIndex.add_elem_to_lit ui.unif_index sel_lit main_clause

(* remove clause with given selection literal: i/r *)
(* Throws Not_found if sel_lit not found in unif index *)
let elim_clause_with_sel ui sel_lit main_clause =
  dbg D_trace (lazy ("Del: lit: "^(Term.to_string sel_lit)^", clause: "^(Clause.to_string main_clause)));
  UnifIndex.elim_elem_from_lit ui.unif_index sel_lit main_clause

(* eliminates all clauses indexed by lit from unif_index and returns *)
(* the eliminated clause list: i *)

let eliminate_lit ui lit =
  let removed_clauses = UnifIndex.eliminate_lit ui.unif_index lit in
  dbg D_trace (lazy ("Elim: lit: "^(Term.to_string lit)^", clauses: "^(Clause.clause_list_to_string removed_clauses)));
  (* return the list *)
  removed_clauses

let print_unif_cand unif_cand =
  let cl_list_to_string clause_list =
    let p_cl str clause = str^","^(Clause.to_string clause) in
    match clause_list with
    | hd::tl -> (List.fold_left p_cl ("["^(Clause.to_string hd)) tl)^"]"
    | [] -> "[]"
  in
  let print_one_cand str (lit, clause_list) = str^(Term.to_string lit)^": "^(cl_list_to_string clause_list)^"; " in
  (List.fold_left print_one_cand "[ " unif_cand)^"]"

(* get unification candidates for given selection literals, i/r *)
let get_unif_candidates ui sel_lit =
  dbg D_trace (lazy ("Unif: lit: "^(Term.to_string sel_lit)));
  let candidates = UnifIndex.get_unif_candidates ui.unif_index sel_lit in
  dbg D_trace (lazy ("Cand: lit: "^(Term.to_string sel_lit)^", res: "^(print_unif_cand candidates)));
  candidates


(* check whether given literal is in the unif index *)
let in_unif_index ui lit = UnifIndex.in_unif_index ui.unif_index lit

(*--------------------*)

let add_cl_measure_list cl_measure start cl_list = 
  List.fold_left (fun rest cl -> (cl_measure cl) + rest) start cl_list 
 
let get_measure_unif_cand_lit ui cl_measure lit = 
  let unif_cands = (get_unif_candidates ui (add_compl_lit lit)) in 
  let f rest (_cand_lit, cands) = add_cl_measure_list cl_measure rest cands in 
  List.fold_left f 0 unif_cands

let get_measure_unif_cand_lits ui cl_measure lits = 
  List.fold_left (fun rest lit -> rest + (get_measure_unif_cand_lit ui cl_measure lit)) 0 lits

let filter_lits_min_unif_cand ui cl_measure lits = 
  match lits with 
  |[] -> lits
  |[h] -> lits 
  |_->
      begin (* List.length lits >= 2 *)
        let measure_unif_cands_cons_list = 
          List.map 
            (fun lit -> (lit,(get_measure_unif_cand_lit ui cl_measure lit))) 
            lits
        in
        let cmp (_l1,n1) (_l2,n2) = compare n1 n2 in 
        let (min_lits,min_ns) = List.split (list_find_all_min_elements cmp measure_unif_cands_cons_list) in
        dbg_env D_filter_mu 
          (fun () ->
            dbg  D_filter_mu (lazy ("-------- all cands: "));
            List.iter (fun (l,n) -> 
              dbg  D_filter_mu (lazy (" cand: "^(Term.to_string l)^" measure_cand: "^(string_of_int n))); 
                      ) measure_unif_cands_cons_list
        );
        let min_n = List.hd min_ns in
        dbg D_filter_mu (lazy ("min cands: "^(Term.term_list_to_string min_lits)^" measure_cand: "^(string_of_int min_n)));
(*  (min_lits, min_n) *)
        min_lits
      end
(*
let filter_lits_min_unif_cand ui cl_measure lits = 
  let (min_lits, _min_n) = filter_lits_min_unif_cand' ui cl_measure lits in
  min_lits
*)
(*
let cmp_lits_min_unif_cand ui cl_measure lits1 lits2 = 
  *)

