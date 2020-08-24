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








(* semantic filter based on top symbol, *)
(* more general based on unification is in prep_sem_filer_unif.ml*)

open Lib
type clause = Clause.clause
type lit = Term.literal
type term = Term.term
type symbol = Symbol.symbol  


module OrderSymb = 
  struct
    type t = symbol
    let compare = Symbol.compare
  end

module SymbSet = Set.Make(OrderSymb)

module SymbHashKey = 
  struct
    type t    = symbol
    let equal = Symbol.equal
    let hash  = Symbol.get_fast_key
  end 

module SymbHash = Hashtbl.Make(SymbHashKey)

type filter_state = 
    {

(* intially all clauses unprocessed*)
     mutable unprocessed_clauses : clause list;

(* clauses that are kept after the filter *)
     mutable filtered_clauses : clause list;
     mutable undef_pred_queue : symbol list;
     mutable undef_pred_set   : SymbSet.t; 
     watch_symbol_table       : ((clause list) ref)SymbHash.t
   }
      
let init_filter_state clause_list = 
  {
   unprocessed_clauses = clause_list;
   filtered_clauses    = [];
   undef_pred_queue    = [];
   undef_pred_set      = SymbSet.empty;
   watch_symbol_table  = SymbHash.create 100000 
 }


(* find_watch_symb raise Not_found if no watch_symb found *)
    
let find_watch_symb filter_state clause =
  let cand_watch_lit lit =  
    let top_symb = Term.lit_get_top_symb lit in
    not (SymbSet.mem top_symb filter_state.undef_pred_set) 
      &&
    (Term.is_neg_lit lit)
  in
  let next_watch_lit = Clause.find cand_watch_lit clause in
  Term.lit_get_top_symb next_watch_lit

let add_to_watch filter_state symb clause = 
  try 
    let clause_list_ref  = SymbHash.find filter_state.watch_symbol_table symb in
    clause_list_ref:=clause::(!clause_list_ref)
  with
    Not_found ->       
      SymbHash.add filter_state.watch_symbol_table symb (ref [clause])

let add_preds_to_undef_list filter_state clause =
  Clause.iter 
    (fun lit -> 
      if (not (Term.is_neg_lit lit))       
      then 	
	let top_symb = (Term.lit_get_top_symb lit) in
	if 
	  (not (SymbSet.mem top_symb filter_state.undef_pred_set))
	then 
	  filter_state.undef_pred_queue <- 
	    top_symb:: filter_state.undef_pred_queue
	else ()
      else ()
    )
    clause

let rec filter_clauses filter_state = 
  match filter_state.unprocessed_clauses with 
  |[] ->  filter_state.filtered_clauses
  |clause::tl ->
      (try 
	let watch_symb = find_watch_symb filter_state clause in 
	add_to_watch filter_state watch_symb clause;
      with
	Not_found -> 
	  (
	   add_preds_to_undef_list filter_state clause;
	   filter_state.filtered_clauses<-clause::filter_state.filtered_clauses;
	  )
      );
      filter_state.unprocessed_clauses <- tl;
      process_undef_preds filter_state
and
    process_undef_preds filter_state =
  match filter_state.undef_pred_queue with 
  |[] -> filter_clauses filter_state
  |symb::tl -> 
      (try
	let watch_clause_list_ref =
	  SymbHash.find filter_state.watch_symbol_table symb in
	filter_state.unprocessed_clauses <- 
	  (!watch_clause_list_ref)@filter_state.unprocessed_clauses;
	SymbHash.remove filter_state.watch_symbol_table symb		      
      with 
	Not_found -> ()
      );
      filter_state.undef_pred_queue <- tl;
      filter_state.undef_pred_set <-
	(SymbSet.add symb filter_state.undef_pred_set);
      process_undef_preds filter_state

	

(* output filtered clauses*)
let filter clause_list = 
  filter_clauses (init_filter_state clause_list)
