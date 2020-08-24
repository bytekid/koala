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
  | D_prop

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_prop -> "prop"

let dbg_groups =
  [
   D_trace;
   D_prop
 ]
    
let module_name = "problem_properties"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


(*---------------Probelm Properties---------------------*)

type prob_props =
    {
     mutable clauses : int;
     mutable conjectures : int;
     mutable epr : int;
     mutable horn : int;
     mutable unary : int;
     mutable binary : int;
     mutable lits : int;
     mutable lits_eq : int;
   }


(* initialisation is like this due to how epr/horn is reassigned *)
let empty_prob_props () =
  {
   clauses = 0;
   conjectures = 0;
   epr = 0;
   horn = 0;
   unary = 0;
   binary = 0;
   lits = 0;
   lits_eq = 0;
 }

let is_epr prob_props = (prob_props.clauses = prob_props.epr)
let is_horn prob_props = (prob_props.clauses = prob_props.horn)
let has_eq prob_props = (prob_props.lits_eq > 0)
let is_unary prob_props = (prob_props.clauses =  prob_props.unary) 
let is_binary prob_props = (prob_props.clauses = prob_props.unary + prob_props.binary) 
let is_unit_eq prob_props = (is_unary prob_props) && (prob_props.lits_eq = prob_props.clauses)

let prob_props_to_string props =
  let props_list =
    [
     ("clauses", string_of_int props.clauses);
     ("conjectures", string_of_int props.conjectures);
     ("EPR", string_of_int props.epr);
     ("Horn", string_of_int props.horn);
     ("unary", string_of_int props.unary);
     ("binary", string_of_int props.binary);
     ("lits", string_of_int props.lits);
     ("lits eq", string_of_int props.lits_eq);
   ]
  in
  Options.opt_val_list_to_str props_list
    

let prob_props_to_statistics props = 
  assign_int_stat props.clauses clauses; 
  assign_int_stat props.conjectures conjectures; 
  assign_int_stat props.epr epr;
  assign_int_stat props.horn horn;
  assign_int_stat props.unary unary;
  assign_int_stat props.binary binary;
  assign_int_stat props.lits lits;
  assign_int_stat props.lits_eq lits_eq

let add_prob_props prob_props cl = 
  let num_cl_lits = (Clause.length cl) in 
  let nun_cl_lits_eq = 
    if (not (Clause.has_eq_lit cl)) 
    then 0 
    else 
      (
       let lits = (Clause.get_lits cl) in
       let lits_eq = List.filter Term.is_eq_lit lits in 
       List.length lits_eq
      )
  in        
  let new_props =
(* assigning would be more efficient but could be error prone if new props are added *)
   {
    clauses = prob_props.clauses + 1;
    conjectures = if (Clause.is_negated_conjecture cl) then (prob_props.conjectures +1) else prob_props.conjectures;
    epr = if (Clause.is_epr cl) then (prob_props.epr+1) else prob_props.epr;
    horn = if (Clause.is_horn cl) then (prob_props.horn+1) else prob_props.horn;
    unary = if (num_cl_lits = 1) then (prob_props.unary + 1) else prob_props.unary;
    binary = if (num_cl_lits = 2) then (prob_props.binary + 1) else prob_props.binary;
    lits = prob_props.lits + num_cl_lits;
    lits_eq = prob_props.lits_eq + nun_cl_lits_eq;    
  }
  in
  new_props 
    
let get_prob_props clause_list =
  List.fold_left add_prob_props (empty_prob_props ()) clause_list
  
(*
let get_prob_props clause_list =
  let props = empty_prob_props () in
  let f cl =
    (if props.epr 
    then
      (
       props.epr <- Clause.is_epr cl
      )
    else ()
    );
    (if props.horn then
      props.horn <- Clause.is_horn cl
    else ()
    );
    (if not props.has_eq then
     ( 
       dbg D_trace (lazy ("not props.has_eq:"));
       dbg D_trace (lazy ("clause: "^(Clause.to_string cl)^(" has eq: "^(string_of_bool (Clause.has_eq_lit cl)))));
       props.has_eq <- Clause.has_eq_lit cl;
      )
    else ()
    );
    (props.unary_clauses <- 
      (
       if ((Clause.length cl) = 1) 
       then (props.unary_clauses + 1) 
       else props.unary_clauses
      )
    );
     (props.binary_clauses <- 
      (
       if ((Clause.length cl) = 2) 
       then (props.binary_clauses + 1) 
       else props.binary_clauses
      )
     );    
  
      
    (*debug*)
    (* (if not (Clause.is_horn cl) then
       (out_str "\nNon_horn\n";
       flush stdout;
       out_str (Clause.to_tptp cl))
       else ()
       );*)
    (*debug*)
  in
  List.iter f clause_list;
  props
*)

(*-------------Symbol type check--------------------------*)
(* check if there is only on symbol name for each type  *)

module NameSymMap = Map.Make(String)

(* table from symb numbes to list of symbols with the same name *)

type symb_name_table = (((Symbol.symbol list) ref) NameSymMap.t)

let create_name_symb_table () =
  let f symb symb_table =
    if not (Symbol.is_input symb)
    then symb_table
    else
      (
       let symb_name = (Symbol.get_name symb) in
       try
	 let symb_list_ref = NameSymMap.find symb_name symb_table in
	 symb_list_ref:= symb:: (!symb_list_ref);
	 symb_table
       with
	 Not_found ->
	   NameSymMap.add symb_name (ref [symb]) symb_table
      )
  in
  SymbolDB.fold f !symbol_db_ref NameSymMap.empty

let check_symb_name_table snt =
  let ok = ref true in
  let f sname symb_list_ref =
    if ((List.length !symb_list_ref) > 1)
    then
      (
       ok:= false;
       out_str (pref_str^("Type Check Faild on ")^(sname)^"\n");
       List.iter (fun symb ->
	 Symbol.to_stream_full stdout_stream symb;
	 out_str "\n")
	 !symb_list_ref
      )
    else ()
  in
  NameSymMap.iter f snt;
  (if !ok
  then ()
  else
    failwith "Type Check Faild, see help on option --symbol_type_check"
  )

let symb_type_check () =
  let snt = create_name_symb_table () in
  check_symb_name_table snt

let has_equality clause_list = 
   (val_of_override !current_options.bmc1_incremental) ||  (Clause.has_eq_lit_clause_list clause_list) 



(*------Prolific Symbols change for large theories----------------*)

(* If prolific_symb_bound is changed in current_options *)
(* then we need to recalculate which terms/clauses contain prolific symbols *)
let rec change_prolific_symb_input input_clauses =
  let rec change_prolific_symb_term t =
    match t with
    | Term.Fun (symb, args, info) ->
	Term.arg_iter change_prolific_symb_term args;
	Term.assign_has_non_prolific_conj_symb t
    | Term.Var _ -> ()
  in
  let change_prolific_symb_clause c =
    Clause.iter change_prolific_symb_term c;
    Clause.reset_has_non_prolific_conj_symb c
  in
  List.iter change_prolific_symb_clause input_clauses

(*--------------------*)
