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





(*--------------- OLD: not used and not supported at the moment -------------------------------------*)

open Lib 
open Statistics
open Logic_interface 


let prolif_bound () = 30
(* (get_val_stat num_of_input_clauses)/5000*)


(*let prolif_bound_ref = ref 100*)


type clause_sig = 
    {
     clause     : clause;
     symb_list  : symbol list; 
   }


module SigTable = SHtbl

(*
(*------------------Large Theories--------------------------------*)


*)


(*----Create clause_sig-------------*)

let eligible_symb symb  = 
  not (symb == Symbol.symb_neg)

let rec fill_sig_term sig_table term =
  match term with 
  |Term.Fun (symb,args,_) -> 
      (if eligible_symb symb then
	SigTable.replace sig_table symb symb
      else ());
      Term.arg_iter (fill_sig_term sig_table) args
  |Term.Var _ -> ()

let create_clause_sig clause = 
  let lits = Clause.get_literals clause in
  let sig_table = SigTable.create 7 in
  List.iter (fill_sig_term sig_table) lits;
  let symb_list = SigTable.fold (fun s _ list -> (s::list)) sig_table [] in 
  {clause = clause;
   symb_list = symb_list}


(*------Table for Axioms---------*)

let table_gr_axioms = 
  SigTable.create (SymbolDB.size !symbol_db_ref)


let table_non_gr_axioms = 
  SigTable.create (SymbolDB.size !symbol_db_ref)


let add_ax_table_clause ax_table clause = 
  let clause_sig = create_clause_sig clause in
  let f symb =  
    try 
      let clause_sig_list_ref = SigTable.find ax_table symb in
      clause_sig_list_ref:= clause_sig::(!clause_sig_list_ref)
    with 
      Not_found -> 
	SigTable.add ax_table symb (ref [clause_sig])
  in 
  List.iter f clause_sig.symb_list


let fill_tables clause_list = 
  let f_table clause = 
    if (Clause.is_ground clause) then
      add_ax_table_clause table_gr_axioms clause
    else
      add_ax_table_clause table_non_gr_axioms clause
  in
  List.iter f_table clause_list

(*
  let fill_tables clause_list = 
  List.iter (add_ax_table_clause table_axioms) clause_list
 *)

let get_symb_list clause_list = 
  let f rest clause = 
    let cl_sig = create_clause_sig clause in
    cl_sig.symb_list@rest
  in
  List.fold_left f [] clause_list
    

(*
  let not_considered_ax_gr_symb symb =
  (not (Symbol.get_bool_param Symbol.large_ax_considered_gr symb))

  let not_considered_ax_non_gr_symb symb =
  (not (Symbol.get_bool_param Symbol.large_ax_considered_non_gr symb))
 *)

let not_considered_ax_symb ground_flag symb = 
  if ground_flag 
  then 
    (not (Symbol.get_bool_param Symbol.large_ax_considered_gr symb)) 
  else
    (not (Symbol.get_bool_param Symbol.large_ax_considered_non_gr symb))

let not_considered_ax_clause clause =
  (not (Clause.get_bool_param Clause.large_ax_considered clause))


(* symb_filter and clause_filter should check and assign considered_ax_symb *)
(*  *)

let get_axioms_next_keys ground_flag table_ax symb_filter clause_filter symb_list = 
  let f (ax_rest,symb_rest) symb =
    if (symb_filter symb)
    then 
      begin
	try	
	  (*out_str ("Try to find: "^(Symbol.to_string symb)^"\n");*)
	  let clause_sig_list_ref = SigTable.find table_ax symb in
	  let g (ax_rest2,symb_rest2) clause_sig = 
	    if (clause_filter clause_sig)
	    then
	      (
	       let new_symb_list =  
		 (List.filter (not_considered_ax_symb ground_flag) 
		    clause_sig.symb_list)
		 @symb_rest2 in
	       let new_ax_list = clause_sig.clause::ax_rest2 in	     
	       (new_ax_list,new_symb_list) 
	      )
	    else (ax_rest2,symb_rest2)
	  in
	  List.fold_left g (ax_rest,symb_rest) !clause_sig_list_ref
	with Not_found -> 
	  (* some symbols can be only in one of the tables *)
	  (ax_rest,symb_rest)
      end      	  
    else (ax_rest,symb_rest)
  in
  List.fold_left f ([],[]) symb_list 

    
let non_prolif_fun symb = 
(*  out_str ("Symb: "^(Symbol.to_string symb)^" Num occ: "
    ^(string_of_int (Symbol.get_num_input_occur symb))
    ^" prolif_bound: "^(string_of_int (prolif_bound ()))^"\n");*)
  (Symbol.get_num_input_occur symb) <= (prolif_bound ())
    
let symb_gr_filter symb = 
  if (not (Symbol.get_bool_param Symbol.large_ax_considered_gr symb))
      &&
    (non_prolif_fun symb)
  then 
    ((*out_str ("Gr Symb: "^(Symbol.to_string symb)^"\n");*)
      Symbol.set_bool_param true Symbol.large_ax_considered_gr symb;
     true
    )
  else false 

let clause_gr_filter clause_sig = 
  if (not (Clause.get_bool_param Clause.large_ax_considered clause_sig.clause))
  then
    (
(*  out_str ("Gr Clause: "^(Clause.to_string clause_sig.clause)^"\n");*)
     Clause.set_bool_param true Clause.large_ax_considered clause_sig.clause;
     true)
  else 
    false

let symb_non_gr_filter symb = 
  if (not (Symbol.get_bool_param Symbol.large_ax_considered_non_gr symb))
  then 
    (
     Symbol.set_bool_param true Symbol.large_ax_considered_non_gr symb;
     true
    )
  else false 


let clause_non_gr_filter clause_sig = 
  if (not (Clause.get_bool_param Clause.large_ax_considered clause_sig.clause))
  then    
(* if there exists a  symbol then *)
(* there should be a symb which is considered *)
    if 

(*
  (*  (not (List.exists (fun symb -> Symbol.get_type symb = Symbol.Fun) 
      clause_sig.symb_list)
      )
      ||*)
  (List.exists (fun symb -> 
  (* (Symbol.get_type symb = Symbol.Fun) 
     &&*) 
  not (non_prolif_fun symb)
  ||
  (
  (Symbol.get_bool_param Symbol.large_ax_considered_gr symb)
  ||  
  (Symbol.get_bool_param Symbol.large_ax_considered_non_gr symb)
  )
  )
 *)

      (not (List.exists non_prolif_fun clause_sig.symb_list)
      )
||
  (List.exists (fun symb -> 
    (non_prolif_fun symb) 
      &&
    (
     (Symbol.get_bool_param Symbol.large_ax_considered_gr symb)
   ||  
     (Symbol.get_bool_param Symbol.large_ax_considered_non_gr symb)
)
               )       
     clause_sig.symb_list)
    
    then
      ((*out_str ("Non Gr Clause: "^(Clause.to_string clause_sig.clause)^"\n");*)
	Clause.set_bool_param true Clause.large_ax_considered clause_sig.clause;
       true)
    else 
      false
  else
    false


let get_axioms_next_keys_all symb_list = 
  let (gr_ax,gr_keys) =  
    get_axioms_next_keys 
      true table_gr_axioms symb_gr_filter clause_gr_filter symb_list in
  let (non_gr_ax,non_gr_keys) = 
    get_axioms_next_keys 
      false table_non_gr_axioms symb_non_gr_filter clause_non_gr_filter symb_list in
  out_str ("Ground Axioms added: "^
	   (Clause.clause_list_to_string gr_ax)^"\n");
  out_str ("Non Ground Axioms added: "^
	   (Clause.clause_list_to_string non_gr_ax)^"\n");
  (gr_ax@non_gr_ax,gr_keys@non_gr_keys)
    

(*
  let increase_prolific_bound_by n = 
  prolif_bound_ref:=!prolif_bound_ref*n  
 *)

let get_all_non_considered clause_list = 
  List.filter (fun c -> not (Clause.get_bool_param Clause.large_ax_considered c))
    clause_list
