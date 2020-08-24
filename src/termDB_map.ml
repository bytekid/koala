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

type term = Term.term
      
module TermKey = 
  struct 
    type t       = term
    let  compare = Term.compare_key
    let  assign_fast_key = Term.assign_fast_key
 end
    
module TermDBM =  AbstAssignDB.Make (TermKey)
type termDB  = TermDBM.abstDB

let create_name = TermDBM.create_name
let create () = create_name "Term_DB"
let mem    = TermDBM.mem   
let remove = TermDBM.remove
let find   = TermDBM.find
let size   = TermDBM.size
let map    = TermDBM.map
let get_name = TermDBM.get_name
let fold = TermDBM.fold
let iter = TermDBM.iter

let to_stream s term_db = 
  TermDBM.to_stream s Term.to_stream "\n" term_db

let out = to_stream stdout_stream

let to_string term_db = 
  TermDBM.to_string Term.to_stream "\n" term_db




(* add with sharing*)
    
let rec add_ref t db_ref = 
  try find t !db_ref
  with 
    Not_found->
      match t with
      |Term.Fun(sym, args,info) ->
	  let new_args = Term.arg_map (fun t' -> add_ref t' db_ref) args in
	  let new_term = Term.create_fun_term_args sym new_args in 
(* add usefull info for terms*)	  
	  let ()= Term.assign_fun_all new_term in
	  db_ref:=TermDBM.add new_term !db_ref;
	  new_term	   
      |Term.Var(_,_) ->
	  db_ref:=TermDBM.add t !db_ref;
	  Term.assign_var_all t;
	  t


 
let add t db =
  let db_ref = ref db in
  let _ = add_ref t db_ref in
  !db_ref
    
(*debug*)
 let get_greatest_key = TermDBM.get_greatest_key
