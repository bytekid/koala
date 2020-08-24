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

type symbol = Symbol.symbol
type stype    = Symbol.stype
      
module SymKey = 
  struct 
    type t       = symbol
    let compare = Symbol.compare_key
    let assign_fast_key = Symbol.assign_fast_key
    let assign_db_id = Symbol.assign_db_id
 end
    
module SymbolDBM =  AbstAssignDB.Make (SymKey)



type symbolDB  = 
    {db                       : SymbolDBM.abstDB;
     mutable unused_split_symb_number : int}


let get_name db = SymbolDBM.get_name db.db

let mem sym db = SymbolDBM.mem sym db.db 

let remove symb db     =  { db with db = (SymbolDBM.remove symb db.db)}
let find symb db       = SymbolDBM.find symb db.db
let size db            = SymbolDBM.size db.db
let map f db           = { db with db = (SymbolDBM.map f db.db)}
let fold f db a        = SymbolDBM.fold f db.db a
let iter f db          = SymbolDBM.iter f db.db

(* hash is a random number...*)
(*let add_sdb symb sdb_ref = 
(* in order not to reassign hash to symbs in db it is done to the input symb*)
  Symbol.assign_hash symb (Random.bits());
  let added_symb = SymbolDBM.add_ref symb sdb_ref in
  added_symb
*)
    
let add_ref symb db_ref   =
  let sdb_ref   = ref !db_ref.db in
(*  let added_symb = add_sdb symb sdb_ref in*)
  let added_symb = SymbolDBM.add_ref symb sdb_ref in
  db_ref:= {!db_ref with db = !sdb_ref};
  added_symb
    

let add symb db  = 
(*  Symbol.assign_hash symb (Random.bits());*)
  { db with db = (SymbolDBM.add symb db.db)}


let create_name name = 
  let sdb_ref = ref (SymbolDBM.create_name name) in
(*add all special symbols to db*)
(*  List.iter (fun symb -> (let _ = add_sdb symb sdb_ref in ())) *)
  List.iter 
    (fun symb -> 
      (let added_symb = SymbolDBM.add_ref symb sdb_ref in 
      Symbol.set_is_special_symb true added_symb)) 
    Symbol.special_symbols_list;
  {db = !sdb_ref;
   unused_split_symb_number=0;
 }  
    
let create ()   = 
  create_name "Symbol_DB"


(* Create a fresh split symbol and add to the database 

   Follow the TPTP convention for new names, that is, create the
   symbol as sP{n}_iProver_split.
*)
let create_new_split_symb symb_db_ref stype = 
  (* let new_symb_name = ("iProver_split_" 
     ^(string_of_int !symb_db_ref.unused_split_symb_number)) in *)

  (* Name of symbol conforming to the TPTP convention for new names *)
  let new_symb_name = 
    Format.sprintf 
      "sP%d_iProver_split" 
      !symb_db_ref.unused_split_symb_number
  in

  (* Create new split symbol *)
  let new_symb = 
    Symbol.create_from_str_type_property 
      new_symb_name stype 
      Symbol.Split 
  in
  Statistics.incr_int_stat 1 Statistics.num_of_split_atoms;
  (* Increment counter for split symbols *)
  !symb_db_ref.unused_split_symb_number <- 
    succ !symb_db_ref.unused_split_symb_number;
  Symbol.assign_is_essential_input true new_symb; 
  (* Add symbol to symbol database *)
  add_ref new_symb symb_db_ref 



let get_num_of_sym_groups db = 
  let size_db = size db in
  if Symbol.max_num_of_sym_groups > size_db then 
    size_db 
  else 
    Symbol.max_num_of_sym_groups

(*------------------------------------------*)
let to_stream s symbol_db = 
  SymbolDBM.to_stream s Symbol.to_stream "\n" symbol_db.db

let to_stream_full s symbol_db = 
  SymbolDBM.to_stream s Symbol.to_stream_full "\n" symbol_db.db

let symb_to_stream_full_filter f s symb = 
 if f symb 
 then 
   Symbol.to_stream_full s symb 
 else 
   ()

let to_stream_full_filter f s symbol_db = 
  SymbolDBM.to_stream s (symb_to_stream_full_filter f) "\n" symbol_db.db


let out = to_stream stdout_stream

let out_full = to_stream_full stdout_stream

let out_full_filter f = to_stream_full_filter f stdout_stream

let to_string symbol_db = 
  SymbolDBM.to_string Symbol.to_stream "\n" symbol_db.db



(*debug*)
let get_greatest_key db = SymbolDBM.get_greatest_key db.db
 
