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







type   symbol = Symbol.symbol
      
module SymKey = 
  struct 
    type t       = symbol
    let  compare = Symbol.compare_key
    let  assign_fast_key = Symbol.assign_fast_key
 end
    
module SymbolDBM =  AbstAssignDB.Make (SymKey)
type symbolDB  = {db : SymbolDBM.abstDB; mutable current_group : int}
let min_group = 0 
let max_group = Bit_vec.max_pos

let create_name name = {db = SymbolDBM.create_name name; current_group=0}
let create ()    = create_name "Symbol_DB"
let get_name sdb = SymbolDBM.get_name sdb.db
let mem  s sdb   = SymbolDBM.mem s sdb.db  
let remove s sdb = 
  {db = SymbolDBM.remove s sdb.db; current_group = sdb.current_group}
let find s sdb   = SymbolDBM.find s sdb.db
let size sdb     = SymbolDBM.size sdb.db
let map f  sdb   = {db = SymbolDBM.map f sdb.db; current_group = sdb.current_group}
let fold f sdb a = SymbolDBM.fold f sdb.db a 
let iter f sdb   = SymbolDBM.iter f sdb.db

let add_ref s sdb_ref = 
  let new_db_ref = ref (!sdb_ref).db in
  let s_added = SymbolDBM.add_ref s new_db_ref in
  sdb_ref := {db = !new_db_ref; current_group = (!sdb_ref).current_group};   
  try
    let _=(Symbol.get_group s) in  
    s
    with Symbol.Group_undef -> 
      (if (!sdb_ref).current_group > max_group 
      then 
	(!sdb_ref).current_group <- min_group
      );
      Symbol.assign_group s (!sdb_ref).current_group; 
      (!sdb_ref).current_group <- ((!sdb_ref).current_group+1);
      s  
	
(*since add_ref is diff from abstAssingDB, so add also*)
let add elem elem_db =
  let elem_db_ref = ref elem_db in
  let _= add_ref elem elem_db_ref in
  !elem_db_ref



let to_string symbol_db = 
  SymbolDBM.to_string Symbol.to_string "," symbol_db.db

(*debug*)
let get_greatest_key sdb = SymbolDBM.get_greatest_key sdb.db
