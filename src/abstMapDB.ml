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







type  elem ='a 
      
module SymKey = 
  struct 
    type t       = symbol
    let  compare = Symbol.compare_key
  end
    
module SymbolDBM =  Map.Make (SymKey)
type   symbolDB  = {db: symbol SymbolDBM.t ; num_of_el: int}


let empty                 =  {db=SymbolDBM.empty; num_of_el=0}
let mem symbol symbol_db  = SymbolDBM.mem symbol symbol_db.db
    
let add (symbol:symbol) (symbol_db:symbolDB)  =  
  if (mem symbol symbol_db) then symbol_db
  else 
    let new_num_of_el = (symbol_db.num_of_el + 1) in
    let ()=(Symbol.assign_fast_key symbol new_num_of_el)
    in	 
    {db        =(SymbolDBM.add symbol symbol symbol_db.db); 
     num_of_el = new_num_of_el }
      
let find symbol symbol_db =  SymbolDBM.find symbol symbol_db.db
    

let num_of_el symbol_db = symbol_db.num_of_el    
    
let remove symbol symbol_db =  
  {db        = (SymbolDBM.remove symbol symbol_db.db); 
   num_of_el = symbol_db.num_of_el-1}
    
let map f symbol_db = 
  {db        = (SymbolDBM.map f symbol_db.db); 
   num_of_el = symbol_db.num_of_el}
    
