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
type clause = Clause.clause

module ClauseKey =
  struct
    type t       = clause
    let  compare = Clause.compare
  end

module ClauseDBM =  AbstDB.Make (ClauseKey)

type clauseDB  = ClauseDBM.abstDB

let create_name = ClauseDBM.create_name
let create () = create_name "Clause_DB"
let mem      = ClauseDBM.mem
let remove   = ClauseDBM.remove
let find     = ClauseDBM.find
let size     = ClauseDBM.size
let map      = ClauseDBM.map
let fold     = ClauseDBM.fold
let iter     = ClauseDBM.iter

let add_ref  = ClauseDBM.add_ref 

let add  = ClauseDBM.add
    

let get_name = ClauseDBM.get_name


let to_stream s clause_db = 
  ClauseDBM.to_stream s Clause.to_stream ",\n" clause_db

let out = to_stream stdout_stream

let to_string clause_db = 
  ClauseDBM.to_string Clause.to_stream ",\n" clause_db

(*
  let to_string clause_db = 
  ClauseDBM.to_string Clause.to_string ",\n" clause_db
 *)
