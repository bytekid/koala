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







type tmp = bool 
type solver = tmp

type var = int
type var_id = int

type lit = int

type lit_list = lit list

type solver_out = Sat  | Unsat 

type lit_val    = True | False | Any

type lit_sign   = Pos  | Neg

exception Unsatisfiable

exception Create_var_error


let create_solver () = false
    
let create_variable solver int  = int

let create_lit solver bool var = if bool then var else -var

let lit_sign  lit = if lit >0 then Pos else Neg
let lit_to_string lit = string_of_int lit

(* can raise Unsatisfiable if trivialy unsat *)
let add_clause solver lit_list  = ()

let get_var_id lit = 0

let solve solver = Sat

(*let var_val solver var = Any *)
let lit_val solver lit = Any 
