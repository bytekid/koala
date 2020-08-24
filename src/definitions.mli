(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2017 Konstantin Korovin and The University of Manchester. 
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


open Logic_interface

type def_env 


val create_def_env : unit -> def_env

(* TODO: after retyping also retype definitions with var mappings *)
(* it is sound as it is now but definitions will need to be regenerated in def_env_glb to be useful *)
val def_env_glb : def_env (* global definitions *) 


(* returns definition: C(X,Y) \/ ~p(X) and def atom p(X), restricted to var_list *)
(* returend lit should be used in the reduced clause and compl(lit) is used in the definition *)

(* let add_def de parent_clause var_list lit_list = *)

val add_def : def_env -> parent:clause -> var list -> lit list -> lit * clause

(* creating the other side of the reduced clause; lit list = literals in the clause *)
val create_def_reduced_clause : parent:clause -> lit list -> clause 
