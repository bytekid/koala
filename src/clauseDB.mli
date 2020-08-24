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

type clause   = Clause.clause

type clauseDB

val create      : unit -> clauseDB
val create_name : string -> clauseDB
val mem         : clause -> clauseDB -> bool
 
(* when adding clause literals are not added to termDB*)
val add         : clause -> clauseDB -> clauseDB

(* the same as add but returns clause from clauseDB which 
 is added if it was not there already*)

val add_ref     : clause -> clauseDB ref -> clause

(*remove clause but not literals in the clause *)
val remove      : clause -> clauseDB -> clauseDB
val find        : clause -> clauseDB -> clause
val size        : clauseDB -> int
val map         : (clause -> clause) -> clauseDB -> clauseDB
val fold        : (clause -> 'a -> 'a) -> clauseDB -> 'a -> 'a
val iter        : (clause -> unit) -> clauseDB -> unit


val get_name    : clauseDB -> string

val to_stream   : 'a string_stream -> clauseDB -> unit
val out         : clauseDB -> unit

val to_string   : clauseDB -> string
