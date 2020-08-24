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

type symbol   = Symbol.symbol
type stype    = Symbol.stype

type symbolDB  
  
val create      : unit -> symbolDB
val create_name : string -> symbolDB
val mem         : symbol -> symbolDB -> bool 
val add         : symbol -> symbolDB -> symbolDB
val add_ref     : symbol -> symbolDB ref -> symbol
val remove      : symbol -> symbolDB -> symbolDB 
val find        : symbol -> symbolDB -> symbol
val size        : symbolDB -> int
val map         : (symbol -> symbol)-> symbolDB -> symbolDB 
val fold        : (symbol -> 'a -> 'a) -> symbolDB -> 'a -> 'a
val iter        : (symbol -> unit) -> symbolDB -> unit

(** Create a fresh split symbol and add it to the database

    Follow the TPTP convention for new names, that is, create the
    symbol as sP{n}_iProver_split.
*)
val create_new_split_symb : symbolDB ref ->  stype -> symbol

val get_name    : symbolDB ->string

val get_num_of_sym_groups : symbolDB -> int

val to_stream   : 'a string_stream -> symbolDB -> unit
val out         :  symbolDB -> unit
val out_full    :  symbolDB -> unit

val out_full_filter    :  (symbol -> bool) -> symbolDB -> unit

val to_string   : symbolDB ->string

(*debug*)
val get_greatest_key : symbolDB -> int
