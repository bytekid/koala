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






(* use this DB if there is already fast key assignd (use it in ElemDB.compare) 
   if you want that DB will assign fast key then use abstAssignDB
   which is the same except of ElemDB has assign_fast_key and 
   when elements is added DB assigns a fast key*)

open Lib

module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
  end

module type AbstDB =
  sig   
    type elem
    type abstDB 
    val create     : unit -> abstDB 
    val create_name : string -> abstDB
    val mem        : elem -> abstDB -> bool   
    val add        : elem -> abstDB -> abstDB
    val add_ref    : elem -> abstDB ref -> elem
    val remove     : elem -> abstDB -> abstDB 
    val find       : elem -> abstDB -> elem
     (* size is a number of elements in DB*)
    val size  : abstDB -> int
    val map        : (elem -> elem) -> abstDB -> abstDB  
    val fold        : (elem -> 'a -> 'a) -> abstDB -> 'a -> 'a
    val iter        : (elem -> unit) -> abstDB -> unit
    val get_name    : abstDB -> string

    (** Return the unique identifier of the database *)
    val get_db_id   : abstDB -> int

    val to_stream   : 
	'a string_stream -> ('a string_stream -> elem -> unit) ->
	  string -> abstDB -> unit

    val out            : 
	(out_channel string_stream -> elem -> unit) ->
	  string -> abstDB -> unit
 
(*    val to_stream   : 'a string_stream -> string -> abstDB -> unit*)
    val to_string   : (Buffer.t string_stream -> elem  -> unit) 
      -> string -> abstDB ->  string

(*    val to_string : (elem -> string) -> string -> abstDB ->string*)

 end	


module Make (El : ElemDB) : (AbstDB with type elem = El.t)
