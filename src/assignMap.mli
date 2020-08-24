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



val assign_map_counter : int ref

module type KeyEl = 
  sig
		type t
    type e (* t -> element *)
    (* val compare : t -> t -> int *)
		val hash : t -> int 
		val equal : t -> t -> bool  
    val assign_fast_key : e -> int -> unit
    val assign_db_id : e -> int -> unit
  end

module Make :
  functor (MKey : KeyEl) ->
    sig
      type key = MKey.t
      type e = MKey.e
      type assign_map 
			(* create_name size name *)
      val create : int -> string -> assign_map
      val get_name : assign_map -> string
      val get_map_id : assign_map -> int
      val mem : assign_map -> key -> bool
      val find : assign_map -> key -> e
      val size : assign_map -> int
      val fold : (key -> e -> 'a -> 'a) -> assign_map -> 'a -> 'a
      val iter : (key -> e -> unit) -> assign_map -> unit
      val add : assign_map -> key -> e -> e
      val remove : assign_map -> key -> unit
      val to_stream :
        'a Lib.string_stream ->
        ('a Lib.string_stream -> e -> unit) -> string -> assign_map -> unit
      val out :
        (out_channel Lib.string_stream -> e -> unit) ->
        string -> assign_map -> unit
      val to_string :
        (Buffer.t Lib.string_stream -> e -> unit) ->
        string -> assign_map -> string
      val get_key_counter : assign_map -> int
    end
