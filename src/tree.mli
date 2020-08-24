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






exception Tree_add_already_in


module type Key =
  sig
    type t
    val compare : t -> t -> int
  end


      
module type Tree =
  sig
    type key
    type +'a tree  
    val create : unit  -> 'a tree
    val is_empty : 'a tree -> bool
    val find : key -> 'a tree -> 'a
    val mem  : key -> 'a tree -> bool
    val add  : key -> 'a -> 'a tree -> 'a tree
    val remove :  key -> 'a tree -> 'a tree
    val findf_leq : (key -> 'a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_geq : (key -> 'a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_all_geq :  (key -> 'a -> 'b list) -> key -> 'a tree -> 'b list 
    val findf_all     :  (key -> 'a -> 'b list)  -> 'a tree -> 'b list 
(*    val findf_all_leq :  ('a -> 'b list) -> key -> 'a tree -> 'b list *)
  end

module Make(Key:Key): (Tree with type key=Key.t) 
