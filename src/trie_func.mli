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






(*trie gets list of keys, term oriented:  
  no keylist can be a proper subkeylist *)

exception Trie_add_leaf_extension
exception Trie_add_short_kyelist
exception Trie_add_already_in

exception Trie_remove_path_too_long
exception Trie_remove_path_too_short
exception Trie_remove_remove_from_emptytrie

(* exception Is_Leaf *)
exception Is_Empty_Trie

      
module type Key = 
  sig
    type t
    val compare : t -> t -> int
  end
      
      
module type Trie = 
  sig 
    type key 
    type keylist = key list
    type 'a trie
    val create : unit  -> 'a trie
    val mem        : keylist -> 'a trie -> bool

(* long_or_in can be used in forward subsumption*)
(* returns element which subsumes the given list*)
(* otherwise raises Not_found *)
    val long_or_in : keylist -> 'a trie -> 'a 

    val add    : keylist -> 'a -> 'a trie -> 'a trie
    val map    : ('a -> 'b) -> 'a trie -> 'b trie

    val remove : keylist -> 'a trie -> 'a trie

(* returns list of all elements of a trie*)
    val all_elem : 'a trie -> 'a list 
  
(* return element corr. to the keylist and raises Not_found *)
(*  if the keylist is not in trie *)
    val  find : keylist ->'a trie -> 'a
 
(* returns trie corr. to strictly short keylist and raises *)
(*   Not_found if the key is not strictly short*)
 
    val find_short : keylist ->'a trie -> 'a trie 

    val get_subtrie : key -> 'a trie -> 'a trie
	    
(* returns list of  all elem corr. to all 
   extensions of the strictly short keylist *)
	    
    val all_elem_short : keylist -> 'a trie -> 'a list 
 
(* removes a subtrie corr. to a short keylist,*)
(* raises Not_found if no extension of the keylist is in the trie *)
    val  remove_short : keylist -> 'a trie -> 'a trie 



(*  debug&test  *)
    val debug_apply_to_all_keys : (key -> unit) -> 'a trie -> unit

(*-- extras ---*)
    val get_from_leaf : 'a trie -> 'a 

    val fold_level0   : (key -> 'a trie -> 'b -> 'b)->'a trie -> 'b -> 'b 
    val iter_level0   : (key -> 'a trie -> unit)->'a trie -> unit 
    val iter_elem     : ('a -> unit) -> 'a trie -> unit
    val is_empty : ('a trie) -> bool 

  end

module Make (MKey : Key) : ( Trie with type key = MKey.t)
