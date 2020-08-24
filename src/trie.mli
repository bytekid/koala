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
  no keylist can be a proper subkeylist 
  this implementation is based on hash tables and 
  should be good when used in non-perfect discr tree*)

open Lib
  

    
module type Key = 
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
(* init_num_of_keys: expected number of elem in each node *)
    val init_num_of_keys : int
  end
 
 
module type Trie = 
  sig 
   
    exception Trie_add_leaf_extension
    exception Trie_add_short_kyelist
    exception Trie_add_emptylist_to_emptytrie
    exception Trie_remove_path_too_long
    exception Trie_remove_path_too_short
    exception Trie_remove_remove_from_emptytrie
    exception Is_Leaf
    exception Is_Empty_Trie
    exception Not_Node
    exception Not_leaf	    
    exception Not_in_tree

    type 'a trie
    type key 
    type keylist = key list
(* create with an expected number of keys *)
    val create : unit -> 'a trie
    val is_empty : ('a trie) -> bool 
    val get_from_leaf : 'a trie -> 'a ref_elem
    val get_subtrie   : key -> 'a trie -> 'a trie
    val fold_level0   : (key -> 'a trie -> 'b -> 'b)->'a trie -> 'b -> 'b 
    val iter_level0   : (key -> 'a trie -> unit)->'a trie -> unit 
    val iter_elem     : ('a ref_elem -> unit) ->  'a trie -> unit
    val mem         : keylist -> 'a trie -> bool 
    val find          : keylist -> 'a trie -> 'a ref_elem  
    val add_path    : keylist -> ('a trie) ref -> 'a ref_elem

(* remove_path/_ret can raise:
    Trie_remove_path_too_long
    Trie_remove_path_too_short
    Trie_remove_remove_from_emptytrie
    Not_in_tree
 *)
    val remove_path : keylist -> ('a trie) ref -> unit
    val remove_path_ret : keylist -> ('a trie) ref -> 'a ref_elem
(*    val map    : ('a elem -> 'a elem) ->'a trie ->'a trie *)
(*  debug&test  *)
(*    val debug_apply_to_all_keys : (key -> unit) ->'a trie -> unit *)
end

module Make (MKey : Key) : ( Trie with type key = MKey.t)
