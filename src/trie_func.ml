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







(* REIMPLEMENT: make abstract tire based on ref 
  where KeyDB is a paremeter *)

(*trie gets list of keys 
 term oriented :  if smth tries to extend leaf then exception*)

exception Trie_add_leaf_extension
exception Trie_add_short_kyelist
exception Trie_add_already_in
    
exception Trie_remove_path_too_long
exception Trie_remove_path_too_short
exception Trie_remove_remove_from_emptytrie
    
exception Is_Leaf
exception Is_Empty_Trie
exception Not_leaf 
exception Not_Node

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
    val mem    : keylist -> 'a trie -> bool 
    val long_or_in : keylist -> 'a trie -> 'a 
    val add    : keylist -> 'a -> 'a trie -> 'a trie
    val map    : ('a -> 'b) -> 'a trie -> 'b trie
    val remove : keylist -> 'a trie -> 'a trie

(* returns list of all elements of a trie*)
    val all_elem : 'a trie -> 'a list 

(* return element corr. to the keylist and raises Not_found 
  if the keylist is not in trie *)
   val  find : keylist ->'a trie -> 'a

(* returns trie corr. to strictly short keylist and raises 
   Not_found if the key is not strictly short*)
 
    val find_short : keylist ->'a trie -> 'a trie 

    val get_subtrie : key -> 'a trie -> 'a trie
	    
(* returns list of  all elem corr. to all 
   extensions of the strictly short keylist *)
	    
    val all_elem_short : keylist -> 'a trie -> 'a list 
 
(* removes a subtrie corr. to a short keylist*)
    val remove_short : keylist -> 'a trie -> 'a trie 

    val debug_apply_to_all_keys : (key -> unit) -> 'a trie -> unit

    val get_from_leaf : 'a trie -> 'a 

    val fold_level0   : (key -> 'a trie -> 'b -> 'b)->'a trie -> 'b -> 'b 
    val iter_level0   : (key -> 'a trie -> unit)->'a trie -> unit 
    val iter_elem     : ('a -> unit) -> 'a trie -> unit
    val is_empty : ('a trie) -> bool 

  end

module Make(Key:Key)  =
  struct 

    module KeyDB = Map.Make (Key)   
    type key     = Key.t
    type keylist = key list 	  
    type 'a trie =  
	Node of (('a trie) KeyDB.t) 
      | Leaf of 'a
      | Empty

    let create () = Empty

    let is_empty trie = (trie = Empty)

(* partial list return false: ab in abcd *)

    let rec mem keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
        	( try mem tl (KeyDB.find key keydb) with 
		  Not_found -> false
		 ) 
	    | Leaf(_)  -> false
	    | Empty -> false 
	   )
      |[] ->
	  ( 
	    match trie with 
	    |Node(_) -> false
	    |Leaf(_) -> true
	    |Empty   -> true
	   ) 



(* can be used in forward subsumption*)
(* returns element which subsumes the given list*)
(* otherwise raises Not_found *)
    let rec long_or_in keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
        	( try long_or_in tl (KeyDB.find key keydb) with 
		  Not_found -> raise Not_found
		 ) 
	    | Leaf(a)  -> a
	    | Empty ->  raise Not_found
	   )
      |[] ->
	  ( 
	    match trie with 
	    |Node(_) -> raise Not_found
	    |Leaf(a) -> a
	    |Empty   -> raise Not_found
	   ) 
	    
(* return element corr. to the keylist and raises Not_found 
  if the keylist is not in trie *)

let rec find keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
        	 find tl (KeyDB.find key keydb)  		   
	    | Leaf(_)  -> raise Not_found
	    | Empty -> raise Not_found
	   )
      |[] ->
	  ( 
	    match trie with 
	    |Leaf(elem) -> elem 
	    |Node(_) -> raise Not_found
	    |Empty   -> raise Not_found
	   ) 



(* returns trie corr. to a strictly short keylist*)

    let rec find_short keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
        	find_short tl (KeyDB.find key keydb)  		   
	    | Leaf(_)  -> raise Not_found
	    | Empty    -> raise Not_found
	   )
	    (* this if we want non stricck short list |[] ->  trie *)
      | [] -> 
	  match trie with 
	  |Node(_) -> trie
          |Leaf(_)  -> raise Not_found
	  |Empty    -> raise Not_found

    let get_subtrie key = function
      | Node(keydb) ->  
	  (try (KeyDB.find key keydb) with
	    Not_found -> raise Not_found)
      | Leaf(_)    -> raise Is_Leaf
      | Empty -> raise Not_found (*Is_Empty_Trie*)
	    

		
(* returns list of all elements of a trie*)
    let rec all_elem trie = 
      match trie with 
      |Leaf(elem)  -> [elem] 
      |Node(keydb) -> 
	  let f key trie rest = rest@(all_elem trie) in
	  KeyDB.fold f keydb [] 
      |Empty   -> raise Not_found
	    
(* returns list of  all elem corr. to all 
   extensions of the strictly short keylist *)
	    
    let all_elem_short keylist trie =
      let short_trie = find_short keylist trie in
      all_elem short_trie
	

    let rec map f trie = 
      match trie with
      |Node(keydb) -> 
	  Node(KeyDB.map (map f) keydb)
      | Leaf(el) ->  Leaf(f el)
      | Empty -> Empty

	    

    let rec debug_apply_to_all_keys f trie = 
      match trie with 
      |Node(keydb) ->
	  let f' key node =  
	    let ()=f key in   debug_apply_to_all_keys f node 
	  in
	  KeyDB.iter  f' keydb
      | Leaf(_)  -> ()
      | Empty -> () 

	    
    let rec create_from_keys keylist elem = 
      match keylist with 
      |key::tl  ->
	  Node((KeyDB.add key (create_from_keys tl elem)  KeyDB.empty))
      |[] -> Leaf(elem)
	    
    let rec add keylist elem trie =
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
		(
		 try 
		   Node (KeyDB.add key (add tl elem  (KeyDB.find key keydb)) keydb) 
		 with 
		   Not_found -> 
		     Node(KeyDB.add key (create_from_keys tl elem) keydb)    	
		)   
	    | Leaf(_)  -> raise Trie_add_leaf_extension
	    | Empty    -> create_from_keys keylist elem
	   )
      |[] ->
	  ( 
	    match trie with 
	    |Node(_) -> raise Trie_add_short_kyelist
	    |Leaf(_) -> raise Trie_add_already_in
	    |Empty   -> Empty
	   ) 



    let rec remove keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) -> 
		let new_tail_trie =
		  remove tl (KeyDB.find key keydb) in	  
                if new_tail_trie = Empty 
                then 		  
		  let new_keydb = KeyDB.remove key keydb in
		  if (KeyDB.is_empty new_keydb) 
		  then Empty
		  else Node(new_keydb)
		else Node (KeyDB.add key new_tail_trie keydb)
	    | Leaf(_)  -> raise Trie_remove_path_too_long
	    | Empty -> raise Trie_remove_path_too_long
	   )
      |[] ->    
	  (
	   match trie with 
	   |Leaf(_) -> Empty
	   |Node(_) -> raise Trie_remove_path_too_short
	   |Empty   -> raise Trie_remove_remove_from_emptytrie
	  ) 	  

(* removes a subtrie corr. to a short keylist*)
let rec remove_short keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
		let new_tail_trie =
		  remove_short tl (KeyDB.find key keydb) in	  
                if new_tail_trie = Empty 
                then 		  
		  let new_keydb = KeyDB.remove key keydb in
		  if (KeyDB.is_empty new_keydb) 
		  then Empty
		  else Node(new_keydb)
		else Node (KeyDB.add key new_tail_trie keydb)		   
	    | Leaf(_)  -> raise Not_found
	    | Empty    -> raise Not_found
	   )
      |[] -> Empty

(*------------ extras ----------*)
    let get_from_leaf = function 
      | Leaf(x) -> x 
      | _ -> raise Not_leaf

    let fold_level0 f trie a = 
      match trie with 
      |Node(keydb) -> 
	  let f' key subtrie a = f key subtrie a in 
	  KeyDB.fold f' keydb a 
      | _ -> 
	  raise Not_Node
 
    let iter_level0 f trie = 
      match trie with 
      |Node(keydb) -> 
	  let f' key subtrie = f key subtrie in 
	  KeyDB.iter f' keydb 
      | _ -> raise Not_Node

    let rec iter_elem f trie = 
      match trie with 
      |Node(keydb) -> 
	  let f' _key subtrie = iter_elem f subtrie in 
	  KeyDB.iter f' keydb 
      |Leaf elem -> f elem
      |Empty -> ()
	    
 

  end
    
    
