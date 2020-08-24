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







(*trie gets list of keys 
 term oriented :  if smth tries to extend leaf then exception*)

open Lib


module type Key = 
  sig
    type t
    val equal : t -> t -> bool
    val hash : t -> int
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
    type key 
    type keylist = key list
    type 'a trie
    val create : unit -> ('a trie)
    val is_empty : ('a trie) -> bool 
    val get_from_leaf : 'a trie -> 'a ref_elem
    val get_subtrie   : key -> 'a trie -> 'a trie
    val fold_level0   : (key -> 'a trie -> 'b -> 'b)->'a trie -> 'b -> 'b 
    val iter_level0   : (key -> 'a trie -> unit) -> 'a trie -> unit 
    val iter_elem     : ('a ref_elem -> unit) -> 'a trie -> unit
    val mem    : keylist -> 'a trie -> bool 
    val find          : keylist -> 'a trie -> 'a ref_elem  
    val add_path : keylist -> ('a trie) ref -> 'a ref_elem
    val remove_path     : keylist -> ('a trie) ref -> unit
    val remove_path_ret : keylist -> ('a trie) ref -> 'a ref_elem
(*    val map    : ('a elem -> 'a elem) -> 'a trie -> 'a trie *)
(*    val debug_apply_to_all_keys : (key -> unit) ->  'a trie -> unit *)
end

module Make(Key:Key)  =
  struct 
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

    module KeyDB = Hashtbl.Make (Key)   
    type key     = Key.t
    type keylist = key list 	  
    type 'a trie =  
	Node of ((('a trie) ref) KeyDB.t) 
      | Leaf of ('a ref_elem)
      | Empty_Trie
	  
    let create () = Empty_Trie

    let is_empty trie = (trie = Empty_Trie)

    let get_from_leaf = function 
      | Leaf(x) -> x 
      | _ -> raise Not_leaf
 
    
    let  get_subtrie key = function
      | Node(keydb) ->  
	  (try !(KeyDB.find keydb key) with
	    Not_found -> raise Not_found)
      | Leaf(_)    -> raise Is_Leaf
      | Empty_Trie -> raise Not_found (*Is_Empty_Trie*)

    let fold_level0 f trie a = 
      match trie with 
      |Node(keydb) -> 
	  let f' key trie_ref a = f key !trie_ref a in 
	  KeyDB.fold f' keydb a 
      | _ -> raise Not_Node
 
     let iter_level0 f trie = 
      match trie with 
      |Node(keydb) -> 
	  let f' key trie_ref = f key !trie_ref in 
	  KeyDB.iter f' keydb 
      | _ -> raise Not_Node
 
    let rec iter_elem f trie = 
      match trie with 
      |Node(keydb) -> 
	  let f' _key trie_ref = iter_elem f !trie_ref in 
	  KeyDB.iter f' keydb 
      |Leaf ref_elem -> f ref_elem
      |Empty_Trie -> ()
	    

(* partial list return false: ab in abcd *)

    let rec mem keylist trie = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match trie with 
	    |Node(keydb) ->
        	( try mem tl !(KeyDB.find keydb key) with 
		  Not_found -> false
		 ) 
	    | Leaf(_)  -> false
	    | Empty_Trie -> false 
	   )
      |[] ->
	  ( 
	    match trie with 
	    |Node(_) -> false
	    |Leaf(_) -> true
	    |Empty_Trie   -> true
	   ) 

(* return element corr. to the keylist and raises Not_found
  if the keylist is not in trie *)

let rec find keylist trie =
      match keylist with
      |key::tl ->
          (
            match trie with
            |Node(keydb) ->
                 find tl !(KeyDB.find keydb key)
            | Leaf(_)    -> raise Not_found
            | Empty_Trie -> raise Not_found
           )
      |[] ->
          (
            match trie with
            |Leaf(elem)  -> elem
            |Node(_)     -> raise Not_found
            |Empty_Trie  -> raise Not_found
           )




(*
    let rec map f trie = 
      match trie with
      |Node(keydb) -> 
	  Node(KeyDB.map (map f) keydb)
      | Leaf(el) ->  Leaf(f el)
      | Empty_Trie -> Empty_Trie

	    
*)
(*
    let rec debug_apply_to_all_keys f trie = 
      match trie with 
      |Node(keydb) ->
	  let f' key node =  
	    let ()=f key in   debug_apply_to_all_keys f node 
	  in
	  KeyDB.iter  f' keydb
      | Leaf(_)  -> ()
      | Empty_Trie -> () 

*)	    
 
(* works but not tail rec *)
(*
   let rec create_from_keys keylist = 
      match keylist with 
      |key::tl  -> 
	  let new_kdb = KeyDB.create Key.init_num_of_keys in 
	  let (rest_trie,ref_leaf) = create_from_keys tl in
          let () = KeyDB.add new_kdb key (ref rest_trie) in
	  (Node(new_kdb),ref_leaf)
      |[] -> let ref_leaf = ref Empty_Elem in
	  (Leaf(ref_leaf),ref_leaf)
*)

    let rec create_from_keys' current_db current_key key_list = 
      match key_list with 
      |key::tl  -> 
	  let new_kdb = KeyDB.create Key.init_num_of_keys in 
          let () = KeyDB.add current_db current_key (ref (Node (new_kdb) )) in
	  create_from_keys' new_kdb key tl 
      |[] -> 
	  let ref_leaf = ref Empty_Elem in
	  let () = KeyDB.add current_db current_key (ref ( Leaf (ref_leaf))) in
	  ref_leaf

    let create_from_keys keylist =       
      match keylist with 
      |key::tl  -> 
	  let new_kdb = KeyDB.create Key.init_num_of_keys in 
	  let ref_leaf = create_from_keys' new_kdb key tl in 
	  (Node(new_kdb),ref_leaf)
      |[] ->
	  let ref_leaf = ref Empty_Elem in
	  (Leaf(ref_leaf),ref_leaf)

   
	    
    let rec add_path keylist ref_trie =
      match keylist with 
      |key::tl -> 
	  ( 
	    match !ref_trie with 
	    |Node(keydb) ->
		(try 
		  let n_trie = (KeyDB.find keydb key) in  
		  add_path tl n_trie 
		with 		  
		  Not_found -> 
		    let (new_trie,ref_leaf)= create_from_keys tl in
		    let () = KeyDB.add keydb key (ref new_trie) in
		    ref_leaf
		)
	    | Leaf(_)  -> raise Trie_add_leaf_extension
	    | Empty_Trie  -> 
		let (new_trie,ref_leaf) = create_from_keys keylist in
                let ()= (ref_trie := new_trie)  in
		ref_leaf
	   )
      |[] ->
	  ( 
	    match !ref_trie with 
	    |Node(_) -> raise Trie_add_short_kyelist
	    |Leaf(ref_leaf) -> ref_leaf
	    |Empty_Trie   -> raise Trie_add_emptylist_to_emptytrie
	   ) 	

    exception Not_in_tree
 
    let rec remove_path keylist ref_trie = 
      try
	(match keylist with 
	|key::tl -> 
	  ( 
	    match !ref_trie with 
	    |Node(keydb) -> 
		remove_path tl (KeyDB.find keydb key);  	  
                if !(KeyDB.find keydb key)= Empty_Trie 
                then 
		  (
		   KeyDB.remove keydb key; 
		   if (KeyDB.length keydb)=0 
		   then ref_trie := Empty_Trie
		  )
	    | Leaf(_)  -> raise Trie_remove_path_too_long
	    | Empty_Trie -> raise Trie_remove_path_too_long
	   )
      |[] ->    
	  (
	   match !ref_trie with 
	   |Node(_) -> raise Trie_remove_path_too_short
	   |Leaf(_) -> (ref_trie := Empty_Trie)
	   |Empty_Trie   -> raise Trie_remove_remove_from_emptytrie
	  ) 
     ) with Not_found -> raise Not_in_tree

  let rec remove_path_ret keylist ref_trie = 
    try
      match keylist with 
      |key::tl -> 
	  ( 
	    match !ref_trie with 
	    |Node(keydb) -> 
		let ref_elem = remove_path_ret tl (KeyDB.find keydb key) in  	  
                if !(KeyDB.find keydb key)= Empty_Trie 
                then 
		  (
		   KeyDB.remove keydb key; 
		   if (KeyDB.length keydb)=0 
		   then ref_trie := Empty_Trie;
		   ref_elem )
		else ref_elem	       
	    | Leaf(_)  -> raise Trie_remove_path_too_long
	    | Empty_Trie -> raise Trie_remove_path_too_long
	   )
      |[] ->    
	  (
	   match !ref_trie with 
	   |Node(_) -> raise Trie_remove_path_too_short
	   |Leaf(ref_elem) -> (ref_trie := Empty_Trie; ref_elem)
	   |Empty_Trie   -> raise Trie_remove_remove_from_emptytrie
	  )
    with Not_found -> raise Not_in_tree
 end
