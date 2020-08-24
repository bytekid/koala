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

exception VecIndex_add_leaf_extension
exception VecIndex_add_short_kyelist
exception VecIndex_add_emptylist_to_emptyindex
exception VecIndex_remove_path_too_long
exception VecIndex_remove_path_too_short
exception VecIndex_remove_remove_from_emptyindex


module type Key =
  sig
    type t
    val compare : t -> t -> int
  end

module type Index = 
  sig
    type key
    type keylist = key list
    type 'a index
    val create : unit  -> 'a index
(* copied from trie_func *) 
    val mem    : 'a index -> keylist -> bool
    val add    : 'a index -> keylist -> 'a ref_elem
    val remove : 'a index -> keylist -> unit

(* return element corr. to the keylist and raises Not_found
  if the keylist is not in index *)
    val  find : 'a index -> keylist -> 'a ref_elem

(* new for feature indexes*)
    val findf_leq : 'a index -> ('a -> 'b option) -> keylist -> 'b option
    val findf_geq : 'a index -> ('a -> 'b option) -> keylist -> 'b option

    val findf_all_geq :
        'a index -> (keylist -> 'a ref_elem -> 'b list) -> keylist -> 'b list 

(*    val findf_all : (keylist -> 'a ref_elem -> 'b list) -> ('a index) ref -> 'b list *)
(*
    val findf_all_leq :  
	('a ref_elem -> 'b list) -> keylist -> ('a index) ref -> 'b list 
*)  
 end

module Make(Key:Key)  =
  struct
    module KeyDB = Tree.Make (Key)
    type key     = Key.t
    type keylist = key list
    type 'a index_plain =
(*        Node of ((('a index) ref)  KeyDB.tree) *)
        Node of (('a index)  KeyDB.tree) 
      | Leaf of 'a ref_elem
      | Empty
          
    and
          'a index = ('a index_plain) ref  
          
    let create () = ref Empty 

(* partial list return false: ab in abcd *)

    let rec mem index keylist = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match !index with 
	    |Node(keydb) ->
        	( try mem (KeyDB.find key keydb) tl with 
		  Not_found -> false
		 ) 
	    | Leaf(_)  -> false
	    | Empty -> false 
	   )
      |[] ->
	  ( 
	    match !index with 
	    |Node(_) -> false
	    |Leaf(_) -> true
	    |Empty   -> true
	   ) 
 
(* return element corr. to the keylist and raises Not_found
  if the keylist is not in index *)

let rec find index keylist =
      match keylist with
      |key::tl ->
          (
            match !index with
            |Node(keydb) ->
                 find (KeyDB.find key keydb) tl
            | Leaf(_)    -> raise Not_found
            | Empty -> raise Not_found
           )
      |[] ->
          (
            match !index with
            |Leaf(elem)  -> elem
            |Node(_)     -> raise Not_found
            |Empty  -> raise Not_found
           )


    let rec create_from_keys keylist = 
      match keylist with 
      |key::tl  -> 	   
	  let (rest_index,ref_leaf) = create_from_keys tl in
          let new_kdb = KeyDB.add  key (rest_index) (KeyDB.create ()) in
	  (ref (Node(new_kdb)),ref_leaf)
      |[] -> let ref_leaf = ref Empty_Elem in
	(ref (Leaf(ref_leaf)),ref_leaf)
	  
	(*    
    let create_from_keys keylist =  
      (create_from_keys_plain keylist)
*)
    let rec add index keylist =
      match keylist with 
      |key::tl -> 
	  ( 
	    match !index with 
	    |Node(keydb) ->
		(try 
		  let n_index = (KeyDB.find key keydb) in  
		  add n_index tl
		with 		  
		  Not_found -> 
		    let (new_index,ref_leaf) = create_from_keys tl in
		    index := 
		      Node((KeyDB.add key new_index keydb));
		    ref_leaf
		)
	    | Leaf(_)  -> raise VecIndex_add_leaf_extension
	    | Empty  -> 
		let (new_index,ref_leaf) = create_from_keys keylist in
                index := !new_index;
		ref_leaf
	   )
      |[] ->
	  ( 
	    match !index with 
	    |Node(_) -> raise VecIndex_add_short_kyelist
	    |Leaf(ref_leaf) -> ref_leaf
	    |Empty   -> raise VecIndex_add_emptylist_to_emptyindex
	   ) 
	

    let rec remove index keylist = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match !index with 
	    |Node(keydb) -> 
		remove (KeyDB.find key keydb)  tl;  	  
                if !(KeyDB.find key keydb)= Empty 
                then 
		  (
		   let new_keydb = KeyDB.remove key keydb in
		   if (KeyDB.is_empty new_keydb) 
		   then index := Empty
		   else index := Node(new_keydb)
		  )
	    | Leaf(_)  -> raise VecIndex_remove_path_too_long
	    | Empty -> raise VecIndex_remove_path_too_long
	   )
      |[] ->    
	  (
	   match !index with 
	   |Node(_) -> raise VecIndex_remove_path_too_short
	   |Leaf(_) -> (index := Empty)
	   |Empty   -> raise VecIndex_remove_remove_from_emptyindex
	  ) 

(* new *)
exception VecIndex_findf_leq_keylist_too_long
exception VecIndex_findf_leq_keylist_too_short

    let rec findf_leq index f keylist =
	match keylist with 
	| key::tl -> 
	    (match !index with 
	    |Node(keydb) -> 
(*  		(KeyDB.findf_leq (findf_leq f tl) key keydb)*)
 		(KeyDB.findf_leq (fun _ x -> findf_leq x f tl) key keydb)
	    |Leaf(_)-> raise VecIndex_findf_leq_keylist_too_long
	    |Empty -> None
	    )	    
	|[] ->
	    (match !index with 
	    |Leaf(elem_ref) -> 
		(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> None
		)
	    |Node(_) -> raise VecIndex_findf_leq_keylist_too_short
	    |Empty -> None
	    )

exception VecIndex_findf_geq_keylist_too_long
exception VecIndex_findf_geq_keylist_too_short

    let rec findf_geq index f keylist =
	match keylist with 
	| key::tl -> 
	    (match !index with 
	    |Node(keydb) -> 
(*  		(KeyDB.findf_geq (findf_geq f tl) key keydb)*)
		(KeyDB.findf_geq (fun _ x -> findf_geq x f tl) key keydb)
	    |Leaf(_)-> raise VecIndex_findf_geq_keylist_too_long
	    |Empty -> None
	    )	    
	|[] ->
	    (match !index with 
	    |Leaf(elem_ref) -> 
		(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> None
		)
	    |Node(_) -> raise VecIndex_findf_geq_keylist_too_short
	    |Empty -> None
	    )

exception VecIndex_findf_all_geq_keylist_too_long
exception VecIndex_findf_all_geq_keylist_too_short
	      
(* old work but no trace of followed keys which is needed for delition

    let rec findf_all_geq f keylist ref_index =
      match keylist with 
      | key::tl -> 
	  (match !ref_index with 
	  |Node(keydb) -> 
  	      (KeyDB.findf_all_geq (findf_all_geq f tl) key keydb)
	  |Leaf(_)-> raise VecIndex_findf_all_geq_keylist_too_long
	  |Empty -> []
	  )	    
      |[] ->
	  (match !ref_index with 
	    |Leaf(elem_ref) ->  f elem_ref
	       (*(match !elem_ref with 
		 |Elem(elem) -> f elem
		|Empty_Elem -> []
		) *)
	    |Node(_) -> raise VecIndex_findf_all_geq_keylist_too_short
	    |Empty -> []
	  )
	
*)
(* followed_key_list is reversed to as needed *)

   let rec findf_all_geq' index f followed_key_list keylist =
      match keylist with 
      | key::tl -> 
	  (match !index with 
	  |Node(keydb) -> 
	      let apply_key followed_key ref_index = 
		findf_all_geq' index f (followed_key::followed_key_list) tl in
  	      (KeyDB.findf_all_geq apply_key key keydb)
	  |Leaf(_)-> raise VecIndex_findf_all_geq_keylist_too_long
	  |Empty -> []
	  )	    
      |[] ->
	  (match !index with 
	    |Leaf(elem_ref) ->  f followed_key_list elem_ref
	       (*(match !elem_ref with 
		 |Elem(elem) -> f elem
		|Empty_Elem -> []
		) *)
	    |Node(_) -> raise VecIndex_findf_all_geq_keylist_too_short
	    |Empty -> []
	  )
    
    let findf_all_geq index f keylist =
      findf_all_geq' index f [] keylist

exception VecIndex_findf_all_leq_keylist_too_long
exception VecIndex_findf_all_leq_keylist_too_short
	      
(*
    let rec findf_all_leq f keylist ref_index =
      match keylist with 
      | key::tl -> 
	  (match !ref_index with 
	  |Node(keydb) -> 
  	      (KeyDB.findf_all_leq (findf_all_leq f tl) key keydb)
	  |Leaf(_)-> raise VecIndex_findf_all_leq_keylist_too_long
	    |Empty -> []
	  )	    
      |[] ->
	  (match !ref_index with 
	    |Leaf(elem_ref) -> f elem_ref
		(*(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> []
		)*)
	    |Node(_) -> raise VecIndex_findf_all_leq_keylist_too_short
	    |Empty -> []
	  )
	    
*)
  end

    

(*-----------------------------------------------------------------*)
(*                      Compressed Feature Vector Index            *)
(*-----------------------------------------------------------------*)
(* if we have a vector [0,0,0,1,0,0,2,0,0]                         *)
(* then the compresed vector is [(3,1),(6,2)]                       *)
(* where 0 is the minimal element,                                  *)
(* we compress only the least element  "0"                          *)
(* (a generalisation is possible to compress any repeating value)   *)
(* so the compressed keys are pairs (p,v) where p is  position,     *)
(* and v is a "non-zero" value                                         *)
(* the least position is 0, and vectors can have different length *)
(* the empty compressed list [] correspods to lists [0,..,0]*)
(* the positions, values and orders are abstracted                  *)
(* the vector is assumed to be well defined: *)
(* ordered w.r.t. positions: lower pos. come first, *)
(* there is  no two elem  with the same position *)

(* vectors are stored in trees of trees  *)
(* keys of a tree are (p,v)'s  ordered by the following lex combination: *)
(* (p,v) >= (p',v')  if 1. p<p' 2. p=p' and v>=v'*)
(* vlues in the nodes of the trees consit of: *)
(* 1. the  next tree 2. value of the vectors ending at this node*)


module type KeyCom =
  sig
    type t
(* compare position  *)
    val compare_p : t -> t -> int
(* compare the value *)
    val compare_v : t -> t -> int
  end

(* Generates the Key module used in the trees *)
module MakeKey(KeyCom:KeyCom) = 
  struct 
    type t = KeyCom.t
    let compare_p = KeyCom.compare_p
    let compare_v = KeyCom.compare_v	
    let compare x y = 
      let  c = compare_p x y in
      if not (c=0) then -c
      else compare_v x y 
  end

module type IndexCom = 
  sig
    type key
    type keylist = key list
    type 'a index
    val create : unit  -> 'a index
(* copied from trie_func *) 
    val mem    : 'a index -> keylist -> bool
    val add    : 'a index -> keylist ->  'a ref_elem
    val remove : 'a index -> keylist -> unit

(* return element corr. to the keylist and raises Not_found
  if the keylist is not in index *)
    val  find : 'a index -> keylist -> 'a ref_elem
(* new for feature indexes*)
    val findf_leq : 'a index -> ('a -> 'b option) -> keylist -> 'b option
(*    val findf_geq : ('a -> 'b option) -> keylist -> ('a index) ref -> 'b option*)

    val findf_all_geq :  
	'a index -> (keylist -> 'a ref_elem -> 'b list) -> keylist -> 'b list 
(*
    val findf_all_leq :  
	('a ref_elem -> 'b list) -> keylist -> ('a index) ref -> 'b list 
*)  
 end


module MakeCom(KeyCom:KeyCom)  =
  struct

    module Key = MakeKey (KeyCom) 
    module KeyDB = Tree.Make (Key)
    type key     = KeyCom.t
    type keylist = key list
    type 'a index_plain =
        Node of (('a index)  KeyDB.tree) * ('a ref_elem)
      | Empty
    and 
          'a index = ('a index_plain) ref  
           

    let create () = ref Empty


    let rec mem index keylist = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match !index with 
	    |Node(keydb,_) ->
        	( try mem (KeyDB.find key keydb)  tl with 
		  Not_found -> false
		 ) 
	    | Empty -> false 
	   )
      |[] -> true

 
(* return element corr. to the keylist and raises Not_found
  if the keylist is not in index *)

let rec find index keylist =
      match keylist with
      |key::tl ->
          (
            match !index with
            |Node(keydb,_) ->
                 find (KeyDB.find key keydb) tl
            | Empty -> raise Not_found
           )
      |[] ->
          (
            match !index with
            |Node(_,v) -> v
            |Empty  -> raise Not_found
          )
	    

   let rec create_from_keys keylist = 
      match keylist with 
      |key::tl  -> 	   
	  let (rest_index,ref_leaf) = create_from_keys tl in
          let new_kdb = KeyDB.add  key rest_index (KeyDB.create ()) in
	  (ref (Node(new_kdb, ref Empty_Elem)), ref_leaf)
      |[] ->
	  let new_tree = KeyDB.create () in 
	  let ref_leaf = ref Empty_Elem in
	  (ref (Node(new_tree,ref_leaf)),ref_leaf)
	  

    let rec add index keylist =
      match keylist with 
      |key::tl -> 
	  ( 
	    match !index with 
	    |Node(keydb,v) ->
		(try 
		  let n_index = (KeyDB.find key keydb) in  
		  add n_index tl 
		with 		  
		  Not_found -> 
		    let (new_index,ref_leaf) = create_from_keys tl in
		    index := 
		      Node((KeyDB.add key new_index keydb),v);
		    ref_leaf
		)
	    | Empty  -> 
		let (new_index,ref_leaf) = create_from_keys keylist in
                index := !new_index;
		ref_leaf
         )
      |[] ->
	  ( 
	    match !index with 
	    |Node(_,ref_leaf) -> ref_leaf
	    |Empty   -> 
		let ref_elem = ref Empty_Elem in
                index:= Node((KeyDB.create ()), ref_elem);
		ref_elem		       
	   ) 


   let rec remove index keylist = 
      match keylist with 
      |key::tl -> 
	  ( 
	    match !index with 
	    |Node(keydb, v) ->
		(
		 (try 
		  remove (KeyDB.find key keydb) tl
		with 
		  Not_found -> failwith "vectorIndex remove: path too long"
		);
                if !(KeyDB.find key keydb)= Empty 
                then 
		  (
		   let new_keydb = KeyDB.remove key keydb in
		   if (KeyDB.is_empty new_keydb) && (!v= Empty_Elem)
		   then (index := Empty)
		   else (index := Node(new_keydb,v))
		  )
		)
	    | Empty -> failwith "vectorIndex remove: path too long"
	   )
      |[] ->    
	  (
	   match !index with 
	   |Node(keydb, ref_leaf) -> 
	        (ref_leaf := Empty_Elem; 	       
		 if  (KeyDB.is_empty keydb) 
		 then (index:=Empty)
		 else ())
	   | Empty ->
	        failwith "vectorIndex remove: remove from empty index"
	  )


(*----------functions for subsumtion-----------------*)


(*
    let rec vec_skip_to_pos_geq key vec = 
      match vec with 
      | h::tl ->
	  if (Key.compare_p h key) >= 0 
	  then vec
	  else vec_skip_to_pos_geq key tl	      
      | [] -> []
*)


(*we assume that key <= than the head of the vec*)
(*therefore pos(key) >= pos(h)  *)
  let rec vec_skip_to_pos_eq key vec = 
      match vec with 
      | h::tl ->
	  let c = (Key.compare_p h key) in
	  if c = 0 
	  then (h,tl)
	  else
	    if c > 0 
	    then raise Not_found  
	    else vec_skip_to_pos_eq key tl	      
      | [] -> raise Not_found

    let rec findf_leq index f keylist =
	match keylist with 
	| key::tl -> 
	    (match !index with 
	    |Node(keydb,elem_ref) -> 
(* all which are ended before the keylist are smaller*)
		(match 
		  (match !elem_ref with 
		  |Elem(elem) -> f elem
		  |Empty_Elem -> None
		  )
		with 
		|Some(x) -> Some(x)
		|None -> 
(*  		(KeyDB.findf_leq (findf_leq f tl) key keydb)*)
 (*	(KeyDB.findf_leq (fun _ x -> findf_leq f tl x) key keydb)*)
		    KeyDB.findf_leq (prog_fun_findf_leq f keylist) key keydb 
		)	    
	    |Empty -> None
	    )	    
	|[] ->
	    (match !index with 
	    |Node(_,elem_ref) -> 
		(match !elem_ref with 
		|Elem(elem) -> f elem
		|Empty_Elem -> None
		)	  
	    |Empty -> None
	    )
    and
	prog_fun_findf_leq f keylist dbkey dbval = 
      (*inv: dbkey =< key*)
      try 
	let (h_new_vec,tl_new_vec) = vec_skip_to_pos_eq dbkey keylist in
  	if (Key.compare_v h_new_vec dbkey) >= 0 then
          findf_leq dbval f tl_new_vec
	else None 
      with 
   (* Not_found is the case when 0 is in *)
   (*the (uncompressed) position = pos(dbkey) in keylist *)	   
    	Not_found -> None 


(*--------------*)
   let rec findf_all index f followed_key_list =
     (match !index with 
     |Node(keydb,elem_ref) -> 
	 (
	  (f followed_key_list elem_ref)@(KeyDB.findf_all (prog_fun_findf_all f followed_key_list) keydb)
	 )
     |Empty -> []
     )	    
   and
       prog_fun_findf_all f followed_key_list dbkey dbval = 
     findf_all dbval f (dbkey::followed_key_list)


(*--------------*)
(* followed_key_list is reversed to as needed *)
(* followed_key_list is needed for removals   *)
    let rec findf_all_geq' index f followed_key_list keylist =
  (*    findf_all f followed_key_list ref_index *)
      match keylist with 
      | key::tl -> 
	  (match !index with 
	  |Node(keydb,_) -> 
	      KeyDB.findf_all_geq 
		(prog_fun_findf_all_geq f followed_key_list key tl) key keydb 
	  |Empty -> []
	  )	    
      |[] -> 
	  findf_all index f followed_key_list
    and
	prog_fun_findf_all_geq f followed_key_list key tl dbkey dbval = 
      (*inv: dbkey >= key, therfore  pos(key) >= pos(dbkey)*)
      let c = Key.compare_p key dbkey in
      if c > 0 
      then
	findf_all_geq' dbval f (dbkey::followed_key_list) (key::tl)
      else
	if c=0 
	then 
	  findf_all_geq' dbval f (dbkey::followed_key_list) tl
	else failwith "vectorIndex: findf_all_geq'"

    let findf_all_geq index f keylist =
      findf_all_geq' index f [] keylist
	


  end
