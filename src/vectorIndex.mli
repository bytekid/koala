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
    val mem    : 'a index -> keylist ->  bool
    val add    : 'a index -> keylist -> 'a ref_elem
    val remove : 'a index -> keylist -> unit
(* return element corr. to the keylist and raises Not_found
   if the keylist is not in index *)
    val  find : 'a index -> keylist -> 'a ref_elem
(* new for feature indexes*)

(* findf_leq applies f to leaf elements with key list less or equal to key
   (coordinatewise)
   and stops if f returns Some(v) and returns Some(v) otherwise
   reterns None; used in subsumtion index for subsumption *)

    val findf_leq : 'a index ->  ('a -> 'b option) -> keylist -> 'b option
    val findf_geq : 'a index ->  ('a -> 'b option) -> keylist ->  'b option
	
(* findf_all_leq returns list of all elements with key less or eqaul to key
   and [] if all f return []; f can also change the elements of the index 
   (used to remove subsumed clauses) *)

    val findf_all_geq :  
	'a index -> (keylist -> 'a ref_elem -> 'b list) -> keylist -> 'b list 
	
(*
    val findf_all_leq :  
	('a ref_elem -> 'b list) -> keylist -> ('a index) ref -> 'b list 
*)
  end

module Make(Key:Key): (Index with type key=Key.t) 



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

module type IndexCom = 
  sig
    type key
    type keylist = key list
    type 'a index
    val create : unit  -> 'a index
(* copied from trie_func *) 
    val mem    : 'a index ->  keylist -> bool
    val add    : 'a index -> keylist -> 'a ref_elem
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


module MakeCom(KeyCom:KeyCom)  : (IndexCom with type key=KeyCom.t) 
