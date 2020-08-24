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







(***********************************************************************)
(*                                                                     *)
(*                           Objective Caml                            *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 1996 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file ../LICENSE.     *)
(*                                                                     *)
(***********************************************************************)

(* $Id: map.ml,v 1.17 2005/08/13 20:59:37 doligez Exp $ *)



(* Modified: K. Korovin, Apr 2008 *)
(* Summary: I use balanced trees from the implementation of maps in ocaml stdlib *)
(* balanced trees then extended with functionallity needed for the vector index*)



module type Key =
  sig
    type t
    val compare: t -> t -> int
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
	(*  val findf_all_leq :  ('a -> 'b list) -> key -> 'a tree -> 'b list *)

(*
  val empty: 'a t
  val is_empty: 'a t -> bool
  val add: key -> 'a -> 'a t -> 'a t
  val find: key -> 'a t -> 'a
  val remove: key -> 'a t -> 'a t
  val mem:  key -> 'a t -> bool
  val iter: (key -> 'a -> unit) -> 'a t -> unit
  val map: ('a -> 'b) -> 'a t -> 'b t
  val mapi: (key -> 'a -> 'b) -> 'a t -> 'b t
  val fold: (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  val compare: ('a -> 'a -> int) -> 'a t -> 'a t -> int
  val equal: ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
 *)
  end

module Make(Key: Key) = struct

  type key = Key.t

  type 'a tree =
      Empty
    | Node of 'a tree * key * 'a * 'a tree * int

  let create () = Empty
  let is_empty tree = (tree = Empty)
      
  let height = function
      Empty -> 0
    | Node(_,_,_,_,h) -> h

  let create_node l x d r =
    let hl = height l and hr = height r in
    Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))

  let bal l x d r =
    let hl = match l with Empty -> 0 | Node(_,_,_,_,h) -> h in
    let hr = match r with Empty -> 0 | Node(_,_,_,_,h) -> h in
    if hl > hr + 2 then begin
      match l with
        Empty -> invalid_arg "Tree.bal"
      | Node(ll, lv, ld, lr, _) ->
          if height ll >= height lr then
            create_node ll lv ld (create_node lr x d r)
          else begin
            match lr with
              Empty -> invalid_arg "Tree.bal"
            | Node(lrl, lrv, lrd, lrr, _)->
                create_node (create_node ll lv ld lrl) lrv lrd (create_node lrr x d r)
          end
    end else if hr > hl + 2 then begin
      match r with
        Empty -> invalid_arg "Tree.bal"
      | Node(rl, rv, rd, rr, _) ->
          if height rr >= height rl then
            create_node (create_node l x d rl) rv rd rr
          else begin
            match rl with
              Empty -> invalid_arg "Tree.bal"
            | Node(rll, rlv, rld, rlr, _) ->
                create_node (create_node l x d rll) rlv rld (create_node rlr rv rd rr)
          end
    end else
      Node(l, x, d, r, (if hl >= hr then hl + 1 else hr + 1))
(*
  let empty = Empty

  let is_empty = function Empty -> true | _ -> false
 *)

  let rec add x data = function
      Empty ->
        Node(Empty, x, data, Empty, 1)
    | Node(l, v, d, r, h) ->
        let c = Key.compare x v in
        if c = 0 then
          Node(l, x, data, r, h)
        else if c < 0 then
          bal (add x data l) v d r
        else
          bal l v d (add x data r)

  let rec find x = function
      Empty ->
        raise Not_found
    | Node(l, v, d, r, _) ->
        let c = Key.compare x v in
        if c = 0 then d
        else find x (if c < 0 then l else r)

  let rec mem x = function
      Empty ->
        false
    | Node(l, v, d, r, _) ->
        let c = Key.compare x v in
        c = 0 || mem x (if c < 0 then l else r)

  let rec min_binding = function
      Empty -> raise Not_found
    | Node(Empty, x, d, r, _) -> (x, d)
    | Node(l, x, d, r, _) -> min_binding l

  let rec remove_min_binding = function
      Empty -> invalid_arg "Tree.remove_min_elt"
    | Node(Empty, x, d, r, _) -> r
    | Node(l, x, d, r, _) -> bal (remove_min_binding l) x d r

  let merge t1 t2 =
    match (t1, t2) with
      (Empty, t) -> t
    | (t, Empty) -> t
    | (_, _) ->
        let (x, d) = min_binding t2 in
        bal t1 x d (remove_min_binding t2)

  let rec remove x = function
      Empty ->
        Empty
    | Node(l, v, d, r, h) ->
        let c = Key.compare x v in
        if c = 0 then
          merge l r
        else if c < 0 then
          bal (remove x l) v d r
        else
          bal l v d (remove x r)

  let rec iter f = function
      Empty -> ()
    | Node(l, v, d, r, _) ->
        iter f l; f v d; iter f r

  let rec map f = function
      Empty               -> Empty
    | Node(l, v, d, r, h) -> Node(map f l, v, f d, map f r, h)

  let rec mapi f = function
      Empty               -> Empty
    | Node(l, v, d, r, h) -> Node(mapi f l, v, f v d, mapi f r, h)

  let rec fold f m accu =
    match m with
      Empty -> accu
    | Node(l, v, d, r, _) ->
        fold f r (f v d (fold f l accu))

  type 'a enumeration = End | More of key * 'a * 'a tree * 'a enumeration

  let rec cons_enum m e =
    match m with
      Empty -> e
    | Node(l, v, d, r, _) -> cons_enum l (More(v, d, r, e))

  let compare cmp m1 m2 =
    let rec compare_aux e1 e2 =
      match (e1, e2) with
        (End, End) -> 0
      | (End, _)  -> -1
      | (_, End) -> 1
      | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
          let c = Key.compare v1 v2 in
          if c <> 0 then c else
          let c = cmp d1 d2 in
          if c <> 0 then c else
          compare_aux (cons_enum r1 e1) (cons_enum r2 e2)
    in compare_aux (cons_enum m1 End) (cons_enum m2 End)

  let equal cmp m1 m2 =
    let rec equal_aux e1 e2 =
      match (e1, e2) with
        (End, End) -> true
      | (End, _)  -> false
      | (_, End) -> false
      | (More(v1, d1, r1, e1), More(v2, d2, r2, e2)) ->
          Key.compare v1 v2 = 0 && cmp d1 d2 &&
          equal_aux (cons_enum r1 e1) (cons_enum r2 e2)
    in equal_aux (cons_enum m1 End) (cons_enum m2 End)


(*----------KK additional functions:-------------------------*)

(* traverses tree until f returns Some(v) and returns Some(v) else return None*)
  let rec findf f = function 
    |Node (l, v, d, r, _) -> 	
        (match (f v d) with 
	|Some(d) -> Some(d)
	|None -> 
	    ( match (findf f l) with 
	    |Some(d) -> Some(d)
	    |None ->
		(match (findf f r) with 
		|Some(d) -> Some(d)
		|None -> None
		)
	     )
	)
    |Empty -> None


(* findf_leq applies f to elements with key less or equal to key 
   and stops if f returns Some(v) and returns Some(v) otherwise
   reterns None; used in vector index for subsumption *)

  let rec findf_leq f key = function
    |Node (l, v, d, r, _) ->
	let cmp = Key.compare key v in
	if cmp >= 0
	then 
	  match (findf f l) with 
	  |Some(d) -> Some(d)
	  |None -> 
	      (match (f v d) with
	      |Some(d) -> Some(d)
	      |None -> findf_leq f key r
	      )
	else (*cmp < 0*)
          (findf_leq f key l)
    |Empty -> None

(* as above but for greater or equal *)

  let rec findf_geq f key = function
    |Node(l, v, d, r, _)->
	let cmp = Key.compare key v in
	if cmp <= 0
	then 
	  match (findf f r) with 
	  |Some(d) -> Some(d)
	  |None -> 
	      (match (f v d) with
	      |Some(d) -> Some(d)
	      |None -> findf_geq f key l
	      )
	else (*cmp > 0*)
          (findf_geq f key r)
    |Empty -> None


  let rec findf_all f = function 
    |Node(l, v, d, r, _) -> 	
	(f v d)@(findf_all f l)@(findf_all f r)
    |Empty -> []


  let rec findf_all_geq f key = function
    |Node(l, v, d, r, _) ->
	let cmp = Key.compare key v in
	if cmp <= 0
	then 
	  (f v d)@(findf_all f r)@(findf_all_geq f key l)
	else 
	  findf_all_geq f key r
    |Empty -> []

end





(*---KK my Simple Search Trees with functionality needed for the vector index----*)

exception Tree_add_already_in

(*
  module type Key =
  sig
  type t
  val compare : t -> t -> int
  end
 *)

    
module type TreeNonBl =
  sig
    type key
    type 'a tree  
    val create : unit  -> 'a tree
    val is_empty : 'a tree -> bool
    val find : key -> 'a tree -> 'a
    val mem  : key -> 'a tree -> bool
    val add  : key -> 'a -> 'a tree -> 'a tree
    val remove :  key -> 'a tree -> 'a tree
    val findf_leq : (key -> 'a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_geq : (key -> 'a -> 'b option) -> key -> 'a tree -> 'b option
    val findf_all_geq :  (key -> 'a -> 'b list) -> key -> 'a tree -> 'b list 
	(*  val findf_all_leq :  ('a -> 'b list) -> key -> 'a tree -> 'b list *)
  end

module MakeNonBl(Key:Key)  =
  struct
    type key = Key.t

	  (*inv: keys of right (left) subtree 
	    are greater (smaller) than node key *)

    type 'a tree = 
      |Node of key * 'a * 'a tree * 'a tree   
      |Empty
	  
    let create () = Empty
    let is_empty tree = (tree = Empty)

    let rec mem key = function
      |Node(ck, elem, lt, rt) -> 
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then  mem key rt 
	  else	 
	    if cmp < 0
	    then  mem key lt
	    else
	      true
      |Empty -> false 
	    
    let	rec find key = function
      |Node(ck, elem, lt, rt) -> 
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then find key rt 
	  else	 
	    if cmp < 0
	    then find key lt
	    else
	      elem
		
      |Empty -> raise Not_found

	    
    let rec add key elem = function
      |Node(ck,celem, lt, rt) -> 	
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then Node(ck,celem,lt,(add key elem rt)) 
	  else	 
	    if cmp < 0
	    then Node(ck,celem,(add key elem lt),rt)
	    else
	      raise Tree_add_already_in
		
      |Empty -> Node(key,elem,Empty,Empty)

(*  transforms tree such that the maximal key is at the top
    inv: right subtree of the result is always Empty 
    (used for removal) *)
	    
    let rec pop_max_top = function
      |Node(ck, celem, clt, crt) as tree -> 
	  if crt = Empty then 
	    tree 
	  else
	    let poped = pop_max_top crt in
	    (match poped with
	    |Node(pck, pelem, plt, _) ->
		Node(pck,pelem,Node(ck,celem,clt,plt),Empty)
	    |_->failwith "tree pop_max_top: should happen"	     
	    )
      |Empty -> Empty
	    

    let rec remove key = function
      |Node(ck,celem, clt, crt) -> 	
	  let cmp = Key.compare key ck in
	  if cmp > 0
	  then Node(ck,celem, clt,(remove key crt)) 
	  else	 
	    if cmp < 0
	    then Node(ck,celem,(remove key clt),crt)
	    else (*cmp = 0 *)
              if clt = Empty 
	      then crt
	      else
		(match (pop_max_top clt) with
		|Node(pck, pelem,plt,_) ->
                    Node(pck,pelem,plt,crt)
		|_-> failwith "tree remove: should not happen"  
		)
      |Empty -> Empty


(* traverses tree until f returns Some(v) and returne Some(v) else return None*)

    let rec findf f = function 
      |Node(ck,celem, clt, crt) -> 	
          (match (f ck celem) with 
	  |Some(v) -> Some(v)
	  |None -> 
	      ( match (findf f clt) with 
	      |Some(v) -> Some(v)
	      |None ->
		  (match (findf f crt) with 
		  |Some(v) -> Some(v)
		  |None -> None
		  )
	       )
	  )
      |Empty -> None


(* findf_leq applies f to elements with key less or equal to key 
   and stops if f returns Some(v) and returns Some(v) otherwise
   reterns None; used in vector index for subsumption *)

    let rec findf_leq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp >= 0
	  then 
	    match (findf f clt) with 
	    |Some(v) -> Some(v)
	    |None -> 
		(match (f ck celem) with
		|Some(v) -> Some(v)
		|None -> findf_leq f key crt
		)
	  else (*cmp < 0*)
            (findf_leq f key clt)
      |Empty -> None

(* as above but for greater or equal *)

    let rec findf_geq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp <= 0
	  then 
	    match (findf f crt) with 
	    |Some(v) -> Some(v)
	    |None -> 
		(match (f ck celem) with
		|Some(v) -> Some(v)
		|None -> findf_geq f key clt
		)
	  else (*cmp > 0*)
            (findf_geq f key crt)
      |Empty -> None

(* returns list of all elem's v obtained by applyng f to all elements *)	    
(* old works ok but no trace of passed keys, cannot be used for delition

   let rec findf_all f = function 
   |Node(ck, celem, clt, crt) -> 	
   (f celem)@(findf_all f clt)@(findf_all f crt)
   |Empty -> []
 *)

    let rec findf_all f = function 
      |Node(ck, celem, clt, crt) -> 	
	  (f ck celem)@(findf_all f clt)@(findf_all f crt)
      |Empty -> []
	    
(* findf_all_leq returns list of all elements with key less or eqaul to key
   and [] if all f return None
 *)
(*
  let rec findf_all_leq f key = function
  |Node(ck, celem, clt, crt) ->
  let cmp = Key.compare key ck in
  if cmp >= 0
  then 
  (f ck celem)@(findf_all f clt)@(findf_all_leq f key crt)
  else 
  findf_all_leq f key clt
  |Empty -> []
 *)	    
(* as above but for greater or equal *)

(* old works ok but no trace of passed keys, cannot be used for delition
   
   let rec findf_all_geq f key = function
   |Node(ck, celem, clt, crt) ->
   let cmp = Key.compare key ck in
   if cmp <= 0
   then 
   (f celem)@(findf_all f crt)@(findf_all_geq f key clt)
   else 
   findf_all_geq f key crt
   |Empty -> []
   
 *)

    let rec findf_all_geq f key = function
      |Node(ck, celem, clt, crt) ->
	  let cmp = Key.compare key ck in
	  if cmp <= 0
	  then 
	    (f ck celem)@(findf_all f crt)@(findf_all_geq f key clt)
	  else 
	    findf_all_geq f key crt
      |Empty -> []

  end


    
(* debug 

   module IKey =
   struct
   type t = int
   let compare = compare
   end

   module ITree = Make (IKey)

   let tree1 = ITree.create ()
   let tree2 = ITree.add 5 5 tree1
   let tree3 = ITree.add 4 4 tree2
   let tree4 = ITree.add 7 7 tree3
   let tree5 = ITree.add 20 20 tree4
   let tree6 = ITree.add 10 10 tree5
   let tree7 =  ITree.add 15 15 tree6

   let tree8 =  ITree.add 22 22 tree7

   let f x = 
   if x >= 7 
   then Some(x) else None
 *)
