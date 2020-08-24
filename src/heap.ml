(*
 * Heap: heaps implemented both functionally and imperatively
 * Copyright (C) 2003 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Library General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU Library General Public License version 2 for more details
 * (enclosed in the file LGPL).
 *)

(* KK added heap_equal *)
(* store equal elements as a least rather than a tree *)

(*s Heaps *)

open Lib

module type Ordered = sig
  type t
  val compare : t -> t -> int
end


(* A bare element module with only the type and no operations, those
   are given in a separate module at runtime *)
module type Elem0 =
  sig 
    type t 
  end

exception EmptyHeap


(* This is a partially generic imperative heap, slightly modified from
   the module {Imperative} below.

   The module is a functor paramterised with a module that only
   contains the type of the elements. The comparison function is given
   as a module parameter at runtime. This uses the first-class module
   feature introduced in OCaml 3.12.

   The type of this heap is only dependent on the type of the
   elements, since the ordering of the elements is a runtime
   parameter, heaps with the same element types but different
   orderings are of the same type and can be mixed in a list, see
   n-ary priority queues.
 *)
module ImperativeGen(E : Elem0) = struct

  (* The type of an element in the heap *)
  type elt = E.t

	(* The heap is encoded in the array [data], where elements are stored
	   from [0] to [size - 1]. From an element stored at [i], the left 
	   (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  type t = 
      { 

	(* The module containing the [compare] function for the
	   elements of the heap, passed at runtime. *)
	ordered_m : (module Ordered with type t = elt);
	
	(* The size of the heap *)
	mutable size : int; 
	
	(* The arry containing the data *)
	mutable data : elt array 

      }

	(* When [create n] is called, we cannot allocate the array, since there is
	   no known value of type [X.t]; we'll wait for the first addition to 
	   do it, and we remember this situation with a negative size. *)

	(* [create] has an addtional parameter [o]: a module of type Ordered
	   that gives the ordering of the elements. *)

  let create o n = 
    if n <= 0 then invalid_arg "create";
    { ordered_m = o;
      size = -n; 
      data = [||] }

  let is_empty h = h.size <= 0

      (* [resize] doubles the size of [data] *)

  let resize h =
    let n = h.size in
    assert (n > 0);
    let n' = 2 * n in
    let d = h.data in
    let d' = Array.make n' d.(0) in
    Array.blit d 0 d' 0 n;
    h.data <- d'

  let add h x =
    
    (* Locally bind the module [X] the the module extracted from the
       value [h.ordered_m] *)
    let module X = (val h.ordered_m : Ordered with type t = elt) in 

    (* first addition: we allocate the array *)
    if h.size < 0 then begin
      h.data <- Array.make (- h.size) x; h.size <- 0
    end;
    let n = h.size in
    (* resizing if needed *)
    if n == Array.length h.data then resize h;
    let d = h.data in
    (* moving [x] up in the heap *)
    let rec moveup i =
      let fi = (i - 1) / 2 in
      if i > 0 && X.compare d.(fi) x < 0 then begin
	d.(i) <- d.(fi);
	moveup fi
      end else
	d.(i) <- x
    in
    moveup n;
    h.size <- n + 1

  let maximum h =
    if h.size <= 0 then raise EmptyHeap;
    h.data.(0)

  let remove h =

    (* Locally bind the module [X] the the module extracted from the
       value [h.ordered_m] *)
    let module X = (val h.ordered_m : Ordered with type t = elt) in 

    if h.size <= 0 then raise EmptyHeap;
    let n = h.size - 1 in
    h.size <- n;
    let d = h.data in
    let x = d.(n) in
    (* moving [x] down in the heap *)
    let rec movedown i =
      let j = 2 * i + 1 in
      if j < n then
	let j = 
	  let j' = j + 1 in 
	  if j' < n && X.compare d.(j') d.(j) > 0 then j' else j 
	in
	if X.compare d.(j) x > 0 then begin 
	  d.(i) <- d.(j); 
	  movedown j 
	end else
	  d.(i) <- x
      else
	d.(i) <- x
    in
    movedown 0

  let pop_maximum h = let m = maximum h in remove h; m

  let iter f h = 
    let d = h.data in
    for i = 0 to h.size - 1 do f d.(i) done

  let fold f h x0 =
    let n = h.size in
    let d = h.data in
    let rec foldrec x i =
      if i >= n then x else foldrec (f x d.(i)) (succ i)
    in
    foldrec x0 0

end



(*s Imperative implementation *)

module Imperative(X : Ordered) = struct

  (* The heap is encoded in the array [data], where elements are stored
     from [0] to [size - 1]. From an element stored at [i], the left 
     (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  type t = { mutable size : int; mutable data : X.t array }

	(* When [create n] is called, we cannot allocate the array, since there is
	   no known value of type [X.t]; we'll wait for the first addition to 
	   do it, and we remember this situation with a negative size. *)

  let create n = 
    if n <= 0 then invalid_arg "create";
    { size = -n; data = [||] }

  let is_empty h = h.size <= 0

      (* [resize] doubles the size of [data] *)

  let resize h =
    let n = h.size in
    assert (n > 0);
    let n' = 2 * n in
    let d = h.data in
    let d' = Array.make n' d.(0) in
    Array.blit d 0 d' 0 n;
    h.data <- d'

  let add h x =
    (* first addition: we allocate the array *)
    if h.size < 0 then begin
      h.data <- Array.make (- h.size) x; h.size <- 0
    end;
    let n = h.size in
    (* resizing if needed *)
    if n == Array.length h.data then resize h;
    let d = h.data in
    (* moving [x] up in the heap *)
    let rec moveup i =
      let fi = (i - 1) / 2 in
      if i > 0 && X.compare d.(fi) x < 0 then begin
	d.(i) <- d.(fi);
	moveup fi
      end else
	d.(i) <- x
    in
    moveup n;
    h.size <- n + 1

  let maximum h =
    if h.size <= 0 then raise EmptyHeap;
    h.data.(0)

  let remove h =
    if h.size <= 0 then raise EmptyHeap;
    let n = h.size - 1 in
    h.size <- n;
    let d = h.data in
    let x = d.(n) in
    (* moving [x] down in the heap *)
    let rec movedown i =
      let j = 2 * i + 1 in
      if j < n then
	let j = 
	  let j' = j + 1 in 
	  if j' < n && X.compare d.(j') d.(j) > 0 then j' else j 
	in
	if X.compare d.(j) x > 0 then begin 
	  d.(i) <- d.(j); 
	  movedown j 
	end else
	  d.(i) <- x
      else
	d.(i) <- x
    in
    movedown 0

  let pop_maximum h = let m = maximum h in remove h; m

  let iter f h = 
    let d = h.data in
    for i = 0 to h.size - 1 do f d.(i) done

  let fold f h x0 =
    let n = h.size in
    let d = h.data in
    let rec foldrec x i =
      if i >= n then x else foldrec (f x d.(i)) (succ i)
    in
    foldrec x0 0

end


(*-----------------------------------------------------*)
(*KK Heap equal  Imperative  implementation *)

(* Not yet checked!!!! use FunctionalEq !!!*)

module ImperativeEq(X : Ordered) = struct

  (* The heap is encoded in the array [data], where elements are stored
     from [0] to [size - 1]. From an element stored at [i], the left 
     (resp. right) subtree, if any, is rooted at [2*i+1] (resp. [2*i+2]). *)

  type elt = X.t
  type elt_list = elt list
	
  let compare_elt_list el l  = 
    try 
      X.compare el (List.hd l)
    with 
      _-> failwith "heap compare_elt_list: list should be non-empty"
	  
  let compare_list_list l1 l2 =
    try 
      X.compare (List.hd l1) (List.hd l2)
    with 
      _-> failwith "heap compare_list_list: list should be non-empty"


  type t = { mutable size : int; mutable num_nonequal : int; 
	     mutable data : elt_list array }

	(* When [create n] is called, we cannot allocate the array, since there is
	   no known value of type [X.t]; we'll wait for the first addition to 
	   do it, and we remember this situation with a negative size. *)

  let create n = 
    if n <= 0 then invalid_arg "create";
    { size = -n; num_nonequal = 0; data = [||] }

  let is_empty h = h.size <= 0

      (* [resize] doubles the size of [data] *)

  let resize h =
    let n = h.num_nonequal in
    assert (n > 0);
    let n' = 2 * n in
    let d = h.data in
    let d' = Array.make n' d.(0) in
    Array.blit d 0 d' 0 n;
    h.data <- d'

  let add h x =
    (* first addition: we allocate the array *)
    if h.size < 0 then begin
      h.data <- Array.make (- h.size) [x]; h.size <- 0;
    end;
    let n = h.num_nonequal in
    (* resizing if needed *)
    if n == Array.length h.data then resize h;
    let d = h.data in
    (* moving [x] up in the heap *)
    let rec moveup i =
      let fi = (i - 1) / 2 in
      let cmp = compare_elt_list x d.(fi) in
      if i > 0 && cmp > 0 
      then begin
	d.(i) <- d.(fi);
	moveup fi
      end else
	if cmp = 0 
	then 
	  d.(fi) <- x::(d.(fi))
	else
	  (h.num_nonequal <- h.num_nonequal +1;
	   d.(i) <- [x])
    in
    moveup n;
    h.size <- n + 1

  let maximum_list h =
    if h.size <= 0 then raise EmptyHeap;
    h.data.(0)

  let maximum h =
    if h.size <= 0 then raise EmptyHeap;
    try  
      List.hd h.data.(0)
    with _-> failwith "heap list should not be empty"

  exception Last_Elem
  let rec remove_from_list l = 
    match l with 
    | h::tl -> 
	if tl=[] then
	  raise Last_Elem
	else tl
    |[] -> failwith "heap remove: should not be empty"    

	  
  let remove h =
    if h.size <= 0 then raise EmptyHeap;
    let n = h.size - 1 in
    h.size <- n;
    let d = h.data in
    let x = d.(n) in
    try 
      d.(n) <- (remove_from_list d.(n))
    with 
      Last_Elem ->
	(* moving [x] down in the heap *)
	h.num_nonequal <- h.num_nonequal -1;
	let rec movedown i =
	  let j = 2 * i + 1 in
	  if j < n then
	    let j = 
	      let j' = j + 1 in 
	      if j' < n && compare_list_list d.(j') d.(j) > 0 then j' else j 
	    in
	    let cmp = compare_list_list x d.(j) in
	    if cmp < 0 then begin 
	      d.(i) <- d.(j); 
	      movedown j 
	    end else
	      d.(i) <- x
	  else
	    d.(i) <- x
	in
	movedown 0

  let pop_maximum h = let m = maximum h in remove h; m

  let iter f h = 
    let d = h.data in
    for i = 0 to h.size - 1 do 
      List.iter f d.(i) 
    done

  let fold f h x0 =
    let n = h.size in
    let d = h.data in
    let rec foldrec x i =
      if i >= n then x else 
      foldrec (List.fold_left f x d.(i)) (succ i)
    in
    foldrec x0 0
end


(*s Functional implementation *)

module type FunctionalSig = sig
  type elt
  type t
  val empty : t
  val add : elt -> t -> t
  val maximum : t -> elt
  val remove : t -> t
  val iter : (elt -> unit) -> t -> unit
(*
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
 *)
  val fold : ('a -> elt -> 'a) -> t -> 'a -> 'a
end

module Functional(X : Ordered) = struct

  (* Heaps are encoded as complete binary trees, i.e., binary trees
     which are full expect, may be, on the bottom level where it is filled 
     from the left. 
     These trees also enjoy the heap property, namely the value of any node 
     is greater or equal than those of its left and right subtrees.

     There are 4 kinds of complete binary trees, denoted by 4 constructors:
     [FFF] for a full binary tree (and thus 2 full subtrees);
     [PPF] for a partial tree with a partial left subtree and a full
     right subtree;
     [PFF] for a partial tree with a full left subtree and a full right subtree
     (but of different heights);
     and [PFP] for a partial tree with a full left subtree and a partial
     right subtree. *)

  type elt = X.t

  type t = 
    | Empty
    | FFF of t * X.t * t (* full    (full,    full) *)
    | PPF of t * X.t * t (* partial (partial, full) *)
    | PFF of t * X.t * t (* partial (full,    full) *)
    | PFP of t * X.t * t (* partial (full,    partial) *)

  let empty = Empty
      
      (* smart constructors for insertion *)
  let p_f l x r = match l with
  | Empty | FFF _ -> PFF (l, x, r)
  | _ -> PPF (l, x, r)

  let pf_ l x = function
    | Empty | FFF _ as r -> FFF (l, x, r)
    | r -> PFP (l, x, r)

  let rec add x = function
    | Empty -> 
	FFF (Empty, x, Empty)
	  (* insertion to the left *)
    | FFF (l, y, r) | PPF (l, y, r) ->
	if X.compare x y > 0 then p_f (add y l) x r else p_f (add x l) y r
	  (* insertion to the right *)
    | PFF (l, y, r) | PFP (l, y, r) ->
	if X.compare x y > 0 then pf_ l x (add y r) else pf_ l y (add x r)

  let maximum = function
    | Empty -> raise EmptyHeap
    | FFF (_, x, _) | PPF (_, x, _) | PFF (_, x, _) | PFP (_, x, _) -> x

	  (* smart constructors for removal; note that they are different
	     from the ones for insertion! *)
  let p_f l x r = match l with
  | Empty | FFF _ -> FFF (l, x, r)
  | _ -> PPF (l, x, r)

  let pf_ l x = function
    | Empty | FFF _ as r -> PFF (l, x, r)
    | r -> PFP (l, x, r)

  let rec remove = function
    | Empty -> 
	raise EmptyHeap
    | FFF (Empty, _, Empty) -> 
	Empty
    | PFF (l, _, Empty) ->
	l
	  (* remove on the left *)
    | PPF (l, x, r) | PFF (l, x, r) ->
        let xl = maximum l in
	let xr = maximum r in
	let l' = remove l in
	if X.compare xl xr >= 0 then 
	  p_f l' xl r 
	else 
	  p_f l' xr (add xl (remove r))
	    (* remove on the right *)
    | FFF (l, x, r) | PFP (l, x, r) ->
        let xl = maximum l in
	let xr = maximum r in
	let r' = remove r in
	if X.compare xl xr > 0 then 
	  pf_ (add xr (remove l)) xl r'
	else 
	  pf_ l xr r'

  let rec iter f = function
    | Empty -> 
	()
    | FFF (l, x, r) | PPF (l, x, r) | PFF (l, x, r) | PFP (l, x, r) -> 
	iter f l; f x; iter f r

(* old fold
   let rec fold f h x0 = match h with
   | Empty -> 
   x0
   | FFF (l, x, r) | PPF (l, x, r) | PFF (l, x, r) | PFP (l, x, r) -> 
   fold f l (fold f r (f x x0))
 *)

  let rec fold f h x0 = match h with
  | Empty -> 
      x0
  | FFF (l, x, r) | PPF (l, x, r) | PFF (l, x, r) | PFP (l, x, r) -> 
      fold f l (fold f r (f x0 x))

end



(*KK Heap equal Functional implementation *)



module FunctionalEq(X : Ordered) = struct

  (* Heaps are encoded as complete binary trees, i.e., binary trees
     which are full expect, may be, on the bottom level where it is filled 
     from the left. 
     These trees also enjoy the heap property, namely the value of any node 
     is greater or equal than those of its left and right subtrees.

     There are 4 kinds of complete binary trees, denoted by 4 constructors:
     [FFF] for a full binary tree (and thus 2 full subtrees);
     [PPF] for a partial tree with a partial left subtree and a full
     right subtree;
     [PFF] for a partial tree with a full left subtree and a full right subtree
     (but of different heights);
     and [PFP] for a partial tree with a full left subtree and a partial
     right subtree.
     KK added lists to store elements whish are equal according to compare
   *)

  type elt = X.t
  type elt_list = elt list
  type elt_list_ref = elt_list ref

(* we need to preserve the FFF,.., relations after adding and removing ....*)

  type t = 
    | Empty
    | FFF of t * elt_list_ref * t (* full    (full,    full) *)
    | PPF of t * elt_list_ref * t (* partial (partial, full) *)
    | PFF of t * elt_list_ref * t (* partial (full,    full) *)
    | PFP of t * elt_list_ref * t (* partial (full,    partial) *)
	  
  let empty = Empty  
      

  let compare_elt_list el l  = 
    try 
      X.compare el (List.hd !l)
    with 
      _-> failwith "heap compare_elt_list: list should be non-empty"
	  
  let compare_list_list l1 l2 =
    try 
      X.compare (List.hd !l1) (List.hd !l2)
    with 
      _-> failwith "heap compare_list_list: list should be non-empty"
(*
  let apply_f_to_elem f = function
  |FFF(l,y,r) -> FFF(l,(f y),r) 
  |PPF(l,y,r) -> PPF(l,(f y),r)  
  |PFF(l,y,r) -> PFF(l,(f y),r)  
  |PFP(l,y,r) -> PFP(l,(f y),r)
  |Empty -> Empty
 *)

  let apply_f_to_elem f = function
    |FFF(_,y,_) |PPF(_,y,_) |PFF(_,y,_) |PFP(_,y,_) -> (f y)
    |Empty -> ()

  exception Add_if_equal
  let add_if_equal x h =
    apply_f_to_elem (function y -> y := x::(!y)) h    
      
      (* smart constructors for insertion *)
  let p_f l x r = match l with
  | Empty | FFF _ -> PFF (l, x, r)
  | _ -> PPF (l, x, r)

  let pf_ l x = function
    | Empty | FFF _ as r -> FFF (l, x, r)
    | r -> PFP (l, x, r)

(* just old add *)
  let rec add_list x = function
    | Empty -> 
	FFF (Empty, x, Empty)
	  (* insertion to the left *)
    | FFF (l, y, r) | PPF (l, y, r) ->
	if compare_list_list x y > 0 
	then p_f (add_list y l) x r 
	else p_f (add_list x l) y r
	    (* insertion to the right *)
    | PFF (l, y, r) | PFP (l, y, r) ->
	if compare_list_list x y > 0 
	then pf_ l x (add_list y r) 
	else pf_ l y (add_list x r)


  let rec add' x heap =
    match heap with 
    | Empty -> 
	FFF (Empty, (ref [x]), Empty)
	  (* insertion to the left *)
    | FFF (l, y, r) | PPF (l, y, r) ->
	let cmp = compare_elt_list x y in
	if cmp = 0 then 
	  ((*out_str "Add Heap compare equal\n";*)
	   add_if_equal x heap;
	   raise Add_if_equal)
	else
	  ((*out_str "Add Heap compare not equal\n";*)
	   if  compare_elt_list x y > 0 
	   then p_f (add_list y l) (ref [x]) r 
	   else p_f (add' x l) y r)

	    (* insertion to the right *)
    | PFF (l, y, r) | PFP (l, y, r) ->
	let cmp = compare_elt_list x y in
	if cmp = 0 then 
	  ((*out_str "Add Heap compare equal\n";*)
	   add_if_equal x heap;
	   raise Add_if_equal)
	else
	  ((*out_str "Add Heap compare equal\n";*)
	   if cmp > 0 
	   then pf_ l (ref [x]) (add_list y r) 
	   else pf_ l y (add' x r))

(* need this to preserve FFF properties...*)
  let add x heap = 
    try
      add' x heap 
    with 
      Add_if_equal -> heap

  let maximum_list = function
    | Empty -> raise EmptyHeap
    | FFF (_, x, _) | PPF (_, x, _) | PFF (_, x, _) | PFP (_, x, _) -> x
	  

  let maximum = function
    | Empty -> raise EmptyHeap
    | FFF (_, x, _) | PPF (_, x, _) | PFF (_, x, _) | PFP (_, x, _) -> 
	try (List.hd !x) with _-> failwith "heap maximum: should not be empty"

	    (* smart constructors for removal; note that they are different
	       from the ones for insertion! *)
  let p_f l x r = match l with
  | Empty | FFF _ -> FFF (l, x, r)
  | _ -> PPF (l, x, r)

  let pf_ l x = function
    | Empty | FFF _ as r -> PFF (l, x, r)
    | r -> PFP (l, x, r)




  let rec remove_list = function
    | Empty -> 
	raise EmptyHeap
    | FFF (Empty, _, Empty) -> 
	Empty
    | PFF (l, _, Empty) ->
	l
	  (* remove on the left *)
    | PPF (l, x, r) | PFF (l, x, r) ->
        let xl = maximum_list l in
	let xr = maximum_list r in
	let l' = remove_list l in
	if compare_list_list xl xr >= 0 then 
	  p_f l' xl r 
	else 
	  p_f l' xr (add_list xl (remove_list r))
	    (* remove on the right *)
    | FFF (l, x, r) | PFP (l, x, r) ->
        let xl = maximum_list l in
	let xr = maximum_list r in
	let r' = remove_list r in
	if compare_list_list xl xr > 0 then 
	  pf_ (add_list xr (remove_list l)) xl r'
	else 
	  pf_ l xr r'


  exception Last_Elem
  let rec remove_from_list l = 
    match !l with 
    | h::tl -> 
	if tl=[] then
	  raise Last_Elem
	else l:=tl
    |[] -> failwith "heap remove: should not be empty"    

  let remove heap = 
    if heap = Empty then
      raise EmptyHeap
    else
      try 
	apply_f_to_elem remove_from_list heap;
	heap
      with 
	Last_Elem ->
	  (match heap with 
	  | Empty -> 
	      raise EmptyHeap
	  | FFF (Empty,_, Empty) -> Empty
		
	  | PFF (l, _, Empty) -> l

		(* remove on the left *)
	  | PPF (l, x, r) | PFF (l, x, r) ->
              let xl = maximum_list l in
	      let xr = maximum_list r in
	      let l' = 
		try remove_list l with 
		  EmptyHeap -> failwith "heap empty here1"
	      in
	      if compare_list_list xl xr >= 0 then 
		p_f l' xl r 
	      else 
		p_f l' xr (add_list xl (remove_list r))
		  (* remove on the right *)
	  | FFF (l, x, r) | PFP (l, x, r) ->
              let xl = maximum_list l in
	      let xr = maximum_list r in
	      let r' = 	try remove_list r with 
		EmptyHeap -> failwith "heap empty here2" in
	      if compare_list_list xl xr > 0 then 
		pf_ (add_list xr (remove_list l)) xl r'
	      else 
		pf_ l xr r'
	  )

  let rec iter f = function
    | Empty -> 
	()
    | FFF (l, x, r) | PPF (l, x, r) | PFF (l, x, r) | PFP (l, x, r) -> 
	iter f l; List.iter f !x; iter f r

  let rec fold f h x0 = match h with
  | Empty -> 
      x0
  | FFF (l, x, r) | PPF (l, x, r) | PFF (l, x, r) | PFP (l, x, r) -> 
      fold f l (fold f r (List.fold_left f x0 !x))

end
