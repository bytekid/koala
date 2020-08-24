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

(* Heaps *)

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

(*S Partially generic imperative implementation. *)

(* The module is a functor paramterised with a module that only
   contains the type of the elements. The comparison function is given
   as a module parameter at runtime. This uses the first-class module
   feature introduced in OCaml 3.12.

   The type of this heap is only dependent on the type of the
   elements, since the ordering of the elements is a runtime
   parameter, heaps with the same element types but different
   orderings are of the same type and can be mixed in a list, see
   n-ary priority queues. *)

module ImperativeGen(E : Elem0) : sig
    
  (* Type of imperative heaps.
     (In the following [n] refers to the number of elements in the heap) *)
  type t 
    
  (* The type of elements in the heap *)
  type elt = E.t
      
  (* [create o c] creates a new heap, with initial capacity of
     [c]. The addtional parameter [o] is a module of type Ordered that
     gives the ordering of the elements. *)
  val create : (module Ordered with type t = elt) -> int -> t

  (* [is_empty h] checks the emptiness of [h] *)
  val is_empty : t -> bool

  (* [add x h] adds a new element [x] in heap [h]; size of [h] is
     doubled when maximum capacity is reached; complexity
     $O(log(n))$ *)
  val add : t -> elt -> unit

  (* [maximum h] returns the maximum element of [h]; raises
     [EmptyHeap] when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> elt

  (* [remove h] removes the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(log(n))$ *)
  val remove : t -> unit

  (* [pop_maximum h] removes the maximum element of [h] and returns
     it; raises [EmptyHeap] when [h] is empty; complexity
     $O(log(n))$ *)
  val pop_maximum : t -> elt

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit

  val fold : ('a ->  elt -> 'a) -> t -> 'a -> 'a

end


(*S Imperative implementation. *)

module Imperative(X: Ordered) : sig

  (* Type of imperative heaps.
     (In the following [n] refers to the number of elements in the heap) *)

  type t 

  (* [create c] creates a new heap, with initial capacity of [c] *)
  val create : int -> t

  (* [is_empty h] checks the emptiness of [h] *)
  val is_empty : t -> bool

  (* [add x h] adds a new element [x] in heap [h]; size of [h] is doubled
     when maximum capacity is reached; complexity $O(log(n))$ *)
  val add : t -> X.t -> unit

  (* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> X.t

  (* [remove h] removes the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(log(n))$ *)
  val remove : t -> unit

  (* [pop_maximum h] removes the maximum element of [h] and returns it;
     raises [EmptyHeap] when [h] is empty; complexity $O(log(n))$ *)
  val pop_maximum : t -> X.t

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (X.t -> unit) -> t -> unit
(* Old
  val fold : (X.t -> 'a -> 'a) -> t -> 'a -> 'a
*)
  val fold : ('a ->  X.t -> 'a) -> t -> 'a -> 'a
end

(* Does not work.... check later....
module ImperativeEq(X: Ordered) : sig

  (* Type of imperative heaps.
     (In the following [n] refers to the number of elements in the heap) *)

  type t 

  (* [create c] creates a new heap, with initial capacity of [c] *)
  val create : int -> t

  (* [is_empty h] checks the emptiness of [h] *)
  val is_empty : t -> bool

  (* [add x h] adds a new element [x] in heap [h]; size of [h] is doubled
     when maximum capacity is reached; complexity $O(log(n))$ *)
  val add : t -> X.t -> unit

  (* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> X.t

  (* [remove h] removes the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(log(n))$ *)
  val remove : t -> unit

  (* [pop_maximum h] removes the maximum element of [h] and returns it;
     raises [EmptyHeap] when [h] is empty; complexity $O(log(n))$ *)
  val pop_maximum : t -> X.t

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (X.t -> unit) -> t -> unit
(* Old
  val fold : (X.t -> 'a -> 'a) -> t -> 'a -> 'a
*)
  val fold : ('a ->  X.t -> 'a) -> t -> 'a -> 'a
end
*)



(*S Functional implementation. *)

module type FunctionalSig = sig

  (* heap elements *)
  type elt

  (* Type of functional heaps *)
  type t

  (* The empty heap *)
  val empty : t

  (* [add x h] returns a new heap containing the elements of [h], plus [x];
     complexity $O(log(n))$ *)
  val add : elt -> t -> t

  (* [maximum h] returns the maximum element of [h]; raises [EmptyHeap]
     when [h] is empty; complexity $O(1)$ *)
  val maximum : t -> elt

  (* [remove h] returns a new heap containing the elements of [h], except
     the maximum of [h]; raises [EmptyHeap] when [h] is empty; 
     complexity $O(log(n))$ *) 
  val remove : t -> t

  (* usual iterators and combinators; elements are presented in
     arbitrary order *)
  val iter : (elt -> unit) -> t -> unit

(* old
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
*)
  val fold : ('a -> elt -> 'a) -> t -> 'a -> 'a

end

module Functional(X: Ordered) : FunctionalSig with type elt = X.t

module FunctionalEq(X: Ordered) : FunctionalSig with type elt = X.t
