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






(* ******************************************************************
 * N-ary priority queues                                            *
 ********************************************************************)

(* A bare element module with only the type and no operations, those
   are given in a separate module at runtime *)
module type Elem0 =
sig 
  type t 
  val compare : t -> t -> int (* basic compare of id's of elements; used to track which elements are added *)
end


(* An element in a priority queue *)
module type ElemN = 
sig

  (* The type of an element in the queue *)
  type t

  (* A comparison function between two elements for each queue *)
  val compare : t -> t -> int

(*
  (* Tsar: there is no need to separate flag for every queue *)
  (* Right now 1 flag for all queues is enough *)
  (* so move it to th QueueN.t *)
  (* TODO: check the case when the clause that's *)
  (* already taken from a queue (but not from all of them) *)
  (* is added back *)

  (* A flag for membership of an element in each queue *)
  val in_queue : t -> bool

  (* A function setting the membership flag for each queue *)
  val assign_in_queue : bool -> t -> unit

*)

  (* The multiplier for each queue *)
  val mult : int
    
end

(* An n-ary priority queue *)
module QueueN (E : Elem0) =
struct 
  
  (* The type of the elements in the queues *)
  type elt = E.t

  module ESet = Set.Make(E)
      

  (* The data structure for one queue *)
  type queue = { 
    
    (* The module of elements in the queue *)
    mutable m_elem : (module ElemN with type t = elt);
    
    (* The queue of elements *) 
    mutable queue : Heap.ImperativeGen(E).t;
    
    (* The counter for the number of elements taken from the queue *)
    mutable mult : int 
      
  }
      
      
  (* The data structure for all n queues *)
  type t = { 
    
    (* The list of queues *) 
    mutable queues : queue list; 
    
    mutable all_elts : ESet.t;

(*
    (* A flag for membership of an element in each queue *)
    in_queue : elt -> bool;

    (* A function setting the membership flag for each queue *)
    assign_in_queue : bool -> elt -> unit;
*)
    (* Try to count the number of unique elements in the queues *)
    mutable num_elem : int 

  }

  (* All queues are empty *)
  exception Empty 
   
  let in_queue queue elt = ESet.mem elt queue.all_elts
    
  (* Create n queues *)
  let create init_size elems (* in_queue assign_in_queue*) =
    
    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in
    
    { queues = 
	
	(* Create one queue of each element module *)
	List.map 
	  (function e -> 

	    (* Get module from value *)
	    let module E = (val e : ElemN with type t = elt) in 

	    { 

	      (* Save module of elements *)
	      m_elem = e;
	      
	      (* Create heap from element *)
	      queue = 
		H.create 
		  (module E : Heap.Ordered with type t = elt) 
		  init_size;

	      (* Initialise modulus counter *)
	      mult = 0 

	    })
	  elems;

      all_elts = ESet.empty;
(*
      (* Initialise in_queue from input *)
      in_queue = in_queue;

      (* Initialise assign_in_queue from input *)
      assign_in_queue = assign_in_queue;
*)
      (* Initialise counter of elements *)
      num_elem = 0 }


  (* The number of elements in the queues *)
  let num_elem { num_elem } = num_elem

  (* Add an element to all queues *)
  let add_all ({ queues = queue_n } as q) elem = 

    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in

    if not (in_queue q elem) then (
      (* Add element to all queues *)
      List.iter
        (function { m_elem; queue; _ } ->

          (* Get module from value *)
          let module E = (val m_elem : ElemN with type t = elt) in

          (* Queue ratio must not be 0 *)
          if (E.mult > 0)
          then 
            (
            (* Add element to queue *)
            H.add queue elem;

            (* Flag element as in queue *)
(*            q.assign_in_queue true elem *)
            q.all_elts <- ESet.add elem q.all_elts
          )
        )
      queue_n;
      (* Increment counter of elements in queue *)
      q.num_elem <- succ q.num_elem
    )

  (* TODO: Create function add_some that adds to some queues only and
     correctly changes the num_elem counter, that is, does not count
     duplicates *)
      

  (* All queues are empty? *)
(*
  let is_empty { queues = queue_n } = 

    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in
    
    (* All queues are empty? *)
    List.for_all
      (function { queue } -> H.is_empty queue)
      queue_n
*)

(* all_q can be empty and there are still possible elements in some queues *)
  let is_empty all_q = ESet.is_empty all_q.all_elts


  (* Clean queues *)
  let clean init_size { queues = queue_n } =
  
    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in

    List.iter
      (function { m_elem; queue } as q -> 

	(* Get module from value *)
	let module E = (val m_elem : ElemN with type t = elt) in 

	(* Recreate queue *)
	q.queue <- 
	  H.create (module E : Heap.Ordered with type t = elt) init_size)
      queue_n


  (* Remove first element from the next priority queue *)
  let rec remove' ({ queues = queue_n; num_elem } as all_q) = 
    (* Local module binding at outermost level *)
    let module H = Heap.ImperativeGen(E) in function 

      (* No element to remove from any queue?

	 Not every queue is empty, this has to be checked by the
	 calling function, otherwise we will loop infinitely. *)
      | [] -> 

	(* Format.eprintf "No elements available in any queue@."; *)
	(* Reset modulus counters in all queues to their maximum *)
	List.iter
	  (function ({ m_elem } as q) -> 
	    let module E = (val m_elem : ElemN with type t = elt) in
	    q.mult <- E.mult)
	  queue_n;

	(* All queues are empty? *)
	if is_empty all_q then 
	  
	  (* Raise exception *)
	  raise Empty 
	    
	else

	  (* Restart search for element to remove *)
	  remove' all_q queue_n

      (* First queue is not empty and the modulus counter is not 0? *)
      | ({ queue; m_elem; mult } as q) :: tl 
	  when mult > 0 && not (H.is_empty queue) -> 
	
	(
	  (* Format.eprintf 
	    "Removing from queue %d@." 
	    ((List.length queue_n) - (List.length tl)); *)

	  (* Module for elements in this queue *)
	  let module E = (val m_elem : ElemN with type t = elt) in 

	  (* Take first element from the queue *)
	  let elem = H.pop_maximum queue in
	  
	  (* Check if element has not been removed from queue *)
	  if (in_queue all_q elem) then
	  
	    (

	      (* Flag element as removed from every queue *)
(*	      all_q.assign_in_queue false elem; *)
             all_q.all_elts <- ESet.remove elem all_q.all_elts;
	      
	      (* Decrement modulus counter of queue *)
	     q.mult <- pred mult;
	     
	     all_q.num_elem <- pred num_elem;

	      (* Return element *)
	     elem
		
	    )
	      
	  (* Element has been removed from this queues *)
	  else
	    
	    (

	      (* Format.eprintf 
		"Element is not queue@."; *)
	      
	      (* Remove next element from this queue *)
	      remove' all_q (q :: tl)

	    )
	      
	)
	  
      (* First queue is empty or modulus counter is 0 *)
      | _ :: tl ->
        (* Try to remove from some next queue *)
        remove' all_q tl
	

  (* Remove first element from the next priority queue *)
  let remove ({ queues = queue_n } as q) = 

    (* All queues are empty? *)
    if is_empty q 
    then 
      (

      (* Raise exception *)
      raise Empty 
      )
    else 
      
      (* Remove some element from some queue *)
      remove' q queue_n
	
end
  
