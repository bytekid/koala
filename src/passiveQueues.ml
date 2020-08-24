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


(* passive queue implementation for instantiation.ml and discount.ml *)

open Lib
open Options
open Statistics
open Logic_interface

exception Passive_Empty

(* priority list is a list of lists e.g: [[Cl_Num_of_Symb;Cl_Age];[Cl_Ground;Cl_Num_of_Var];..]*)

(* for simple queues/stacks we take first priority from the priority list *)
let cmp_queue priorities =
  let priority = 
    match priorities with
    | hd::tl -> hd
    | [] -> [Options.Cl_Age true]
  in
  Clause.cl_cmp_type_list_to_lex_fun priority

(*--------------Simple Passive using Queue------------*)
module Passive_SQueue =
  struct
    (* type *)
    type t = {
      (* simple queue *)
      mutable queue : clause Queue.t param;
      (* compare on clauses *)
      compare : clause -> clause -> int;
      (* number of elements *)
      mutable num_elem : int;
    }

    (*---------------- interface ----------------*)

    (* create passive queue*)
    let create priorities =
      (* create passive queues *)
      {
        queue = Def(Queue.create ());
        compare = cmp_queue priorities;
        num_elem = 0
      }

    (* add clause to a queue *)
    let add pq clause =
(*      if not (Clause.get_is_dead clause)
      then
*)
      (
        Queue.push clause (get_param_val pq.queue);
  (*      Clause.set_ps_in_passive_queue true clause; *)
        pq.num_elem <- succ pq.num_elem
      )

    (* add list of clauses to a queue *)
    let add_list pq clauses =
      (* List.rev: maximal first *)
      let clauses' = List.rev (List.sort pq.compare clauses) in
      List.iter (add pq) clauses'

    (* get the top clause from a queue *)
    let remove pq =
      try
        let clause = Queue.pop (get_param_val pq.queue) in
(*        Clause.set_ps_in_passive_queue false clause; *)
        pq.num_elem <- pred pq.num_elem;
        clause
      with
        Queue.Empty -> raise Passive_Empty

    let rec remove_from_passive_until pq f =
      let clause = remove pq in
      if (f clause) 
      then 
        clause 
      else 
        (
         remove_from_passive_until pq f
        )

    (* get number of elements in the queue *)
    let num_elem { num_elem } = num_elem

    (* clear all the queues so they can be garbage collected *)
    let finalise pq = pq.queue <- Undef
  end

(*--------------Simple Passive using Stack------------*)
module Passive_Stack =
  struct
    (* type *)
    type t = {
      (* simple stack *)
      mutable stack : clause Stack.t param;
      (* compare on clauses *)
      compare : clause -> clause -> int;
      (* number of elements *)
      mutable num_elem : int;
    }

    (*---------------- interface ----------------*)

    (* create passive queue*)
    let create priorities =
      (* create passive queues *)
      {
        stack = Def(Stack.create ());
        compare = cmp_queue priorities;
        num_elem = 0
      }

    (* add clause to a queue *)
    let add pq clause =
(*
      if not (Clause.get_is_dead clause)
      then
*)
      (
        Stack.push clause (get_param_val pq.stack);
(*        Clause.set_ps_in_passive_queue true clause; *)
        pq.num_elem <- succ pq.num_elem
      )

    (* add list of clauses to a queue *)
    let add_list pq clauses =

(* max will be first after adding all *)
      let clauses' = List.sort pq.compare clauses in
      List.iter (add pq) clauses'

    (* get the top clause from a queue *)
    let remove pq =
      try
        let clause = Stack.pop (get_param_val pq.stack) in
(*        Clause.set_ps_in_passive_queue false clause; *)
        pq.num_elem <- pred pq.num_elem;
        clause
      with
        Stack.Empty -> raise Passive_Empty

    let rec remove_from_passive_until pq f =
      let clause = remove pq in
      if (f clause) 
      then 
        clause 
      else 
        (
         remove_from_passive_until pq f
        )
    (* get number of elements in the queue *)
    let num_elem { num_elem } = num_elem

    (* clear all the queues so they can be garbage collected *)
    let finalise pq = pq.stack <- Undef
  end

(*--------------Simple Passive using List------------*)
module Passive_List =
  struct
    (* type *)
    type t = {
      (* simple list *)
      mutable clist : clause list param;
      (* compare on clauses *)
      compare : clause -> clause -> int;
      (* number of elements *)
      mutable num_elem : int;
    }

    (*---------------- interface ----------------*)

    (* create passive queue*)
    let create priorities =
      (* create passive queues *)
      {
        clist = Def([]);
        compare = cmp_queue priorities;
        num_elem = 0
      }

    (* add clause to a queue *)
    let add pq clause =
(*
      if not (Clause.get_is_dead clause)
      then
*)
      (
        pq.clist <- Def(clause :: (get_param_val pq.clist));
(*        Clause.set_ps_in_passive_queue true clause; *)
        pq.num_elem <- succ pq.num_elem
      )

    (* add list of clauses to a queue *)
    let add_list pq clauses =

(* max will be first after adding all *)
      let clauses' = List.sort pq.compare clauses in
      List.iter (add pq) clauses'

    (* get the top clause from a queue *)
    let remove pq =
      match get_param_val pq.clist with
      | clause::tl ->
        pq.clist <- Def(tl);
(*        Clause.set_ps_in_passive_queue false clause; *)
        pq.num_elem <- pred pq.num_elem;
        clause
      | [] -> raise Passive_Empty

    let rec remove_from_passive_until pq f =
      let clause = remove pq in
      if (f clause) 
      then 
        clause 
      else 
        (
         remove_from_passive_until pq f
        )
    (* get number of elements in the queue *)
    let num_elem { num_elem } = num_elem

    (* clear all the queues so they can be garbage collected *)
    let finalise pq = pq.clist <- Undef
  end

(*-------------------- Priority queues implementation ----------------*)

(* total comparison  for clauses!----*)
(* Heap.ImperativeEq does not work yet..... *)

module Pq =
  struct
    (* element for priority queues *)
    module Elem0 =
      struct
        type t = clause
        let compare = Clause.compare
      end

    (* type of priority queues *)
    module PriQ = Priority_queues.QueueN(Elem0)

    (* type *)
    type t = {
      (* priority queues *)
      mutable queues : PriQ.t param;
    }

    (* Initial capacity of a passive queue *)
    let init_capacity_priority = 10001

    (*---------------- interface ----------------*)

    (* create passive queues from given priority values and frequences *)
    let create priority mults =
      assert ((List.length priority) = (List.length mults));
      (* create a single queue data by given priority and freq *)
      let create_elem prior mult =
        (* pre-evaluate compare function *)
        let cmp_fun = Clause.cl_cmp_type_list_to_lex_fun prior in
        (* Create a module from given parameters *)
        let module ElemN =
          struct
            type t = clause
            let compare = cmp_fun
            let mult = mult
          end
        in
        (* Return module *)
        (module ElemN : Priority_queues.ElemN with type t = clause)
      in
      (* build array of elements out of input *)
      let elems = List.map2 create_elem priority mults in
(*
      (* pre-evaluate in_queue function *)
      let in_queue = Clause.get_ps_in_passive_queue in
      (* set that the clause is in the corresponding queue *)
      let set_param = Clause.set_ps_in_passive_queue in
*)
      (* create priority queues of given capacity *)
      {
(*        queues = Def(PriQ.create init_capacity_priority elems in_queue set_param) *)
       queues = Def(PriQ.create init_capacity_priority elems) 

      }

    (* add clause to a given queue *)
    let add pq clause =
(*
      if not (Clause.get_is_dead clause)
      then
*)
        PriQ.add_all (get_param_val pq.queues) clause

    (* add list of clauses to a given queue *)
    let add_list pq clauses =
      List.iter (add pq) clauses

    (* get the top clause from a given queue *)
    let remove pq = 
      try 
        let clause = PriQ.remove (get_param_val pq.queues) in
        clause
      with PriQ.Empty ->
        (
        (* if we find that passive queue is empty then we need to clean it: *)
        (* 1. assign in_queue param to false in all clauses in the remaining queue*)
        (* 2. release memory and assign new queues *)
        PriQ.clean init_capacity_priority (get_param_val pq.queues);
        raise Passive_Empty
        )

    (* remove top clauses until (f c) = true *)
    (* can raise Passive_Empty *)
    let rec remove_from_passive_until pq f =
      let clause = remove pq in
      if (f clause) 
      then 
        clause 
      else 
        (
         remove_from_passive_until pq f
        )

(* before  removed until not the case  that ((Clause.get_ps_in_active clause) || (Clause.get_is_dead clause)) *)

    (* get number of elements in the queue *)
    let num_elem pq = PriQ.num_elem (get_param_val pq.queues)

    (* clear all the queues so they can be garbage collected *)
    let finalise pq = pq.queues <- Undef
  end

(* generalizing type for passive queue *)
type passive_queue =
  | PQ_SQueue of Passive_SQueue.t
  | PQ_Stack of Passive_Stack.t
  | PQ_List of Passive_List.t
  | PQ_PQueues of Pq.t

(* create passive queue depending on the type *)
let create_passive_queue pq_type priorities freqs =
  match pq_type with
  | PQT_Queue -> PQ_SQueue(Passive_SQueue.create priorities)
  | PQT_Stack -> PQ_Stack(Passive_Stack.create priorities)
  | PQT_List -> PQ_List(Passive_List.create priorities)
  | PQT_PriorityQueues -> PQ_PQueues(Pq.create priorities freqs)

(* add a clause to the passive queue *)
let add_to_passive pq clause =
  match pq with
  | PQ_SQueue(squeue) -> Passive_SQueue.add squeue clause
  | PQ_Stack(stack) -> Passive_Stack.add stack clause
  | PQ_List(clist) -> Passive_List.add clist clause
  | PQ_PQueues(pqueues) -> Pq.add pqueues clause

(* add list of clauses to the passive queue *)
let add_list_to_passive pq clauses =
  match pq with
  | PQ_SQueue(squeue) -> Passive_SQueue.add_list squeue clauses
  | PQ_Stack(stack) -> Passive_Stack.add_list stack clauses
  | PQ_List(clist) -> Passive_List.add_list clist clauses
  | PQ_PQueues(pqueues) -> Pq.add_list pqueues clauses

(* get the 1st clause of the passive queue *)
let remove_from_passive pq =
  match pq with
  | PQ_SQueue(squeue) -> Passive_SQueue.remove squeue
  | PQ_Stack(stack) -> Passive_Stack.remove stack
  | PQ_List(clist) -> Passive_List.remove clist
  | PQ_PQueues(pqueues) -> Pq.remove pqueues

(* a function to get the number of elements in pq *)
let num_elem pq =
  match pq with
  | PQ_SQueue(squeue) -> Passive_SQueue.num_elem squeue
  | PQ_Stack(stack) -> Passive_Stack.num_elem stack
  | PQ_List(clist) -> Passive_List.num_elem clist
  | PQ_PQueues(pqueues) -> Pq.num_elem pqueues

let remove_from_passive_until pq f = 
   match pq with
  | PQ_SQueue(squeue) -> Passive_SQueue.remove_from_passive_until squeue f
  | PQ_Stack(stack) -> Passive_Stack.remove_from_passive_until stack f
  | PQ_List(clist) -> Passive_List.remove_from_passive_until clist f
  | PQ_PQueues(pqueues) -> Pq.remove_from_passive_until pqueues f



(* free memory of a passive queue *)
let finalise pq =
  match pq with
  | PQ_SQueue(squeue) -> Passive_SQueue.finalise squeue
  | PQ_Stack(stack) -> Passive_Stack.finalise stack
  | PQ_List(clist) -> Passive_List.finalise clist
  | PQ_PQueues(pqueues) -> Pq.finalise pqueues
