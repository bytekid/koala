open Lib
open Logic_interface

type def_map = (term list) list TMap.t


(* currently only conj/disj definitions are covered  *)
(* definitions are of the form l -> [u_1,..,u_1] where l is a literal and (\forall x [l <-> u_1 &..& u_n ]) *)
(* implied literals are difinitions of the from l -> []; [] stands for T *)
(* if defintion is simple l1<-> l2 then both l1->[l2] and l2 -> [l1] will be in the map *)
(* it is possible that both lit and its compl have definitions; (unless one is implied) *)
(* def are wrt the current state of the solver + input clauses *)
(* TODO: several definitions of the same literal  *)


(* cmp priority larger prioritised for right handsides of definitions; (smaller are eliminated first from defs) *)

val get_def_map :  ?cmp:(term -> term -> int) -> clause list -> def_map 

val out_def_map : def_map -> unit

(* equivalence defs of the form a <-> (~)(b <-> c) *)

type equiv_defs = 
    {
     mutable eqd_odd  : (term list) list; (* atom list for defs with odd negs*)
     mutable eqd_even : (term list) list; (* even negs *)
   }

val get_equiv_defs : clause list -> equiv_defs

val out_equiv_defs : equiv_defs -> unit
