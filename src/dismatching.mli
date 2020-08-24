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

type subst       = Subst.subst
type bsubst      = SubstBound.bound_subst
type term_db_ref = TermDB.termDB ref
type bound       = int
type constr 
type constr_set


(*-------Main Interface------*)

val create_constr_set        : unit -> constr_set

(* subst should be normalised and contain exactly all variables from the constraint set *)
(* even trivial such as X0/X0 *)
val add_constr               : constr_set -> subst -> constr_set
val check_constr_set         : constr_set -> subst -> bool

(* "check_and_add  subst constr_set" checks if subs satisfies constr_set and  *)
(* if it does adds subs to the constr_set returning the new constr_set *)
(* otherwise raises Constr_Not_Sat *)
exception Constr_Not_Sat
val check_and_add            : constr_set -> subst -> constr_set

(* to_stream_constr_set/to_string_constr_set are implemented only in the list representation *)
val to_stream_constr_set     : 'a string_stream -> constr_set -> unit
val to_string_constr_set     : constr_set -> string

val to_flat_subst_list_constr_set  : constr_set -> Subst.flat_subst list 


(*---------------------------------------------------------------------*)      
(* we assume that dismatching constraint is a list of var*term which   *) 
(* forms a completely reduced substitution meaning that      *)
(* if a var. occurs in the left it cannot occur in the right *)
(* for tech. reasons we assume that                          *)
(* vars on the right are implicitly!  renamed from the left  *)
(* so we can have (x,f(x))                                   *)
(*---------------------------------------------------------------------*)  

(*---------------------------*)


(* creates the dismatching constr. from bsubst restricted to bound *)
(*val create_constr      : term_db_ref -> bound -> bsubst -> constr
val create_constr_norm : subst -> constr 
val create_constr_list : unit -> constr_list


val add_constr         : constr_list -> constr -> constr_list

(* true if bsubst restricted to bound satisfies the constr. *)
val check_constr       : bound -> bsubst -> constr -> bool
val check_constr_list  : bound -> bsubst -> constr_list -> bool

val check_constr_norm      : subst -> constr -> bool
val check_constr_norm_list : subst -> constr_list -> bool

*)


(* feature index version of constraints *)

(*
type constr_list_feature
val create_constr_feature_list : unit -> constr_list_feature
val add_constr_feature_list    : 
    constr_list_feature-> constr -> unit (*-> constr_list_feature *)

val check_constr_feature_list  : subst -> constr_list_feature -> bool
*)

(* to stream/string *)


(*
val to_stream                  : 'a string_stream -> constr -> unit
val out                        : constr -> unit

val constr_list_to_stream      : 'a string_stream -> constr_list -> unit
val out_constr_list            : constr_list -> unit

val to_string              : constr -> string
val constr_list_to_string  : constr_list -> string
*)
