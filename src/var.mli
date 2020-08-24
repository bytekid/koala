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
type symbol = Symbol.symbol
type var
type t=var

type bound_var = var Lib.bind

(* creates variable with symbol as type; in most cases use first_var, next_var *)
val create : symbol -> int -> var

val get_type : var -> symbol
val get_var_val : var -> int

val get_bv_type : bound_var -> symbol

(* get_first_var vtype *)
val get_first_var  : symbol -> var
val get_next_var   : var -> var

(* get_next_var(v) is greater than v *)
val compare        : var -> var -> int
val equal          : var -> var -> bool

val compare_bvar   : bound_var -> bound_var -> int
val equal_bvar     : bound_var -> bound_var -> bool
val hash           : var -> int
(* val index          : var -> int *)


(*--------------------------*)

(* map from types to the max used variable of this type *)	

type fresh_vars_env

val init_fresh_vars_env : unit -> fresh_vars_env

(* initialises fresh vars away from variables in var_list, so next vars will be always away from the list *)

val init_fresh_vars_env_away : var list -> fresh_vars_env

(* creates new var of vtype in the fresh_vars_env, and declares it as used : by exteding the env with it *)	
				
val get_next_fresh_var : fresh_vars_env -> symbol -> var

(*---------------*)

val to_stream      : 'a string_stream -> var -> unit
val out            : var -> unit

val pp_var : Format.formatter -> var -> unit

val to_string      : var -> string
val to_prolog      : var -> string

val var_list_to_string : var list -> string
(*---------------------------------*)


module VKey :
  sig
    type t = var
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
  end

module VMap : Map.S with type key = var
module VSet : Set.S with type elt = var
module VHashtbl : Hashtbl.S with type key = var



(* the same for bound vars *)
module BKey :
  sig
    type t = bound_var
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
  end

module BMap : Map.S with type key = bound_var
module BSet : Set.S with type elt = bound_var
module BHashtbl : Hashtbl.S with type key = bound_var


(* -------- renaming ------------*)

(* variable renaming  *)
type renaming = var VMap.t

(* if var is returned unchanged if not in the renaming *)
val apply_renaming : renaming -> var -> var 

val apply_renaming_vlist : renaming -> var list -> var list

(* assumes than renaming is one-to-one *)
val reverse_renaming : renaming -> renaming
