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





type var   (* var *)
type lit   (* lit *)

val var_to_lit : bool -> var -> lit (* pol. as bool *)
val get_var_lit : lit -> var
val lit_to_var : lit -> bool * var
val is_pos_lit : lit -> bool
val compl_lit : lit -> lit
val is_compl : lit -> lit -> bool
val make_var : int -> var (* pos int *)
val make_lit : int -> lit (* +- v *)	
val get_lit_id : lit -> int (* do not mix var and lit ids *)
val get_var_id : var -> int 

val var_compare : var -> var -> int
val var_equal   : var -> var -> bool
val lit_compare : lit -> lit -> int
val lit_equal   : lit -> lit -> bool

val var_to_string : var -> string
val var_list_to_string : var list -> string
val var_list_to_string_0 : var list -> string

val lit_to_string : lit -> string
val lit_list_to_string : lit list -> string
val lit_list_to_string_0 : lit list -> string


module VKey :
  sig
    type t = var
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
  end

module VMap : Map.S with type key = var
module VSet : Set.S with type elt = var
module VHashtbl : Hashtbl.S with type key = var
module VUF : Union_find.UF with type e = var

module LKey :
  sig
    type t = lit
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
  end

module LMap : Map.S with type key = lit
module LSet : Set.S with type elt = lit
module LHashtbl : Hashtbl.S with type key = lit
module LUF : Union_find.UF with type e = lit
