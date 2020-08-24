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
open Logic_interface

(* This is an implementation of a datatype with a finite domain *)
(* Given a datatype (that is already in a SymbolDB) it allows one *)
(* to create constants of that datatype. *)
(* *)
(* The concepts are organiced in GROUPs. Group is defined by a user. *)
(* All concepts in all groups are different. *)
(* *)

(* index of the last used constant *)
let const_index = ref 0

(* auxilliary method to generate a const name *)
let get_type_const_name type_symb group_id const_id =
  let const_format = format_of_string "$$c_%s_g%d_%d" in
  let type_name = Symbol.to_string type_symb in
  Format.sprintf const_format type_name group_id const_id

(* auxilliary method to create a const with a given name of a given type *)
let const_by_type const_name type_symb =
  let const_stype = Symbol.create_stype [] type_symb in
  let const = create_symbol const_name const_stype in
  const

(* auxilliary method to create a const term with a given name of a given type *)
let const_term_by_type const_name type_symb =
  let const = const_by_type const_name type_symb in
  add_fun_term const []

(* auxilliary method to create a const of a given type in a group with a given id *)
let get_const_g type_symb group_id const_id =
  let const_name = get_type_const_name type_symb group_id const_id in
  let const_term = const_term_by_type const_name type_symb in
  const_term

(* create the 1st const of a given type in a group *)
let get_first_const_g type_symb group_id =
  get_const_g type_symb group_id 0

(* create the 1st const of a given type in a default group *)
let get_first_const type_symb =
  get_const_g type_symb 0 0

(* create new const of a given type in a group *)
let get_new_const_g type_symb group_id =
  const_index := succ !const_index;
  get_const_g type_symb group_id !const_index

(* create new const of a given type in a default group *)
let get_new_const type_symb =
  get_new_const_g type_symb 0
