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

type var = int  (* start from 1  *)
type lit = int  (* pos even, neg odd  *)

(* shorthands *)
type v = var
type l = lit


let var_to_lit pol v = 
  if pol
  then
    (v lsl 1)
  else
    ((v lsl 1) +1)    

let is_pos_lit l = ((l mod 2) = 0)
    
let lit_to_var l = 
  if (is_pos_lit l)
  then
    (true, (l lsr 1))
  else
    (false, (l lsr 1))
    
let get_var_lit l = (l lsr 1)
  
let compl_lit l = 
  let (pol,v) = lit_to_var l in
  var_to_lit (not pol) v

let is_compl l1 l2 =
  l1 = (compl_lit l2)

let get_var_id v = v

let get_lit_id l = l

let make_var n = 
  (assert (n >0));
  n
    
let make_lit n = 
  assert (n != 0);
  let v = make_var (abs n) in
  if n > 0 
  then
    var_to_lit true v 
  else
    var_to_lit false v 

let next_var v = v + 1
    
let var_to_string v = string_of_int v 

let var_list_to_string v_list = list_to_string  var_to_string v_list " "

let var_list_to_string_0 v_list = (var_list_to_string v_list)^" 0"


let lit_to_string l = 
  let (pol,v) = lit_to_var l in 
  let l_int = 
    if pol 
    then
      v
    else
      (-v)
  in
  string_of_int l_int
(*  end *)
    
let lit_list_to_string l_list = list_to_string  lit_to_string l_list " "

let lit_list_to_string_0 l_list = (lit_list_to_string l_list)^" 0"


let var_compare v1 v2 = Pervasives.compare (get_var_id v1) (get_var_id v2)

let var_equal v1 v2 = (v1 = v2)

let lit_compare l1 l2 = Pervasives.compare (get_lit_id l1) (get_lit_id l2)

let lit_equal l1 l2 = (l1 = l2) 

(* var modules *)    
module VKey =
  struct  
    type t = var
    let compare = var_compare
    let equal = var_equal
    let hash v = get_var_id v
  end
    
module VMap = Map.Make(VKey)
module VSet = Set.Make(VKey)
module VHashtbl = Hashtbl.Make(VKey)
module VUF = Union_find.Make(VKey)

(* lit modules *)    
module LKey =  
  struct  
    type t = lit
    let compare = lit_compare
    let equal = lit_equal
    let hash l = get_lit_id l
  end

module LMap = Map.Make(LKey)
module LSet = Set.Make(LKey)
module LHashtbl = Hashtbl.Make(LKey)
module LUF = Union_find.Make(LKey)
