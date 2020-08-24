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
open Options

type symbol = Symbol.symbol

(* second is var type symbol *)
type var = int * symbol
type t = var
type bound_var = var Lib.bind

let create vtype v = (v,vtype)

let get_type (v,vtype) = vtype 

let get_var_val (v,vtype) = v 

let get_bv_type (b,(v,vtype)) = vtype
    
let get_first_var vtype = (0, vtype)

let get_next_var (var, vtype) = (var + 1, vtype)

let compare = 	
  pair_compare_lex Pervasives.compare Symbol.compare

(* assume vt are shared but v are not shared *)
let equal (v1, vt1) (v2, vt2) = (v1 = v2) && (vt1 == vt2)

let compare_bvar =
  pair_compare_lex Pervasives.compare compare 

let equal_bvar bv1 bv2 =
  if (compare_bvar bv1 bv2) = cequal
  then true
  else false

let hash (v, vt) = 
  let vt_hash = Symbol.hash vt in
  hash_sum v vt_hash
    
let hash_bvar (b, v) = 
  hash_sum (hash v) b

    
(* let index var = var *)

let to_stream s (v,vt) =
  if !current_options.tptp_safe_out
  then
    (s.stream_add_char 'X';
     s.stream_add_str (string_of_int v);
    )
  else 
    (
     s.stream_add_char 'X';
     s.stream_add_str (string_of_int v);
     s.stream_add_char '_';
     (Symbol.to_stream s vt)
    )

let pp_var ppf (v,vt) = 
  if !current_options.tptp_safe_out
  then 
    Format.fprintf ppf "X%d_%d" v (Symbol.get_fast_key vt)
  else
    Format.fprintf ppf "X%d_%s" v (Symbol.to_string vt)

let out = to_stream stdout_stream

let to_string =
  to_string_fun_from_to_stream_fun 5 to_stream

let to_prolog = to_string

let var_list_to_string vl = list_to_string to_string vl ","

(* let to_string var = "X"^(string_of_int var) *)

(* for uniformity to_string is via buffers *)

(* let fast_key_to_int var = var *)
module VKey = 
  struct
    type t      = var
    let equal   = equal  
    let hash    = hash 
    let compare = compare
  end

module VMap = Map.Make(VKey)
    
module VSet = Set.Make(VKey)

module VHashtbl = Hashtbl.Make(VKey)

type var_set = VSet.t

module BKey = 
  struct
    type t      = bound_var
    let equal   = equal_bvar  
    let hash    = hash_bvar 
    let compare = compare_bvar
  end

module BMap = Map.Make(BKey)
    
module BSet = Set.Make(BKey)

module BHashtbl = Hashtbl.Make(BKey)

type bvar_set = BSet.t

module SMap = Symbol.Map


(*-----------------------*)
(* variable renaming  *)
type renaming = var VMap.t

let apply_renaming ren v = 
  try 
    VMap.find v ren 
  with 
    Not_found -> v

let apply_renaming_vlist ren vlist = List.map (apply_renaming ren) vlist

let reverse_renaming ren = 
  let f v u rev_ren = 
    assert (not (VMap.mem u rev_ren));
    VMap.add u v rev_ren
  in
  VMap.fold f ren VMap.empty

(*--------------------------------------*)    
(* map from types to max used variable of this type *)	
type fresh_vars_env = (var SMap.t) ref

let init_fresh_vars_env () = ref SMap.empty

(* initialises fresh vars away from variables in var_list, so next vars will be always away from the list *)
let init_fresh_vars_env_away var_list = 
  let fresh_vars_env = init_fresh_vars_env () in 
  let f v  = 
    begin
      let v_val = get_var_val v in 
      let vtype = get_type v in
      try
	let max_used_var = SMap.find vtype !fresh_vars_env in
	if (v_val > (get_var_val max_used_var)) 
	then				
	  (
	   fresh_vars_env := 
	     SMap.add 
	       vtype 
	       v 
	       !fresh_vars_env
          )
	else
	  () 
      with
      | Not_found ->
	  (	fresh_vars_env := SMap.add vtype v !fresh_vars_env)
    end
  in	
  List.iter f var_list;
  fresh_vars_env

    

(* creates new var of vtype in the fresh_vars_env, and declares it as used : by exteding the env with it *)	
    
let get_next_fresh_var fresh_vars_env vtype =
  let next_fresh_var =
    try
      let max_used_var = SMap.find vtype !fresh_vars_env in
      get_next_var max_used_var
    with
    | Not_found ->
	get_first_var vtype
  in
  fresh_vars_env := SMap.add vtype next_fresh_var !fresh_vars_env;
  next_fresh_var
