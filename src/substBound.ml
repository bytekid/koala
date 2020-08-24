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
open TermDB.Open

(* subst.ml *)
type bound = int
type subst = Subst.subst
type term = Term.term
type bound_term = Term.bound_term
type var = Var.var
type bound_var = Var.bound_var
module SMap = Symbol.Map
module VMap = Var.VMap
module VBMap = Var.BMap
type symbol      = Symbol.symbol


(* type assignment = var*term *)
(* exception Subst_bound_var_already_def *)

module SubstKey =
  struct
    type t = bound_var
    let compare = Var.compare_bvar
  end

module SubstM = Map.Make (SubstKey)

include SubstM

type bound_subst = bound_term SubstM.t

let create() = SubstM.empty





(*
let add v t subst =
  if mem v subst
  then 
    raise Subst_bound_var_already_def
  else 
    SubstM.add v t subst
*)
(*
let remove = SubstM.remove
let find = SubstM.find
let map = SubstM.map
let iter = SubstM.iter
let fold = SubstM.fold
let is_empty = SubstM.is_empty 
let mem = SubstM.mem
*)

(* the subsitution is a proper insatiator for a bound var *)
let rec is_proper_var bsubst bv =
  try
    let (new_b, t) = find bv bsubst in
    match t with
    | Term.Fun(_, _, _) -> true
    | Term.Var(new_v, _) -> is_proper_var bsubst (new_b, new_v)
  with
    Not_found -> false

(* the subsitution is a proper insatiator for a particular bound *)
exception True
let is_proper_instantiator bsubst bound =
  let f (bv, v) (new_b, t) rest =
    if bv = bound
    then
      match t with
      | Term.Fun(_, _, _) -> raise True
      | Term.Var(new_v, _) ->
	  if is_proper_var bsubst (new_b, new_v)
	  then raise True
	  else false
    else false
  in
  try
    fold f bsubst false
  with
    True -> true

(* find normalised bound var by subst we assume that there is no var       *)
(* cycles in subst                                                         *)

let rec find_norm b_x bound_subst =
  let b_x_val = (SubstM.find b_x bound_subst) in
  match b_x_val with
  | (b_v, Term.Var(v, _)) ->
      (try find_norm (b_v, v) bound_subst with
	Not_found -> b_x_val
      )
  | _ -> b_x_val

(* returns right normalised subst *)
let right_vnorm_bsubst bsubst = 
  let f bv bt norm_bsubst = 
    let norm_bt = find_norm bv bsubst in
    add bv norm_bt norm_bsubst
  in
  fold f bsubst (create())

(* returns (proper,non_proper) subst after right_vnorm_bsubst *)
let split_proper_inst bsubst = 
  let norm_bs = right_vnorm_bsubst bsubst in 
  let f _bv (b,t) = 
    match t with 
    | Term.Fun _ -> true 
    | Term.Var _ -> false
  in
  SubstM.partition f norm_bs

let split_left_bound bsubst b = 
  let f (bv,_v) _bt = 
    if bv = b then true else false
  in
  SubstM.partition f bsubst


(* applying bound subsitiution to the bound terms adding to term_db we     *)
(* assume that all terms are in term_db (including terms in subst)!        *)
(* renaming_list is an association list of renamimgs of bound vars with    *)
(* vars where vars are terms in db                                         *)
type term_db_ref = TermDB.termDB ref

type renaming_env =
    {
     (* map from types to next un-used variable of this type *)
     mutable ren_max_used_vars : Var.fresh_vars_env;

     (* map from bvars -> var  *)  
     mutable ren_map : (var VBMap.t);
     (*mutable ren_term_db_ref : TermDB.termDB ref;*)
   }

let init_renaming_env term_db_ref =
  {
   ren_max_used_vars = Var.init_fresh_vars_env ();
   ren_map = VBMap.empty;
   (*ren_term_db_ref = term_db_ref*)
 }

(* changes ren_env adding next_unused var to used *)
let get_next_unused_var ren_env vtype = Var.get_next_fresh_var ren_env.ren_max_used_vars vtype
    
let find_renaming renaming_env b_v =
  try
    VBMap.find b_v renaming_env.ren_map
  with
    Not_found ->
      (
       let bv_type = Var.get_bv_type b_v in
       let next_var = get_next_unused_var renaming_env bv_type in
       (*
	 let new_var_term =
	 TermDB.add_ref (Term.create_var_term next_var) renaming_env.ren_term_db_ref in
	 renaming_env.ren_map <- (VBMap.add b_v new_var_term renaming_env.ren_map);
	 new_var_term
	*)
       renaming_env.ren_map <- (VBMap.add b_v next_var renaming_env.ren_map);
       next_var
      )

let in_renaming renaming_env bv =
  VBMap.mem bv renaming_env.ren_map 


(* returns mapping: v-> u iff (bound,v) -> u is in ren_env  *)
let project_renaming ren_env bound = 
  let f (bv,v) u p_ren_map = 
    if (bv = bound)
    then 
      VMap.add v u p_ren_map
    else
      p_ren_map
  in
  VBMap.fold f ren_env.ren_map VMap.empty
 
(*-----------------------*)
(*
let rec apply_bsubst_bterm'
    term_db_ref renaming_env bsubst bterm =
  let (b_t, term) = bterm in
  match term with
  | Term.Fun(sym, args, _) ->
      let new_args =
	Term.arg_map_left
	  (fun term' ->
	    apply_bsubst_bterm'
	      term_db_ref renaming_env bsubst (b_t, term')
	  ) args in
      let new_term = Term.create_fun_term_args sym new_args in
      TermDB.add_ref new_term term_db_ref
  | Term.Var(v, _) ->
      let b_v = (b_t, v) in
      try
	let new_bterm = find b_v bsubst in
	apply_bsubst_bterm'
	  term_db_ref	renaming_env bsubst new_bterm
      with
	Not_found ->
	  add_var_term term_db_ref (find_renaming renaming_env b_v)
*)


(* without adding to term_db_ref *)
let rec apply_bsubst_bterm''
   (* term_db_ref *) renaming_env bsubst bterm =
  let (b_t, term) = bterm in
  match term with
  | Term.Fun(sym, args, _) ->
      let new_args =
	Term.arg_map_left
	  (fun term' ->
	    apply_bsubst_bterm''
	      (* term_db_ref *) renaming_env bsubst (b_t, term')
	  ) args in
      let new_term = Term.create_fun_term_args sym new_args in
      new_term
(*      TermDB.add_ref new_term term_db_ref *)
  | Term.Var(v, _) ->
      let b_v = (b_t, v) in
      try
	let new_bterm = find b_v bsubst in
	apply_bsubst_bterm''
	 (* term_db_ref *) renaming_env bsubst new_bterm
      with
	Not_found ->
           Term.create_var_term (find_renaming renaming_env b_v)
(*	  add_var_term term_db_ref (find_renaming renaming_env b_v) *)

(* with adding to term_db_ref*)
let rec apply_bsubst_bterm' term_db_ref renaming_env bsubst bterm =
  TermDB.add_ref (apply_bsubst_bterm'' renaming_env bsubst bterm) term_db_ref
  

let apply_bsubst_btlist'
    term_db_ref renaming_env bsubst bterm_list =
  List.map
    (apply_bsubst_bterm' term_db_ref renaming_env bsubst)
    bterm_list

let apply_bsubst_bterm term_db_ref bsubst bterm =
  let renaming_env = init_renaming_env () in
  apply_bsubst_bterm' term_db_ref
    renaming_env bsubst bterm

let apply_bsubst_btlist term_db_ref bsubst bterm_list =
  let renaming_env = init_renaming_env () in
  apply_bsubst_btlist'
    term_db_ref renaming_env bsubst bterm_list

(**********apply subst and return both new clause *******)
(********and normalised subst restricted to bound********)
(***************************                    *********)

(* without adding to term_db_ref *)
let rec apply_bsubst_bterm_norm_subst''
     term_db_ref  renaming_env bsubst bound norm_subst_ref bterm =
  let (b_t, term) = bterm in
  match term with
  | Term.Fun(sym, args, _) ->
      let new_args =
	Term.arg_map_left
	  (fun term' ->
	    apply_bsubst_bterm_norm_subst''
	      term_db_ref 
	      renaming_env
	      bsubst bound norm_subst_ref (b_t, term')
	  ) args in
      Term.create_fun_term_args sym new_args 
(*      add_fun_term_args term_db_ref sym new_args *)
  | Term.Var(v, _) ->
      let b_v = (b_t, v) in
      let normalize bound_var =
	try
	  let new_bterm = find bound_var bsubst in
	  apply_bsubst_bterm_norm_subst''
	    term_db_ref 
	    renaming_env
	    bsubst bound norm_subst_ref new_bterm
	with
	  Not_found ->
            Term.create_var_term (find_renaming renaming_env bound_var)
(*	    add_var_term term_db_ref (find_renaming renaming_env bound_var) *)	    
      in
      if b_t = bound
      then
	try
	  Subst.find v !norm_subst_ref
	with
	  Not_found ->
	    let norm_term = TermDB.add_ref (normalize b_v) term_db_ref in
	    norm_subst_ref:= Subst.add v norm_term !norm_subst_ref;
	    norm_term
      else
	normalize b_v

(* with adding to term_db_ref *)
let apply_bsubst_bterm_norm_subst'
    term_db_ref renaming_env bsubst bound norm_subst_ref bterm =
  TermDB.add_ref 
    (apply_bsubst_bterm_norm_subst'' term_db_ref
       renaming_env bsubst bound norm_subst_ref bterm) term_db_ref
  


let apply_bsubst_btlist_norm_subst'
    term_db_ref renaming_env
    bsubst bound norm_subst_ref bterm_list =
  List.map
    (apply_bsubst_bterm_norm_subst'
       term_db_ref renaming_env
       bsubst bound norm_subst_ref)
    bterm_list

let apply_bsubst_btlist_norm_subst
    term_db_ref bsubst bound bterm_list =
  let renaming_env = init_renaming_env () in
  let norm_subst_ref = ref (Subst.create ())
  in
  let new_term_list =
    apply_bsubst_btlist_norm_subst'
      term_db_ref	renaming_env
      bsubst bound norm_subst_ref bterm_list
  in (new_term_list,!norm_subst_ref)

(******************************)
(*to string *)

let to_stream s bound_subst =
  let item_to_str (b_v, v) (b_t, t) =
    s.stream_add_str " (";
    Var.to_stream s v;
    s.stream_add_char '_';
    s.stream_add_str (string_of_int b_v);
    s.stream_add_char ',';
    Term.to_stream s t;
    s.stream_add_char '_';
    s.stream_add_str (string_of_int b_t);
    s.stream_add_str "); "
  in
  iter item_to_str bound_subst

let out = to_stream stdout_stream

let to_string =
  to_string_fun_from_to_stream_fun 30 to_stream

(* let to_string bound_subst = let item_to_str (b_v,v) (b_t,t) rest=       *)
(* rest^" ("^(Var.to_string v)^"_"^(string_of_int b_v)^","^                *)
(* (Term.to_string t)^"_"^(string_of_int b_t)^"); " in fold item_to_str    *)
(* bound_subst ""                                                          *)
