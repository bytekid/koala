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

type var         = Var.var
type term        = Term.term
type bound       = int
type bvar        = Var.bound_var
type bterm       = Term.bound_term
type subst       = Subst.subst
type bsubst      = SubstBound.bound_subst
type term_db_ref = TermDB.termDB ref
      
type var_term    = var * term


(*---------------------------------------------------------------------*)      
(* we assume that dismatching constraint is a list of var*term which   *) 
(* forms a completely reduced substitution meaning that      *)
(* if a var. occurs in the left it cannot occur in the right *)
(* for tech. reasons we assume that                          *)
(* vars on the right are implicitly!  renamed from the left  *)
(* so we can have (x,f(x))                                   *)
(*---------------------------------------------------------------------*)  




(*
  let var_term_to_string (v,t) =  (Term.to_string t)^"/"^(Var.to_string v)  
  let to_string constr =  
  "["^(Lib.list_to_string var_term_to_string constr ",")^"]"

  let constr_list_to_string constr_list = 
  Lib.list_to_string to_string constr_list "\n"
 *)
      


exception Constr_Not_Sat

(*--------------------------------------------------------------------*)
(*------------- List version of Dismating Constr.---------------------*)
    

(* Constr is sat if it doesnot match the subst*)

module FSSet = Subst.FSSet

type constr_plain = Subst.flat_subst

      
type constr_set_plain  = 
    {
     set      : FSSet.t;
     set_size : int
   }

let create_constr_plain subst = 
  Subst.subst_to_flat_subst subst 
   
let create_constr_set_plain () = {set = FSSet.empty; set_size = 0}

let add_constr_plain constr_set_plain subst = 
  {
   set = FSSet.add (create_constr_plain subst) constr_set_plain.set;
   set_size = constr_set_plain.set_size + 1;
 }
       
exception Constr_sat
let rec extend_env_norm env lterm rterm =
  match lterm with
  |Term.Fun(l_sym,l_args,_) ->
      ( 
	match rterm with 
	| Term.Fun(r_sym,r_args,_) -> 
	    if (l_sym == r_sym) 
	    then 
	      let f env' lt' rt' = 
		extend_env_norm env' lt' rt' in
	      Term.arg_fold_left2 f env l_args r_args
	    else raise Constr_sat
	|_-> raise Constr_sat
       )
  |Term.Var(lv,_) -> 
      try
	let ass_rterm = List.assq lv env in
	if (ass_rterm ==rterm)
	then env 
	else raise Constr_sat
      with
	Not_found -> (lv,rterm)::env
				   

let check_constr_norm subst constr = 
  let env_ref = ref [] in
  let f (x,lterm) = 
    let rterm = Subst.find x subst in
    env_ref := (extend_env_norm !env_ref lterm rterm)
  in	  
  try
    List.iter f constr;
    false	
  with  (* Not_found refers to above  SubstBound.find (bound,x) bsubst *)
  |Constr_sat ->  true
  |Not_found -> (* out_str_debug (" Constraint Check Not_found \n ");*) 
      true   
	
let check_constr_set_plain constr_set_plain subst = 
(*  let start_time = Unix.gettimeofday () in*)
  let res = 
    not( FSSet.exists 
	   (fun constr -> not (check_constr_norm subst constr)) constr_set_plain.set) in
(*  let end_time = Unix.gettimeofday () in
    Statistics.add_float_stat (end_time -. start_time) Statistics.inst_dismatching_checking_time;*)
(*  out_str_debug ("\n Constaint Check result: "^(string_of_bool res)^"\n");*)
  res

let check_and_add_plain constr_set_plain subst =
  if (check_constr_set_plain constr_set_plain subst) 
  then 
    add_constr_plain constr_set_plain subst
  else
    raise Constr_Not_Sat

(*-----------To stream/string----------------------*)

let var_term_to_stream s (v,t) =  
  Term.to_stream s t;
  s.stream_add_char '/';
  Var.to_stream s v

let to_stream_plain s constr =  
  s.stream_add_char '[';
  Lib.list_to_stream s var_term_to_stream constr ",";
  s.stream_add_char ']'

let out_plain = to_stream_plain stdout_stream

let to_string_plain = 
  to_string_fun_from_to_stream_fun 30 to_stream_plain

let to_stream_constr_set_plain s constr_set_plain = 
  Lib.list_to_stream s to_stream_plain (FSSet.elements constr_set_plain.set) "\n"

let out_constr_set_plain = to_stream_constr_set_plain stdout_stream

let to_string_constr_set_plain = 
  to_string_fun_from_to_stream_fun 30 to_stream_constr_set_plain
    
let to_flat_subst_list_constr_set_plain constr  = FSSet.elements constr.set


(*---------------------------New Dismatching Index-------------------------*)

(* a constraint set (for a clause c) is orginized as a tree                *)
(* where the length of each branch is exactly the number of different      *)
(* variables in c  which are always assumed to be ordered                  *)
(* each level (node) is labeled by the corresponding variable (v)          *)
(* and represents all substitutions in constraints on this variable (v->t) *)
(* each node hase variable part (v->(u_i, next_node))                      *)
(* and term part (v-> (top_t_symb-> (t_map: t->  next_node )))             *)
(* top_t_symb map is used to speedup the search                            *)
(* if contraints have the same prefix v_1->t_1,..,v_k->t_k... then this    *)
(* prefix will be shared                                                   *)


module VKey = 
  struct 
    type t       = var
    let  compare = Var.compare
  end
    
module VM = Map.Make (VKey)
    
module SKey = 
  struct 
    type t       = Symbol.symbol
    let  compare = Symbol.compare
  end
    
module SM = Map.Make (SKey)
    
module TKey = 
  struct 
    type t       = term
    let  compare = Term.compare
  end
    
module TM = Map.Make (TKey)
    
type constr_index = var_term list  

type constr_set_index = 
  |Node of var * value * (value SM.t)
  |Empty
and
      value  = (constr_set_index TM.t)

      

(* get substitution into an ordered list of (v,t)                        *)
(* smaller vars first                                                    *)
(* (note all constraints in a constr. set must have the same set of v's) *)

let create_constr_index subst = 
  let f v t rest = (v,t)::rest
  in
  let list = Subst.fold f subst [] in
  List.sort 
    (fun (v1,_t) (v2,_t2)-> Var.compare v1 v2)
    list

(* aux returns (insets t and reterns next_node) *)

let rec create_set_from_constr constr = 
  match constr with 
  |(v,t)::tl -> 
      let rest_node = 
	create_set_from_constr tl	  
      in
      let var_val, sym_val = 
	if (Term.is_var t) 
	then
	  ((TM.add t rest_node TM.empty), SM.empty)
	else
	  let top_symb = Term.get_top_symb t in	 
	  let term_val = TM.add t rest_node TM.empty in		
	  (TM.empty, (SM.add top_symb term_val SM.empty))
      in		         
      Node (v,var_val,sym_val)
  |[] -> Empty


let create_constr_set_index () = Empty

let rec add_constr_to_constr_set set constr = 
  match set with 
  |Empty -> 
      create_set_from_constr constr 
  |Node(v_n, var_val_old, sym_val_old) ->
      begin
	match constr with 
	| (v,t)::tl ->
	    assert (Var.equal v v_n);
	    if (Term.is_var t) 
	    then
	      let var_node_old =       
		try
		  TM.find t var_val_old
		with 
		  Not_found -> Empty
	      in
	      let var_node_new = add_constr_to_constr_set var_node_old tl in
	      let var_val_new = TM.add t var_node_new var_val_old in
	      Node(v_n, var_val_new, sym_val_old)
	    else
	      let top_symb = Term.get_top_symb t in 
	      let term_val_old = 
		try
		  SM.find top_symb sym_val_old
		with 
		  Not_found -> TM.empty
	      in
	      let term_node_old = 
		try
		  TM.find t term_val_old
		with 
		  Not_found -> Empty
	      in
	      let term_node_new = add_constr_to_constr_set term_node_old tl in
	      let term_val_new = TM.add t term_node_new term_val_old in
	      let sym_val_new = SM.add top_symb term_val_new sym_val_old in
	      Node(v_n, var_val_old, sym_val_new)
	|[] -> Empty
      end
	
let add_constr_index set subs = 
  let constr = create_constr_index subs in
  add_constr_to_constr_set set constr

(* retuns unit if "contr" satiafies the "set" of constraints*)
(* otherwise raises Constr_Not_Sat *)

(* aux *)


(* aux *)
exception Check_Fails
let rec check_term_env' env set_term t = 
  match set_term with
  |Term.Fun(l_sym,l_args,_) ->
      ( 
	match t with 
	| Term.Fun(r_sym,r_args,_) -> 
	    if (l_sym == r_sym) 
	    then 
	      let f env' lt' rt' = 
		check_term_env' env' lt' rt' in
	      Term.arg_fold_left2 f env l_args r_args
	    else raise Check_Fails
	|_-> raise Check_Fails
       )
  |Term.Var(lv,_) -> 
      try
	let ass_rterm = Subst.find lv env in
	if (ass_rterm == t)
	then env 
	else raise Check_Fails
      with
	Not_found -> Subst.add  lv t env
	    

let check_term_env env set_term t = 
  try 
    (true, (check_term_env' env set_term t))
  with 
    Check_Fails -> (false,env) 

(*------------*)


let rec check_constr_set' env set constr = 
  match constr with 
  |(v,t)::tl ->
      begin
	match set with 
	|Node(v_n, var_val, sym_val) ->
	    assert (Var.equal v v_n);
	    let check_var v_t v_node  = 
	      let set_var = Term.get_var v_t in
	      let set_val, new_env = 
		try
		  (Subst.find set_var env, env)
		with 
		  Not_found -> 
		    (t,Subst.add set_var t env) 
	      in
	      if (set_val == t) 
	      then
		check_constr_set' new_env v_node tl
	      else ()
	    in 
	    TM.iter check_var var_val;
	    if (Term.is_var t) 
	    then () (* vars cannot be matched by non-var terms*)
	    else
	      let top_sym = Term.get_top_symb t in 
	      if not (SM.mem top_sym sym_val)
	      then ()
	      else
		begin
		  let term_val = SM.find top_sym sym_val in
		  let check_term_val set_term set_node = 
		    let (succ,new_env) = check_term_env env set_term t in
		    if succ 
		    then 
		      check_constr_set' new_env set_node tl
		    else ()
		  in
		  TM.iter check_term_val term_val
		end
	|Empty -> ()
      end
  | [] -> raise Constr_Not_Sat


let check_constr_set_index set subs = 
  let constr = create_constr_index subs in
  let env = Subst.create () in
  try
    check_constr_set' env set constr;
    true
  with 
    Constr_Not_Sat -> false

(* Checks if subs satisfies constraint set and *)
(* If it does then adds subs to the constr set otherwise *)
(* raises Constr_Not_Sat *)
let check_and_add_index set subs = 
  let constr = create_constr_index subs in
  let env = Subst.create () in
  check_constr_set' env set constr;
  add_constr_to_constr_set set constr

(* not yet implemented *)
let to_stream_constr_set_index s _set =
  s.stream_add_str "\n Dismatching Index Representation to_stream is Not yet Implemented \n"
let to_string_constr_set_index _set = 
  "\n Dismatching Index Representation to_string is Not yet Implemented \n"

(*-------------------------Dynamic Representation--------------------------*)

(* Dynamic dismatching constraints: if size of the constraint set is less than index_strarts_from *)
(* then we use the plain representation else we use index version *)

(* Also we use completely plain representation when !current_options.sat_out_model = true *)
(* because to_stream_constr_set_index is not implement yet *)


let index_strarts_from = 10

(*
let _ = out_warning " dismatching index_strarts_from changed"

let index_strarts_from = 10000
*)

type ('a, 'b) mark = 
  | L of 'a 
  | I of 'b 


let plain_set_to_index_set plain_set = 
  let f constr_plain index_set = 
    let constr_index =    
(* we already sorted them in plain impl. *)
(*     List.sort 
       (fun (v1,_t) (v2,_t2)-> Var.compare v1 v2)*)
      constr_plain
    in
    add_constr_to_constr_set index_set constr_index
  in
  FSSet.fold f plain_set.set  (create_constr_set_index ()) 



    

(*---------*)
type constr_dyn = (constr_plain, constr_index) mark

type constr_set_dyn = (constr_set_plain, constr_set_index) mark

let create_constr_set_dyn () = L (create_constr_set_plain ())

let need_prepare_model () =
  (not (!current_options.sat_out_model = Model_None)) ||
  (!current_options.aig_mode && !current_options.bmc1_aig_witness_out)

let add_constr_dyn set subs = 
  match set with 
  |I(i_set) -> I(add_constr_index i_set subs)
  |L(l_set) -> 
      if l_set.set_size < index_strarts_from || (need_prepare_model ())
      then 
	L(add_constr_plain l_set subs)
      else
	let i_set = plain_set_to_index_set l_set in
	I(add_constr_index i_set subs)

let check_constr_set_dyn set subs = 
  match set with 
  |I(i_set) -> check_constr_set_index i_set subs
  |L(l_set) -> check_constr_set_plain l_set subs


let check_and_add_dyn set subs = 
  match set with 
  |I(i_set) -> I(check_and_add_index i_set subs)
  |L(l_set) -> 
      if l_set.set_size < index_strarts_from || (need_prepare_model ())
      then 
	L(check_and_add_plain l_set subs)
      else
	let i_set = plain_set_to_index_set l_set in
	I(check_and_add_index i_set subs)
	  
let to_stream_constr_set_dyn s set = 
  match set with 
  |L(l_set) ->
      to_stream_constr_set_plain s l_set
  |I (_i_set) ->
      s.stream_add_str "\n \"to_stream_constr_set_dyn\" is not defined yet\n"

let to_string_constr_set_dyn set = 
  match set with 
  |L(l_set) ->
      to_string_constr_set_plain l_set
  |I (_i_set) ->
      failwith "\n \"to_string_constr_set_dyn\" is not defined yet\n"


let to_flat_subst_list_constr_set_dyn set = 
  match set with 
  |L(l_set) -> 
      to_flat_subst_list_constr_set_plain l_set 
  |I(_i_set) ->
      failwith "\n \"to_flat_subst_set_dyn\" is not defined yet\n"



(*-----------------------Debug Representation---------------------*)


type constr_debug       = constr_plain * constr_index
type constr_set_debug   = constr_set_plain * constr_set_index


let create_constr_set_debug ()  = 
  (create_constr_set_plain (),create_constr_set_index ())

let add_constr_debug (s_plain,s_index) subs = 
  (add_constr_plain s_plain subs, add_constr_index s_index subs)

let check_constr_set_debug (s_plain,s_index) subs =
  let res_plain = check_constr_set_plain s_plain subs in
  let res_index = check_constr_set_index s_index subs in
  if (res_plain && res_index) || ((not res_plain) && (not res_index))
  then 
    res_plain
  else
    failwith "Dismatching Constraints Debug in check_constr_set_debug!!!\n"

let check_and_add_debug (s_plain,s_index) subs = 
  let res_plain, s_plain_new = 
    try 
      (true, check_and_add_plain s_plain subs)
    with 
      Constr_Not_Sat 
      -> (false, s_plain) 
  in
  let res_index, s_index_new = 
    try 
      (true, check_and_add_index s_index subs)
    with 
      Constr_Not_Sat 
      -> (false, s_index)
  in
  if (res_plain && res_index) || ((not res_plain) && (not res_index))
  then 
    if res_plain 
    then 
      (s_plain_new,s_index_new)
    else
      raise Constr_Not_Sat
  else
    failwith "Dismatching Constraints Debug in add_and_check_debug !!!\n"

let to_stream_constr_set_debug s c = ()
let to_string_constr_set_debug c = 
  "\n \"to_string_constr_set_debug\" Is not defined yet\n"



(*------------ ReComment for different implementations ---------------*)

(*--------------Definitions for Dynamic Representation----------------*)


type constr              = constr_dyn
type constr_set          = constr_set_dyn
      
let create_constr_set    = create_constr_set_dyn
let add_constr           =  add_constr_dyn
(*  Statistics.run_and_time Statistics.inst_dismatching_checking_time add_constr_dyn *)
let check_constr_set     = check_constr_set_dyn
let check_and_add        =  check_and_add_dyn
(*  Statistics.run_and_time Statistics.inst_dismatching_checking_time check_and_add_dyn *)
    
let to_stream_constr_set = to_stream_constr_set_dyn
let to_string_constr_set = to_string_constr_set_dyn

let to_flat_subst_list_constr_set = to_flat_subst_list_constr_set_dyn


(*-------------Definitions for Debug representation--------------*)


(*
  let _ = out_str "\n\n!!!!!!!!! Dismatching DEBUG !!!!!!!\n\n"

  type constr       = constr_debug
  type constr_set   = constr_set_debug

  let create_constr_set    = create_constr_set_debug
  let add_constr           = add_constr_debug
  let check_constr_set     = check_constr_set_debug
  let check_and_add        = check_and_add_debug

  let to_stream_constr_set = to_stream_constr_set_debug  
  let to_string_constr_set = to_string_constr_set_debug  
*)

(* TODO: define: let to_flat_subst_list_constr_set = to_flat_subst_list_constr_set_plain *)

(*-------------Definitions for Index representation--------------*)
(*
  type constr       = constr_index
  type constr_set   = constr_set_index

  let create_constr_set        = create_constr_set_index   
  let add_constr               = add_constr_index          
  let check_constr_set         = check_constr_set_index    
  let check_and_add            = check_and_add_index

  let to_stream_constr_set = to_stream_constr_set_index  
  let to_string_constr_set = to_string_constr_set_index  
 *)

(*-------------Definitions for List representation--------------*)

(*
  type constr       = constr_plain
  type constr_set   = constr_set_plain

  let create_constr_set    = create_constr_set_plain
  let add_constr           = add_constr_plain
  let check_constr_set     = check_constr_set_plain
  let check_and_add        = check_and_add_plain

  let to_stream_constr_set = to_stream_constr_set_plain
  let to_string_constr_set = to_string_constr_set_plain
 *)

(*-------------------------------*)




    
(********************new version based on vectIndex *********)
(********************simple feature index*******************)
(* Works but commented for the moment
   

   
   let get_feature_list constr = 
   let (feature_1,feature_2) = 
   let f (num_of_symb_rest,num_of_non_var_rest) (var,term)  = 
   let num_of_symb  = (Term.get_num_of_symb term) + num_of_symb_rest in
   let num_non_var = 
   if (Term.is_var term) then  num_of_non_var_rest
   else num_of_non_var_rest + 1 in
   (num_of_symb,num_non_var)
   in	 
   List.fold_left f (0,0) constr
   in
   [feature_1;feature_2]
   
(* get feature list from subst*)

   let get_subst_feature_list subst = 
   let (feature_1,feature_2) = 
   let f var term  (num_of_symb_rest,num_of_non_var_rest) =
   let num_of_symb  = (Term.get_num_of_symb term) + num_of_symb_rest in
   let num_non_var = 
   if (Term.is_var term) then  num_of_non_var_rest
   else num_of_non_var_rest + 1 in 
   (num_of_symb,num_non_var)
   in	 
   Subst.fold f subst (0,0) 
   in
   [feature_1;feature_2]
   
   module Feature = 
   struct  
   type t = int 
   let  compare = compare
   end

   module VIndexM = VectorIndex.Make (Feature)
   type constr_list_feature = ((constr_flat_list list ) VIndexM.index) ref


   let create_constr_feature_list () =  ref (VIndexM.create ()) 

   let add_constr_feature_list constr_list_feature_ref constr  = 
   let flat_constr = create_constr_flat_list constr in
   let  feature_list = get_feature_list flat_constr in
   let elem_ref = VIndexM.add feature_list constr_list_feature_ref in
   match !elem_ref with 
   |Elem(elem) -> 
   elem_ref:=Elem(flat_constr::elem)
   |Empty_Elem -> elem_ref:= Elem([flat_constr])
   
   exception Constr_unsat
   let check_constr_feature_list subst constr_list_feature_ref =
   (*out_str_debug ("------\n Constraint Check Features: \n");*)
   let subst_feat_list = get_subst_feature_list subst in
   let apply constr_list = 
(* debug *)
(*    let constr_list_str = (constr_list_to_string constr_list)^"\n" in
      let subst_str = (Subst.to_string subst) ^"\n" in*)
   (*out_str_debug 
     ("\n------------------------\n"
     ^"\n Constraint list:  "^constr_list_str
     ^"Subst to Check: "^subst_str);*)
   if not (check_constr_set_list constr_list subst)
   then 
   ((*out_str_debug ("\n Constr is UNSAT\n");*)
   raise Constr_unsat)
   else 
   ((*out_str_debug ("\n Constr is SAT\n");*)
   None)
   in
   try 
   let _=VIndexM.findf_leq apply subst_feat_list constr_list_feature_ref in
   true 
   with 
   Constr_unsat -> false

 *)

(*--------------------Commented----------------------------------*)
(*

(* we need the bound of the current clause since bsubst can contain *)
(* bounds from other clauses *)
(* don't apply resulting subst to the clause since vars are renamed only *)
(* if they in bsubst *)
  let create_constr term_db_ref  bound bsubst = 
  let next_var_ref    = ref (Var.get_first_var ()) and
  renaming_list_ref     = ref [] in
  let add (bv,var) bterm rest = 
  if bv = bound 
  then
  let reduced_term =  
  SubstBound.apply_bsubst_bterm'  
  renaming_list_ref next_var_ref term_db_ref bsubst bterm 
  in
  (var,reduced_term)::rest
  else rest
  in
  SubstBound.fold add bsubst [] 
  
  let add_constr_list constr_list constr = 
  constr::constr_list
  
  exception Not_equal

  let rec eq_bterm_subst' bsubst curr_val (bt,t) (bs,s) =
  match t with
  |Term.Fun(t_sym,t_args,_) ->
  ( 
  match s with 
  |Term.Fun(s_sym,s_args,_) -> 
  if (t_sym == s_sym) 
  then 
  Term.arg_fold_left2 
  (fun curr_val t' s' 
  -> eq_bterm_subst' bsubst curr_val (bt,t') (bs,s')) 
  true t_args s_args
  else      
  raise Not_equal
  |Term.Var(vs,_) -> 
  (try 
  let new_bs = SubstBound.find (bs,vs) bsubst in
  eq_bterm_subst' bsubst curr_val (bt,t) new_bs
  with
  Not_found -> 
  raise Not_equal
  )
  )
  |Term.Var(vt,_) ->
  ( 	
  match s with 	
  |Term.Var(vs,_) ->
  if (bt = bs) && (vt == vs) 
  then true
  else
  (try 
  let new_bt = SubstBound.find (bt,vt) bsubst in
  eq_bterm_subst' bsubst curr_val new_bt (bs,s)
  with 
  Not_found -> 
  (try 
  let new_bs = SubstBound.find (bs,vs) bsubst in
  eq_bterm_subst' bsubst curr_val (bt,t) new_bs
  with
  Not_found -> 
  raise Not_equal
  )
  )
  |_ ->  eq_bterm_subst' bsubst curr_val (bs,s) (bt,t)
  )

  let eq_bterm_subst bsubst bt bs =
  try
  eq_bterm_subst' bsubst true bt bs
  with
  Not_equal -> false

  exception Constr_sat
(* env contains current mapping of (x,bterm) *)
(* *)
  let rec extend_env bsubst env lterm (b,rterm)   =
  match lterm with
  |Term.Fun(l_sym,l_args,_) ->
  ( 
  match rterm with 
  | Term.Fun(r_sym,r_args,_) -> 
  if (Symbol.equal l_sym r_sym) 
  then 
  let f env' lt' rt' = 
  extend_env bsubst env' lt' (b,rt') in
  Term.arg_fold_left2 f env l_args r_args
  else raise Constr_sat
  |_-> raise Constr_sat
  )
  |Term.Var(lv,_) -> 
  try
  let ass_rterm = List.assq lv env in
  if (eq_bterm_subst bsubst ass_rterm  (b,rterm))
  then env 
  else raise Constr_sat
  with
  Not_found -> (lv,(b,rterm))::env


  let check_constr bound bsubst constr = 
  let env_ref = ref [] in
  let f (x,lterm) = 
  let brterm = SubstBound.find (bound,x) bsubst in
  env_ref := (extend_env bsubst !env_ref lterm brterm)
  in	  
  try
  List.iter f constr;
  false	
  with  (* Not_found refers to above  SubstBound.find (bound,x) bsubst *)
  | Constr_sat ->  true
  |Not_found -> (* out_str_debug (" Constaint Check Not_found \n ");*) true   
  

  let check_constr_list bound bsubst constr_list  = 
  let res = 
  not( List.exists (fun constr -> not (check_constr bound bsubst constr)) constr_list) in
(*  out_str_debug ("\n Constaint Check result: "^(string_of_bool res)^"\n");*)
  res

 *)
(*-------------------------------------------------------*)
