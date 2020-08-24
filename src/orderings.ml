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


type term = Term.term

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

	
let dbg_groups =
  [
   D_trace
 ]
    
let module_name = "orderings"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)


(* follows the interface of compare*)

(* we assume that all useful info is assigned 
   i.e. we have already put term in  term_db*)

(* simple_kbo
   weight of each sybol is 1, 
   precedence is the order in symbol_db
   also use an extension as in our paper *)

(* rewrite since got rid of var_list in terms *)
(* get_var_list is not efficient  *)

(* exception_vars is a list of vars that should be treated as minimal  
   constants, so they should participate,
   t_vars,  s_vars are association list (v,num_of_occureces)
   compare_vars checks  that num of 
   occerences in t of each nonexceptional vars 
   is greater than in s and reterns the list of new exceptional vars*)

exception T_vars_less_than_s_vars
let compare_vars exception_vars t_vars s_vars = 
  let f current_exceptions (v,num_v_in_s) = 
    if List.mem v current_exceptions 
    then current_exceptions
    else 
      try 
	let num_v_in_t = List.assoc v t_vars in 
	if num_v_in_t > num_v_in_s 
	then v::exception_vars
	else 
	  if num_v_in_t < num_v_in_s 
	  then raise T_vars_less_than_s_vars
	  else exception_vars
      with Not_found -> raise T_vars_less_than_s_vars
  in
  List.fold_left f exception_vars s_vars

(* returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if these are not the case*)    

(*-----------------------------Commented
  old KBO works but not efficient on the other hand more restrictive
(* uncomment minimal constant when it will be defined*)
  let rec general_kbo' 
  get_weight compare_precedence (*minimal_constant*) exception_vars t s = 
  try 
  let new_exception_vars = 
  compare_vars exception_vars 
  (Term.get_var_list t) (Term.get_var_list s) in    
  let weight_cmp = compare (get_weight t) (get_weight s) in
  if weight_cmp > cequal 
  then cequal+1
  else
  if weight_cmp = cequal 
  then
  (match (t,s) with 
  |(Term.Fun(t_sym,t_args,_),Term.Fun(s_sym,s_args,_)) -> 
  let sym_cmp = compare_precedence t_sym s_sym in
  if sym_cmp > 0 then cequal+1
  else 
  if sym_cmp = cequal 
  then  
  list_compare_lex 
  (general_kbo' get_weight compare_precedence new_exception_vars) 
  (Term.arg_to_list t_args) (Term.arg_to_list s_args) 
  else cequal-1 
  |(Term.Fun(_,_,_),Term.Var(_,_)) -> cequal+1 
  (* note that the var on the left occurs in the right *)
  |(Term.Var(_,_), Term.Var(_,_))  -> cequal

  |(Term.Var(_,_), Term.Fun(_,_,_)) -> cequal-1
(* uncomment when minimal constant will be defined

   |(Term.Var(t_v,_), Term.Fun(s_sym,_,_)) ->
   if (Symbol.compare s_sym minimal_constant)=0 
   then cequal 
   else cequal-1
 *)
  )
  else cequal-1
  with 
  T_vars_less_than_s_vars -> cequal-1 
  
 *)



let rec general_kbo' 
    get_weight compare_precedence (*minimal_constant*) exception_vars t s = 
  let weight_cmp = compare (get_weight t) (get_weight s) in
  if 
    (weight_cmp < cequal)  
(*|| 
  ((Term.get_num_of_var t) < (Term.get_num_of_var s))*)
  then cequal-1   
  else
    try 
      let new_exception_vars = 
	compare_vars exception_vars 
	  (Term.get_var_ass_list t) (Term.get_var_ass_list s) in   	          
      if weight_cmp > cequal 
      then cequal+1 
      else
	(* we have weight_cmp = cequal *)
	(match (t,s) with 
	|(Term.Fun(t_sym,t_args,_),Term.Fun(s_sym,s_args,_)) -> 
	    let sym_cmp = compare_precedence t_sym s_sym in
	    if sym_cmp > 0 then cequal+1
	    else 
	      if sym_cmp = cequal 
	      then
		list_compare_lex 
		  (general_kbo' get_weight compare_precedence new_exception_vars) 
		  (Term.arg_to_list t_args) (Term.arg_to_list s_args) 
              else cequal-1 
	|(Term.Fun(_,_,_),Term.Var(_,_)) -> cequal+1 
	      (* if (Term.var_in v_s t)
		 then cequal+1 
		 else cequal-1*)
	      
	|(Term.Var(_,_), Term.Var(_,_))  ->  cequal
(*	    if (Var.equal v_t v_s) 
  then cequal
  else cequal-1
 *)
	      
	|(Term.Var(_,_), Term.Fun(_,_,_)) -> cequal-1
(* uncomment when minimal constant will be defined
   
   |(Term.Var(t_v,_), Term.Fun(s_sym,_,_)) ->
   if (Symbol.compare s_sym minimal_constant)=0 
   then cequal 
   else cequal-1
 *)
	)
    with 
      T_vars_less_than_s_vars -> cequal-1 
	  

let general_kbo get_weight compare_precedence t s = 
  general_kbo' get_weight compare_precedence [] t s


let cmp_arity s1 s2 = 
  try
    Pervasives.compare (Symbol.get_arity s1) (Symbol.get_arity s2) 
  with 
    Symbol.Arity_undef -> 0 

let symb_precendence =
  lex_combination [cmp_arity; Symbol.compare]
    

let simple_kbo' = 
  general_kbo Term.get_num_of_symb symb_precendence

let cmp_top_symb symb_precendence t1 t2 = symb_precendence (Term.get_top_symb t1) (Term.get_top_symb t2) 

(* spltting literals must be smaller than any other; otherwise incomplete (sat in place of unsat) *)
(* cmp_top_symb: unlike normal KBO compare first predicates *)
let simple_kbo_split = 
  let cmp_lex_fun =
    lex_combination [(compose_sign false Term.cmp_split); (* (cmp_top_symb symb_precendence); *) simple_kbo'] 
  in
  cmp_lex_fun

(* cmp_top_symb: unlike normal KBO compare first predicates *)
let simple_kbo_split_top = 
  let cmp_lex_fun =
    lex_combination [(compose_sign false Term.cmp_split);  (cmp_top_symb symb_precendence); simple_kbo'] 
  in
  cmp_lex_fun


let simple_kbo_atom = simple_kbo_split

(*let simple_kbo = simple_kbo_split_top *)

let cmp_lit cmp l1 l2 = 
  let a1 = Term.get_atom l1 in
  let a2 = Term.get_atom l2 in
  if (a1 == a2)
  then -(Term.cmp_sign l1 l2)
  else cmp a1 a2 
      
  
let simple_kbo = cmp_lit simple_kbo_atom

let simple_kbo_pred = cmp_lit simple_kbo_split_top

(*
  let ()= out_str "!!!!Debug orderigns \n"
  let simple_kbo t s =  -1
 *)

(*
let simple_kbo_lit l1 l2 =
  
  let a1 = Term.get_atom l1 in
  let a2 = Term.get_atom l2 in
  let res =
    if (a1 == a2)
    then -(Term.cmp_sign l1 l2)
    else simple_kbo a1 a2 
  in
  dbg D_trace (lazy ("kbo: cmp "^(Term.to_string l1)^" "^(Term.to_string l2)^" "
                     ^(string_of_int res)));
  res
*)
