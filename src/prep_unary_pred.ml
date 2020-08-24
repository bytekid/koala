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
    
let module_name = "prep_unary_pred"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)



(* currently for the boolean domains *)
type bool_dom =
    {
     mutable bd_true  : term;     
     mutable bd_false : term;     
     mutable bd_true_clause : clause;
     mutable bd_false_clause : clause;
     mutable bd_up : symbol;
     mutable bd_up_type : symbol;

   }

let term_is_true bd t  = bd.bd_true == t 
let term_is_false bd t = bd.bd_false == t 
let is_bd_term bd t = (bd.bd_true == t) || (bd.bd_false == t)

let term_consist_sign bd sign t = 
  (sign && (term_is_true bd t)) ||  ((not sign) && (term_is_false bd t))

(* note the meaning of compl is differnt from (not (term_consist_sign bd sign t)) *)
let term_is_compl_sign bd sign t = term_consist_sign bd (not sign) t 

let sign_to_term bd sign = if sign then bd.bd_true else bd.bd_false


exception Prep_not_applicable
 
let decomp_unary_lit lit = 
  let atom = Term.get_atom lit in 
  (match atom with 
  |Term.Fun(pred, args, _) -> 
      let arg_list = Term.arg_to_list args in 
          (match arg_list with 
          |[t] -> 
              let sign = Term.get_sign_lit lit in 
              Some(sign, pred, t)                                                 
          |_-> None
          )
  |_-> failwith "should be non-var term"
  )

let decomp_unit_clause c = 
  let lits = Clause.get_lits c in 
  match lits with 
  |[lit] -> decomp_unary_lit lit
  | _ -> None 


(* list of Some(sign, atom, t) *)
let collect_unary clause_list = 
  let f rest c = 
    let dc = (decomp_unit_clause c) in
    if ((decomp_unit_clause c) = None)
    then
      rest
    else
      (dc,c)::rest
  in
  List.fold_left f [] clause_list

let get_bd clauses  = 
  let ud_list = collect_unary clauses in 
  match ud_list with 
  |[(Some(true, upred_1, t_const),t_uc); (Some(false, upred_2, f_const), f_uc)] 
  |[(Some(false, upred_1, f_const),f_uc); (Some(true, upred_2, t_const),t_uc) ]  when upred_1 == upred_2 

    ->
      if ((Term.is_constant t_const) && (Term.is_constant f_const))
      then
        (  
           let t_f_type = Term.get_term_type t_const in 
           {
            bd_true = t_const;
            bd_false = f_const;
            bd_true_clause = t_uc;
            bd_false_clause = f_uc;
            bd_up = upred_1;
            bd_up_type = t_f_type;      
          }
          )
      else
        raise Prep_not_applicable

  |_-> raise Prep_not_applicable


(* check that this prep is applicable to lit/clause *)            
let check_lit bd lit = 
  let atom = Term.get_atom lit in
    if (Term.is_epr_lit atom) 
    then
      let args = Term.arg_to_list (Term.get_args atom) in
      let f t = 
        if ((is_bd_term bd t) || (Term.is_var t)) 
        then ()
        else
          raise Prep_not_applicable
      in
      List.iter f args
    else
      raise Prep_not_applicable

let check_clause bd clause = 
  let lits = Clause.get_lits clause in 
  List.iter (check_lit bd) lits

exception Clause_eliminated

let process_clause bd c = 
  dbg D_trace (lazy (""));
  dbg D_trace (lazy (" process_clause: "^(Clause.to_string c)));
  if (Clause.is_epr c)
  then
    let f (subst, rem_lits) lit = 
      match (decomp_unary_lit lit) with 
      |Some(sign, upred, term) when (upred == bd.bd_up) && (term_consist_sign bd sign term) ->           
          dbg D_trace (lazy (" Clause_eliminated:"));
          raise Clause_eliminated
           
      |Some(sign, upred, term) when (upred == bd.bd_up) && (term_is_compl_sign bd sign term) ->
          dbg D_trace (lazy (" lit removed: "^" lit: "^(Term.to_string lit)));
          (subst, rem_lits) (* elim literal *)
            
      |Some(sign, upred, term) when (upred == bd.bd_up) && (Term.is_var term)-> 
          let var = Term.get_var term in
          let bd_term = sign_to_term bd (not sign) in
          (try
            let new_subst = Subst.add var bd_term subst in 
            dbg D_trace (lazy (" subst: v: "^(Term.to_string term)^" : "^(Term.to_string bd_term)));
            (new_subst,rem_lits)
          with 
            Subst.Subst_var_already_def -> 
              dbg D_trace (lazy (" repeated subs: lit removed: "^(Term.to_string lit)));
              (subst,rem_lits) (* we can ignore the lit *)
          )
      |Some _ | None -> 
          (subst, lit::rem_lits)            
    in    
    let lits = Clause.get_lits c in
    let (subst, rem_lits) = List.fold_left f ((Subst.create ()),[]) lits in
    if ((List.length rem_lits) = (List.length lits)) 
    then 
      c 
    else
      let lits_subst = List.map (Subst.apply_subst_term term_db_ref subst) rem_lits in 
      let tstp_source = Clause.tstp_source_dom_res c in 
      let prep_clause = create_clause tstp_source lits_subst in 
      Statistics.incr_int_stat 1  Statistics.prep_upred;
      dbg D_trace (lazy (" before: "^(Clause.to_string c)));
      dbg D_trace (lazy ("  after: "^(Clause.to_string prep_clause)));
      prep_clause
  else
    raise Prep_not_applicable (* should not happen at this stage *)


let prep_unary_pred clauses = 
  try
    let bd = get_bd clauses in
    List.iter (check_clause bd) clauses;
    let f rest c =
      try 
        (process_clause bd c)::rest
      with 
        Clause_eliminated -> rest
    in
    let prep_clauses = List.fold_left f [] clauses in 
    bd.bd_true_clause::bd.bd_false_clause::prep_clauses (* for models adding back true/false unit clauses *)
  with 
    Prep_not_applicable -> clauses
