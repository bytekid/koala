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
  | D_init
  | D_lemmas
  | D_def_atom

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_init -> "init"
  | D_lemmas -> "lemmas"
  | D_def_atom  -> "def_atom"

let dbg_groups =
  [
   (* D_trace; *)
   D_init;
   D_lemmas;
   D_def_atom;
 ]

let module_name = "lemma_lifting"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


type lm_input = 
  {
   lm_input_clauses : clause list; (* a ground set of clauses *)
   lm_is_ignore_pred : (symbol-> bool); (* ignore literals with preds in this set *)
   lm_is_ignore_type : (symbol -> bool); (* do not lift constants  with this type *)
}
  
type lm_state = 
    {
     lm_input : lm_input;
     lm_unit_clauses : clause list; (* unit clauses after removing literals with ignre preds *)
     lm_non_unit_clauses : clause list;
     mutable lm_def_atom_list : lit list;       (* definition lit set for common lemma *)
     mutable lm_ground_lemmas : clause list; 
     mutable lm_lifted_lemmas : clause list; (* a non-ground lemma obtained from lifting lm_ground_lemma *)
     mutable lm_def_clauses_map : clause TMap.t; (* def -> clause *)
   } 

(*

 lm_input_clauses = p(\bar{a1}) \/....\/p(\bar{an}), ..., q(\bar{b1}) \/....\/q(\bar{bn})

|= 
   ~p(\bar{a1}) & .. &~p(\bar{an})\/
   ~q(\bar{b1}) &....&~q(\bar{bn}) 

1. split

comon lemma ~d1(\bra{a1,..,an}) \/~d2(\bar{b1,..,bn})

-----
indiv. lemma  

 d1(\bar{a1,..,an}) \/  ~p(\bar{a1})
 
            .....

 d1(\bar{a1,..,an}) \/  ~p(\bar{an})

--
d2(\bar{b1,..,bn})\/ ~q(\bar{b1})
           .....
d2(\bar{b1,..,bn})\/ ~q(\bar{bn})

*)

let is_ignore_lit lm_input lit = 
(*  SSet.mem  (Term.lit_get_top_symb lit) lm_input.lm_ignore_preds*)
  lm_input.lm_is_ignore_pred (Term.lit_get_top_symb lit)

let get_non_ignore_lits lm_input lit_list = 
  let (_ignore, non_ignore) = List.partition (is_ignore_lit lm_input) lit_list in 
  non_ignore

(* introduce splitting definitions if clause longer than one *)

let init_lm_state lm_input = 
(* we assert that all input clauses are ground *)
  dbg_env D_init
    (fun () -> 
      let f c = 
	if (not (Clause.is_ground c)) 
	then 
	 (dbg D_init (lazy ("not ground: "^(Clause.to_string c))))
	else ()
      in
      List.iter f lm_input.lm_input_clauses;
    );

  assert((List.for_all Clause.is_ground  lm_input.lm_input_clauses));
  
  let (lm_unit_clauses, lm_non_unit_clauses) = 
    let f c = 
      let non_ignore_lits = (get_non_ignore_lits lm_input (Clause.get_lits c)) in
      (List.length non_ignore_lits) = 1 
    in
    List.partition f lm_input.lm_input_clauses
  in
 
  let lm_state = 
    {
     lm_input = lm_input; 
     lm_unit_clauses = lm_unit_clauses;
     lm_non_unit_clauses = lm_non_unit_clauses;

     lm_def_atom_list = [];
  
     lm_ground_lemmas = []; 

     lm_lifted_lemmas = [];

     lm_def_clauses_map = TMap.empty; 
    
   }
  in
  lm_state


let get_all_lifting_constants_term lm_input const_set t = 
  let f rest_const_set t = 
    (* assume that t is ground so it can not be a var *)
    let top_symb =  (Symbol.get_val_type_def (Term.get_top_symb t)) in
    if (Term.is_constant t)
	&& 
      (
       not (lm_input.lm_is_ignore_type top_symb)
      ) 
    then
      TSet.add t rest_const_set 
    else 
      rest_const_set
  in 
  Term.fold_subterms f const_set t 


let get_all_constants_lit_list lm_input const_set lit_list = 
  List.fold_left (get_all_lifting_constants_term lm_input) const_set lit_list 


let get_all_constants_clause lm_input const_set c = 
  get_all_constants_lit_list lm_input const_set (Clause.get_lits c)


let create_def_atom const_set = 
  let arg_const_list = TSet.elements const_set in 
  let arg_types = List.map Term.get_term_type arg_const_list in
  let def_symb_type = create_stype arg_types Symbol.symb_bool_type in  
  let def_symb = SymbolDB.create_new_split_symb symbol_db_ref def_symb_type in 
  let def_atom = add_fun_term def_symb arg_const_list in
  def_atom


(*------------------------------*)
let fill_ground_lemmas lm_state = 
  let lm_input = lm_state.lm_input in  
  let f c = 
    
    let const_set = get_all_constants_clause lm_input TSet.empty c in     
    let def_atom = create_def_atom const_set in
    
    dbg_env D_def_atom 
      (fun () -> 
	
	dbg D_def_atom 
	  (lazy (Clause.to_string c));

	dbg D_def_atom  (lazy "");

	dbg D_def_atom
	  (lazy (" consts: "^(Term.term_list_to_string (TSet.elements const_set))));

	dbg D_def_atom
	  (lazy (" atom: "^(Term.to_string def_atom)));
      );
(* common lemma contribution *)
    lm_state.lm_def_atom_list  <- def_atom :: lm_state.lm_def_atom_list;
    let c_lits = get_non_ignore_lits lm_input (Clause.get_lits c) in 
    
(* add lemma def_atom \/ L for each L \in c *)
    let g l = 
      let compl_l = add_compl_lit l in 
      let def_lemma_lits = [def_atom; compl_l] in
      (* record as splitting/change to lemma splitting *)
      let tstp_source = Clause.tstp_source_split [def_atom] [c] in
      let def_lemma = create_clause tstp_source def_lemma_lits in
      lm_state.lm_ground_lemmas <- def_lemma::lm_state.lm_ground_lemmas;
    in
    List.iter g c_lits;
  in

(* apply to non-unit clauses only *)
  List.iter f lm_state.lm_non_unit_clauses;
  
(* common lemma *)
  let non_ignore_unit_lits = 
    let f lit_list clause = 
      let lit = 
	  match (get_non_ignore_lits lm_input (Clause.get_lits clause)) with 
	  |[lit] -> lit 
	  |_ -> failwith "not a unit (non-ignore) lits"
      in
      (lit::lit_list)
    in
    List.fold_left f [] lm_state.lm_unit_clauses 
  in
  let c_lemma_lits = 
    (List.map add_compl_lit (non_ignore_unit_lits@lm_state.lm_def_atom_list))
  in
  (* record as splitting/change to lemma splitting *)
  let tstp_source = Clause.tstp_source_split 
      c_lemma_lits
      (lm_state.lm_unit_clauses@ 
       lm_state.lm_non_unit_clauses) in
  let common_lemma = create_clause tstp_source c_lemma_lits in 

  dbg D_lemmas (lazy ("common lemma: "^(Clause.to_string common_lemma)));
  lm_state.lm_ground_lemmas <- common_lemma::lm_state.lm_ground_lemmas
					       
    

(*-----------------*)

let fill_lifted_lemmas lm_state = 
  (* map all constants to variables of corresponding types *)
 
  let lm_input = lm_state.lm_input in
  let all_constants = 
    List.fold_left (get_all_constants_clause lm_input) TSet.empty lm_input.lm_input_clauses in
    
  let fresh_vars_env = Var.init_fresh_vars_env_away [] in
  let const_var_map = 
    let f const const_var_map = 
      let const_type = Term.get_term_type const in 
      let fresh_var = Var.get_next_fresh_var fresh_vars_env const_type in 
      let var_term = add_var_term fresh_var in
      TMap.add const var_term const_var_map 
    in
    TSet.fold f all_constants TMap.empty 
  in
  let f cl_rest c =
    let g rest gr_lit = 
      let lifted_lit = add_term_db (Term.replace_map const_var_map gr_lit) in     
      lifted_lit::rest
    in
    let lifted_lits = Clause.fold g [] c in 
    let tstp_source = Clause.tstp_source_lifting c in
    let lifted_clause = create_clause tstp_source lifted_lits in 
    lifted_clause::cl_rest 
  in
  let lifted_lemmas = List.fold_left f [] lm_state.lm_ground_lemmas in 
  lm_state.lm_lifted_lemmas <- lifted_lemmas;
  lm_state


(*--------*)  
let create_lm_state lm_input = 
  let lm_state = init_lm_state lm_input in
  fill_ground_lemmas lm_state;
  fill_lifted_lemmas lm_state  
 
(*--------*)  
let get_ground_lemmas lm_state = 
  lm_state.lm_ground_lemmas

(*-------*)

let get_lifted_lemmas lm_state = 
  lm_state.lm_lifted_lemmas
