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



(* core variable splitting a la paradox with some extensions *)

open Lib
open Logic_interface
open Options
open Definitions

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
    
let module_name = "splitting_cvd"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)


module VC = Ref_cnt.Make(Var.VKey) (* variable count *)

(* TODO move to common with splitting_nvd *)
let create_new_split_atom vset = 
  let vlist = VSet.elements vset in
  let arg_types = List.map Var.get_type vlist in
  let pred_symb = 
    SymbolDB.create_new_split_symb
      symbol_db_ref
      (Symbol.create_stype arg_types Symbol.symb_bool_type)  
  in
  let args = List.map add_var_term vlist in
  let atom = add_fun_term pred_symb args in
  atom

(*---- term variable count ---*)

type tvc =  
    {
     mutable tvc_tset : TSet.t;
     mutable tvc_vset : VSet.t;
     mutable tvc_nterms : int;
     tvc_vcnt : VC.rc;
   }

let tvc_create () = 
  {
   tvc_tset = TSet.empty;
   tvc_vset = VSet.empty;
   tvc_nterms = 0;
   tvc_vcnt = VC.create ();
 }

let tvc_mem_term tvc t = TSet.mem t tvc.tvc_tset
let tvc_mem_var tvc v = VSet.mem v tvc.tvc_vset

let tvc_is_empty tvc = (tvc.tvc_tset = TSet.empty)
let tvc_num_vars tvc = VC.get_num_el tvc.tvc_vcnt
let tvc_num_terms tvc = tvc.tvc_nterms


let tvc_add tvc t t_vars = 
  if (tvc_mem_term tvc t) 
  then 
    ()
  else
    begin
      tvc.tvc_tset <- TSet.add t tvc.tvc_tset;
      tvc.tvc_nterms <- tvc.tvc_nterms +1;
      if (Term.is_ground t)
      then
        ()
      else 
        begin
          tvc.tvc_vset <- VSet.union t_vars tvc.tvc_vset;
          VSet.iter (fun v -> ignore (VC.add_cnt tvc.tvc_vcnt v)) t_vars 
        end
    end
      
  
let tvc_remove tvc t t_vars = 
  if (not (tvc_mem_term tvc t))
  then 
    ()
  else
    begin
      tvc.tvc_tset <- TSet.remove t tvc.tvc_tset;
      tvc.tvc_nterms <- tvc.tvc_nterms - 1;
      if (Term.is_ground t)
      then
        ()
      else 
        begin
          VSet.iter 
            (fun v ->  
              let new_cnt = (VC.remove_cnt tvc.tvc_vcnt v) in
              if (new_cnt = 0) 
              then 
                (tvc.tvc_vset <- VSet.remove v tvc.tvc_vset)
              else ()
            ) t_vars
        end
    end



(* var split environment *)
type vse = 
    {
     mutable vse_var_map       : tvc VMap.t;
     mutable vse_tvc           : tvc; (* global tvc *)
     mutable vse_lit_vars      : VSet.t TMap.t 
      (* lits -> lit_vars; if lit is ground it is not in vse_lit_vars but in tvc  *)
   }

let vse_create () = 
  {
   vse_var_map = VMap.empty;
   vse_tvc = tvc_create ();
   vse_lit_vars = TMap.empty
 }

let vse_mem_lit vse lit = tvc_mem_term vse.vse_tvc lit

let vse_add_lit vse lit = 
  if (vse_mem_lit vse lit) 
  then 
    ()
  else
    begin     
      let lit_vars = Term.add_var_set VSet.empty lit in      
      tvc_add vse.vse_tvc lit lit_vars;
      if (not (Term.is_ground lit))
      then 
        begin
          vse.vse_lit_vars <- TMap.add lit lit_vars vse.vse_lit_vars;
          let fill_v v = 
            let v_tvc = 
              try 
                VMap.find v vse.vse_var_map
              with 
                Not_found -> 
                  let new_tvc = tvc_create () in
                  vse.vse_var_map <- VMap.add v new_tvc vse.vse_var_map;
                  new_tvc
            in
            tvc_add v_tvc lit lit_vars
          in
          VSet.iter fill_v lit_vars
        end
      else 
        ()
    end

let vse_remove_lit vse lit = 
  if (not (vse_mem_lit vse lit))
  then 
    ()
  else
    begin           
      let lit_vars = 
        try
          TMap.find lit vse.vse_lit_vars 
        with 
          Not_found -> 
            (assert (Term.is_ground lit);
             VSet.empty
            )
      in
      tvc_remove vse.vse_tvc lit lit_vars;
      if (not (Term.is_ground lit))
      then 
        begin
          vse.vse_lit_vars <- TMap.remove lit vse.vse_lit_vars;
          let fill_v v = 
              try 
                let v_tvc = VMap.find v vse.vse_var_map in
              
                tvc_remove v_tvc lit lit_vars;
                (if (tvc_is_empty v_tvc)
                then 
                  vse.vse_var_map <- VMap.remove v vse.vse_var_map;
                );
              with 
                Not_found -> ()
          in
          VSet.iter fill_v lit_vars
        end
      else
        ()
    end

(*-------------------*)
module VPQ = Priority_queue.MakePQInt(Var.VKey)

type spe = (* splitting env *)
    {
     spe_clause : clause; (* original clause *)
     mutable spe_vpq  : VPQ.t;
     mutable spe_tail : vse;
     mutable spe_head : clause list; 
   }

let spe_init clause = 
  {
   spe_clause = clause;
   spe_vpq = VPQ.create ();
   spe_tail = vse_create ();
   spe_head = [];
 }

let spe_create clause = 
  let spe = spe_init clause in 
  let lits = Clause.get_lits clause in
  List.iter (vse_add_lit spe.spe_tail) lits;
  let vse = spe.spe_tail in
(*  let vars = vse.vse_tvc.vset in *)
  let fill_var_pr v v_tvc = 
    let v_pr =  tvc_num_terms v_tvc in   
    VPQ.add spe.spe_vpq v v_pr 
  in
  VMap.iter fill_var_pr vse.vse_var_map;
  spe


(*
let finalise spe = 
  let vse = spe.spe_tail in
  let vse_tvc = vse.vse_tvc in
  let tail_lits = TSet.elements vse_tvc.tvc_tset in 
  let all_pre_clauses = 
    if  (tail_lits = []) 
    then 
      spe.spe_head
    else
      tail_lits::spe.spe_head 
  in 
  match all_pre_clauses with 
  |[_] -> [spe.spe_clause] (* there are no splits *) 
  |[] -> failwith "splitting_cvd: finalise: should not happen"
  |_-> 
      (
      dbg D_trace (lazy ("num pre_clauses: "^(string_of_int (List.length all_pre_clauses))));  
      let f rest lits = 
        let tstp_source = Clause.tstp_source_split [] [spe.spe_clause] in	 
        let sp_clause = create_clause tstp_source lits in 
        Clause.inherit_conjecture spe.spe_clause sp_clause;
        dbg D_trace (lazy ("new clause: "^(Clause.to_string sp_clause)));  
        sp_clause::rest
      in
      let splitting_clauses = List.fold_left f [] all_pre_clauses in 
      splitting_clauses
      )
*)

let finalise spe = 
  let vse = spe.spe_tail in
  let vse_tvc = vse.vse_tvc in
  let tail_lits = TSet.elements vse_tvc.tvc_tset in 
  let all_clauses = 
    if  (tail_lits = []) 
    then 
      spe.spe_head
    else
      (let tail_clause = create_def_reduced_clause ~parent:spe.spe_clause tail_lits in
      dbg D_trace (lazy ("tail_clause: "^(Clause.to_string tail_clause)));
      tail_clause::spe.spe_head 
      )
  in 
  match all_clauses with 
  |[_] -> [spe.spe_clause] (* there are no splits; return old clause *) 
  |[] -> failwith "splitting_cvd: finalise: should not happen"
  |_-> all_clauses
      

let update_pr spe vset = 
  let vse = spe.spe_tail in
  let f v = 
    try
      let v_tvc = VMap.find v vse.vse_var_map in (* can raise Not_found *) 
      let v_pr =  tvc_num_terms v_tvc in   
      VPQ.update_pr spe.spe_vpq v v_pr 
    with 
      Not_found -> 
        (
         VPQ.remove spe.spe_vpq v
        )
  in
  VSet.iter f vset

(* termination: each var from vpq considered at most once *)
let rec process def_env spe = 
  let vse = spe.spe_tail in
  let vse_tvc = vse.vse_tvc in
  try 
    let (pr,v) = VPQ.min_el_rm spe.spe_vpq in (* can raise Not_found *)  
    let num_tail_lits =  (tvc_num_terms vse.vse_tvc) in
    dbg D_trace (lazy ("v: "^(Var.to_string v)
                       ^" pr: "^(string_of_int pr)
                       ^" num_tail_lits: "^(string_of_int num_tail_lits)));    
    if (pr = num_tail_lits) (* v occurs in all terms; since it is minimal all other vars also occur in all terms *)
    then
      finalise spe
    else
      begin
        try
          let v_tvc = VMap.find v vse.vse_var_map in (* can raise Not_found *)   
          let v_tvc_vars = v_tvc.tvc_vset in 
          let v_tvc_lits = v_tvc.tvc_tset in 
          let head_lits = 
            if !current_options.splitting_cvd_svl
            then 
              let subvar_lits =
                let f lit vset rest = 
                  if (VSet.subset vset v_tvc_vars) 
                  then 
                    TSet.add lit rest
                  else
                    rest
                in
                TMap.fold f vse.vse_lit_vars TSet.empty
              in
              TSet.union v_tvc_lits subvar_lits
            else
              v_tvc_lits
          in
          dbg D_trace (lazy ("head_lits: "^(Term.term_list_to_string (TSet.elements head_lits))));

(* order of statemets below is important *)

          TSet.iter (vse_remove_lit vse) head_lits;

          if (VSet.subset v_tvc_vars vse_tvc.tvc_vset)  || (VSet.subset vse_tvc.tvc_vset v_tvc_vars)
       (* do not peform split if vars collected lits is a subset of vars of the remaining lits *)
          then
            begin
              TSet.iter (vse_add_lit vse) head_lits; (* add lits back and try next var from vpq *)
              process def_env spe               
            end
          else
            begin
              if (tvc_is_empty vse_tvc) (* tail is empty *)
              then 
                (
                 let head_clause = create_def_reduced_clause ~parent:spe.spe_clause (TSet.elements head_lits) in
                 dbg D_trace (lazy ("head_clause: "^(Clause.to_string head_clause)));
                 spe.spe_head <- head_clause::spe.spe_head;
                 finalise spe 
                )
              else
                begin
                  let split_vars = (* v_tvc_vars*)  VSet.inter v_tvc_vars vse_tvc.tvc_vset in
                  dbg_env D_trace
                    (fun () -> 
                      if (not (VSet.equal v_tvc_vars vse_tvc.tvc_vset))
                      then
                      dbg  D_trace (lazy 
                                      (":split_vars diff: "
                                       ^"v_tvc_vars: "^(Var.var_list_to_string (VSet.elements v_tvc_vars)) 
                                       ^" vse_tvc.tvc_vset: "^(Var.var_list_to_string (VSet.elements vse_tvc.tvc_vset))));
                    );

                  let (split_atom, split_clause) = 
                    add_def def_env ~parent:spe.spe_clause (VSet.elements split_vars) (TSet.elements head_lits) in
                  dbg  D_trace (lazy ("split_atom: "^(Term.to_string split_atom)));
                  dbg D_trace (lazy ("split_clause: "^(Clause.to_string split_clause)));
                  
                  vse_add_lit vse split_atom;          
                  update_pr spe v_tvc_vars; 
                  spe.spe_head <- split_clause::spe.spe_head;
                  process def_env spe

(*                  

                  let split_atom = create_new_split_atom split_vars in 
                  dbg  D_trace (lazy ("split_atom: "^(Term.to_string split_atom)));
                  let neg_split_atom = add_neg_atom split_atom in              
                  let head_lits_split = neg_split_atom::(TSet.elements head_lits) in 
                  vse_add_lit vse split_atom;          

                  update_pr spe v_tvc_vars; 
                  spe.spe_head <- head_lits_split::spe.spe_head;
                  process def_env spe
*)
                end
            end
        with (* v isn not in  vse.vse_var_map *)
          Not_found -> process def_env spe
      end
  with 
    Not_found ->  (* spe.spe_vpq is empty *)
      (
       assert (VPQ.is_empty spe.spe_vpq);
       finalise spe
      )


(* split once; split_clauses can still be splittable *)

let cvd_split_clause_once def_env clause = 
  check_empty_clause clause;
  dbg D_trace (lazy ("--------------\n"));
  dbg D_trace (lazy ("input:\n "^(Clause.to_string clause)));
  let spe = spe_create clause in
  let split_clauses = process def_env spe in 
    dbg D_trace (lazy ("splitting clauses:\n "^(Clause.clause_list_to_string split_clauses)));
  split_clauses

(* full split *)
let rec cvd_split_clause_list' def_env result to_split = 
  match to_split with 
  | [] -> result 
  | clause::tl ->       
      let split_cl = cvd_split_clause_once def_env clause in
      (match split_cl with 
      |[c] -> 
          (
           dbg_env D_trace
             (fun () -> 
               (if (not (clause == c)) then 
                 (dbg D_trace (lazy ("cvd_split_clause_list': single clauses different:"));
                  dbg D_trace (lazy ("clause:"^Clause.to_string clause));
                  dbg D_trace (lazy ("c     :"^Clause.to_string c));
                 )
               )
             );                    
           assert (clause == c);
           let new_result = c::result in 
           cvd_split_clause_list' def_env new_result tl
          )
      |_ -> 
          let new_to_split = split_cl@tl in
          cvd_split_clause_list' def_env result new_to_split
      )

let cvd_split_clause_list def_env clause_list = 
  cvd_split_clause_list' def_env [] clause_list

(*
let rec cvd_split_clause_list clause_list = 
  if (clause_list = []) 
  then 
    clause_list 
  else
    begin
    let f rest clause = 
      check_empty_clause clause;
      dbg D_trace (lazy ("--------------\n"));
      dbg D_trace (lazy ("input:\n "^(Clause.to_string clause)));
      let spe = spe_create clause in
      let split_clauses_init = process spe in 
      let split_clauses = (* splitting can be repeated: applied again to the new split clauses *)
(*
        if (not ((List.length split_clauses_init) = (List.length clause_list))) (* some new splits *)
        then
          cvd_split_clause_list split_clauses_init 
        else (* no new splits *)
*)
          split_clauses_init
      in
      dbg D_trace (lazy ("splitting clauses:\n "^(Clause.clause_list_to_string split_clauses)));
      split_clauses@rest
    in
    List.fold_left f [] clause_list 
    end
*)
