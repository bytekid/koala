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
open Logic_interface 
(* open Qbf_env*)
open PredElim
open Prop_fof

(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_pred_elim
  | D_final 
  | D_gs
  | D_time
  | D_q_res
  | D_def_discovery
  
let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_pred_elim -> "pred_elim"
  | D_final -> "final"
  | D_gs -> "gs"
  | D_time -> "time"
  | D_q_res -> "q_res"
  | D_def_discovery -> "def_discovery"

let dbg_groups =
  [
   D_trace;  
   D_pred_elim; 
(*   D_final; *)
   (* D_gs;  *)
   (* D_time; *)
   D_q_res;
   D_def_discovery;
 ]

let module_name = "qbf_preprocess"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


(* can not open both prop modules and Logic_interface since many name clashes *)
module PV  = Prop_var
module PVE = Prop_env
module QE  = Qbf_env 

module PVMap = PV.VMap
module PVSet = PV.VSet

module PLMap = PV.LMap
module PLSet = PV.LSet

type pvar = PV.var
type plit = PV.lit
type qbf_cnf = Qbf_env.qbf_cnf

let bool_type = Symbol.symb_bool_type
let prop_type = Symbol.symb_default_type

(* ------ time_outs ------ *)
exception QBF_prep_timeout

let prep_remaining_time () = 
    ((!current_options.time_out_real*. !current_options.time_out_prep_mult) -. (iprover_running_time ())) 


let prep_qbf_remaining_time () = 
   (((!current_options.time_out_real *. !current_options.time_out_prep_mult)) -. (iprover_running_time ())) 


let prop_subs_time_limit () = (prep_remaining_time ())/.2.

let pred_elim_time_limit () =  (prep_remaining_time ())/.2.

(*  (prep_remaining_time ())/. 2. *)
(*
let get_half_time_limit () = prep_remaining_time ()
*)
  (* prep_qbf_remaining_time ()*)

(*
  let half_time_lim =  (prep_qbf_remaining_time ())/. 2. in
  dbg D_time (lazy 
   (" iprover_running_time: "^(string_of_float (iprover_running_time ()))
  ^" prep_qbf_remaining_time: "^(string_of_float (prep_qbf_remaining_time ()))
  ^" get_half_time_limit: "^(string_of_float half_time_lim)));
  half_time_lim
  *)  


let check_time ~start_time ~time_limit = 
  let current_time = Unix.gettimeofday () in
   if (!current_options.time_out_real > 0.) 
   then 
    (
     let time_diff = (current_time -. start_time) in 
     if (time_diff > time_limit)
     then
       ( 
(*
         dbg D_time (lazy (" timeout time_limit: "^(string_of_float time_limit)
                           ^" iprover_running_time: "^(string_of_float (iprover_running_time ()))
                           ^" prep_qbf_remaining_time: "^(string_of_float (prep_qbf_remaining_time ()))
                           ^" get_half_time_limit: "^(string_of_float (get_half_time_limit ()))));
*)
         raise QBF_prep_timeout
        )
    )     



(*-------------------------------*)    

let get_var_list_dep qbf var_dep vlist = 
  (* union of dep of e vars in vlist and {avars} *)
  let f dep_set v = 
    try 
      let v_dep_set = PVMap.find v var_dep in
      PVSet.union v_dep_set dep_set
    with 
      Not_found ->
        (         
        (if (not (QE.qbf_is_a_var qbf v))
        then 
          (
           QE.out_qbf qbf;
           failwith ("get_var_list_dep: v should be A var : "^(PV.var_to_string v)^" mem qbf "
                     ^(string_of_bool (QE.qbf_var_in_qbf qbf v)))
          )
        );
(*         assert (QE.qbf_is_a_var qbf v);  *)
         PVSet.add v dep_set
         )
  in
  List.fold_left f PVSet.empty vlist
    
let get_lit_list_dep qbf var_dep lit_list = 
  let vlist = List.map PV.get_var_lit lit_list in
  get_var_list_dep qbf var_dep vlist
    
(*-------------------------------*)    

let q_resolve_dep qbf var_dep c =
  (if (PVE.is_tautology c)
  then
    (Statistics.incr_int_stat 1 Statistics.qbf_num_tautologies;
     raise Eliminated)
  );
  let lit_lits = PVE.clause_get_lits c in
  let (a_lits, e_d_lits) = List.partition (fun lit -> (QE.qbf_is_a_var qbf (PV.get_var_lit lit))) lit_lits in
  let e_d_dep = get_var_list_dep qbf var_dep (List.map PV.get_var_lit e_d_lits) in 
  let new_a_lits = List.filter (fun l -> PVSet.mem (PV.get_var_lit l) e_d_dep) a_lits in 
  if (List.length new_a_lits) <  (List.length a_lits)
  then 
    (
     let new_lits = e_d_lits@new_a_lits in
     let new_clause = PVE.clause_create new_lits (Q_Res c) in 
     Statistics.incr_int_stat 1 Statistics.qbf_q_res;
     dbg D_q_res (lazy ((PVE.clause_to_string new_clause)^" <- "^(PVE.clause_to_string c)));
     (if (PVE.is_empty_clause new_clause) 
     then
       raise (Unsatisfiable_gr); 
(*       raise (Unsatisfiable new_clause); *)
     );
     new_clause
    ) 
  else
    c

let q_resolve ?var_dep qbf c = 
  match var_dep with 
  |Some(var_dep) -> q_resolve_dep qbf var_dep c 
  |None -> QE.q_resolve_clause qbf c

let q_resolve_qbf ?var_dep qbf =  
  let f cl_list cl = 
    try 
      (q_resolve ?var_dep qbf cl)::cl_list
    with 
      Eliminated -> cl_list
  in
  let new_clause_list = List.fold_left f [] qbf.qbf_clauses in
  qbf.qbf_clauses <- new_clause_list


(*----------------------------*)

let prop_subsumption ?var_dep qbf pf_env = 
  let fof_clauses = List.map (prop_clause_to_fof pf_env) qbf.QE.qbf_clauses in 
  List.iter Prop_solver_exchange.add_clause_to_solver fof_clauses;
  let f c = 
    let simp_c =  Simplify.forward_prop_subsume c in 

    if (not (c == simp_c))
    then 
      (
       dbg D_gs (lazy (" before: "^(Clause.to_string c)));
       dbg D_gs (lazy (" after: "^(Clause.to_string simp_c)));
       let pclause = fof_clause_to_prop pf_env simp_c in 
       let new_pclause = q_resolve ?var_dep qbf pclause in
       if (not (new_pclause == pclause)) 
       then 
         prop_clause_to_fof pf_env new_pclause 
       else 
         simp_c
      )
    else
      c
  in
  let simp_fof_clauses = List.map f fof_clauses in 
  let new_prop_clauses = List.map (fof_clause_to_prop pf_env) simp_fof_clauses in 
  qbf.QE.qbf_clauses <- new_prop_clauses 


let get_num_of_plits cl_list =
  List.fold_left (fun rest c -> (List.length (PVE.clause_get_lits c)) + rest) 0 cl_list 
    
let prop_subsumption_exhaustive_clause clause = 
  let finished = ref false in
  let simp_clause_ref = ref clause in
  let count = ref 0 in 
  while (not !finished)
  do
    let simp_c = Simplify.forward_prop_subsume !simp_clause_ref in 
    (
    if (not (!simp_clause_ref == simp_c))
    then
      (
       count:=!count+1;
       dbg D_gs (lazy (" before: "^(Clause.to_string !simp_clause_ref)));
       dbg D_gs (lazy (" after: "^(Clause.to_string simp_c)^" count: "^(string_of_int !count))); 
       simp_clause_ref := simp_c;              
      )
    else 
      (
       finished:=true;
      ) 
    )
  done;
  !simp_clause_ref

let cmp_pclause_num_lits c1 c2 = 
  let num_lits1 = List.length  (PVE.clause_get_lits c1) in
  let num_lits2 = List.length  (PVE.clause_get_lits c2) in
  Pervasives.compare num_lits1 num_lits2

let prop_subsumption_exhaustive ?var_dep qbf pf_env = 
  let start_time = Unix.gettimeofday () in 
  let time_limit = prop_subs_time_limit () in
  dbg D_time (lazy (" prop_subsumption_exhaustive: time_limit: "^(string_of_float time_limit)));
  print_string (" ps_s  "); flush stdout;
  let num_of_gs_subs_before = Statistics.get_val_stat Statistics.prop_fo_subsumed in
  let sorted_pclauses =  List.sort cmp_pclause_num_lits qbf.QE.qbf_clauses in
  let fof_clauses = List.map (prop_clause_to_fof pf_env) sorted_pclauses in 
  List.iter Prop_solver_exchange.add_clause_to_solver fof_clauses;
  let changed = ref true in
  let simp_clauses = ref fof_clauses in
 
 (* (try*)
    while !changed 
    do
      let new_changed =  ref false in 
      let g c =
        try
          check_time ~start_time ~time_limit;
          let simp_c = prop_subsumption_exhaustive_clause c in 
          if (not (c == simp_c))
          then
            (
             dbg D_gs (lazy (" before: "^(Clause.to_string c)));
             dbg D_gs (lazy (" after: "^(Clause.to_string simp_c))); 
             new_changed:=true;
             let pclause = fof_clause_to_prop pf_env simp_c in 
             let new_pclause = q_resolve ?var_dep qbf pclause in
             if (not (new_pclause == pclause)) 
             then 
               prop_clause_to_fof pf_env new_pclause 
             else 
               simp_c
            )
          else
            c   
        with 
          QBF_prep_timeout -> c
      in
      let new_simp_cls = List.map g !simp_clauses in
      changed := !new_changed;
      simp_clauses := new_simp_cls;
    done;
  let new_prop_clauses = List.map (fof_clause_to_prop pf_env) !simp_clauses in 
(* statistics out *)
  let num_of_gs_subs_after = Statistics.get_val_stat Statistics.prop_fo_subsumed in
  let end_time =  Unix.gettimeofday () in 
  print_string 
    (
     (string_of_int (num_of_gs_subs_after - num_of_gs_subs_before))
     ^"c "
     ^(string_of_int (truncate (end_time -. start_time))^"s ps_e" )); flush stdout;
(* end statistics out *)
  qbf.QE.qbf_clauses <- new_prop_clauses

(*
      (let new_prop_clauses = List.map (fof_clause_to_prop pf_env) !simp_clauses in 
      qbf.QE.qbf_clauses <- new_prop_clauses;
      raise QBF_prep_timeout 
      )
*)

(*
  let prop_subsumption_exhaustive_clause clause = 
  let rec f c = 
  let simp_c = Simplify.forward_prop_subsume c in 
  if (not (c == simp_c))
  then
  (dbg D_gs (lazy (" before: "^(Clause.to_string c)));
  dbg D_gs (lazy (" after: "^(Clause.to_string simp_c))); 
  f simp_c 
  )
  else 
  c 
  in
  f clause

  let prop_subsumption_exhaustive qbf pf_env = 
  let fof_clauses = List.map (prop_clause_to_fof pf_env) qbf.QE.qbf_clauses in 
  let rec f changed cls = 
  if (not changed) 
  then
  cls
  else
  (
  let new_changed =  ref false in 
  let g c =
  let simp_c = prop_subsumption_exhaustive_clause c in 
  if (not (c == simp_c))
  then
  (
  new_changed:=true;
  let pclause = fof_clause_to_prop pf_env simp_c in 
  let new_pclause = QE.q_resolve_clause qbf pclause in 
  if (not (new_pclause == pclause)) 
  then 
  prop_clause_to_fof pf_env new_pclause 
  else 
  simp_c
  )
  else
  c               
  in
  let simp_cls = List.map g cls in 
  f !new_changed simp_cls
  )
  in
  let simp_fof_clauses = f true fof_clauses in
  let new_prop_clauses = List.map (fof_clause_to_prop pf_env) simp_fof_clauses in 
  qbf.QE.qbf_clauses <- new_prop_clauses 
 *)

(*
  let prop_subsumption_exhaustive qbf pf_env = 
  let exhausted = ref false in
  while (not !exhausted)
  do
  let old_num_of_lits = get_num_of_plits qbf.QE.qbf_clauses in
  prop_subsumption qbf pf_env;
  let new_num_of_lits = get_num_of_plits qbf.QE.qbf_clauses in
  (if (old_num_of_lits = new_num_of_lits) 
  then 
  exhausted:= true
  );
  done
 *)


(*--------------------resolution preprocess --------------*)
let res_prep_options () = 
  {!current_options
  with 
   (*----Resolution---------*)
   
   resolution_flag = true;
   
   res_prop_simpl_new = true;

   res_prop_simpl_given = true;

   res_passive_queue_type = PQT_PriorityQueues;
   res_passive_queues =
   [
    [Cl_Num_of_Lits false; Cl_Num_of_Symb false]
  ];
   res_passive_queues_freq = [150];
   
   res_forward_subs = Subs_Full;
   res_backward_subs = Subs_Full;
   res_forward_subs_resolution = true;
   (*  res_forward_subs_resolution    = true; exp later for sat *)
   (* res_backward_subs_resolution   = false; *)
   res_backward_subs_resolution = true;
   res_time_limit = 120.0;
 }


(*------------- res_preprocess ---------*)
let res_preprocess ?var_dep qbf pf_env =  
  let start_time = Unix.gettimeofday () in 
  print_string (" rs_s  "); flush stdout; 
 
  let old_options = !current_options in 
  current_options := res_prep_options ();
  let prop_clauses = qbf.QE.qbf_clauses in 
  let fof_clauses = List.map (prop_clause_to_fof pf_env) prop_clauses in 
 
  let res_state = Resolution_loop.res_create_state ~res_prep_only:true in
  Resolution_loop.res_add_clause_list res_state fof_clauses;

  let preprocessed_fof_clauses = Resolution_loop.res_preprocess res_state in

  let q_res fof_clause = 
    let pclause = fof_clause_to_prop pf_env fof_clause in 
    let new_pclause = q_resolve ?var_dep qbf pclause in
    new_pclause 
  in
  let preprocessed_prop_clauses = List.map q_res preprocessed_fof_clauses in 
  current_options := old_options;

(* out stats *)
  let num_of_cl_before = List.length prop_clauses in 
  let num_of_cl_after = List.length preprocessed_prop_clauses in 
  let end_time =  Unix.gettimeofday () in 
  print_string 
    (
     (string_of_int (num_of_cl_before - num_of_cl_after))
     ^"c "
     ^(string_of_int (truncate (end_time -. start_time))^"s rs_e" )); flush stdout;
(*---*)
  qbf.QE.qbf_clauses <- 
    preprocessed_prop_clauses



let dbg_pred_elim_qbf_flag = true
(* SW
let _ = out_warning ("pred_elim_qbf: "^(string_of_bool dbg_pred_elim_qbf_flag))
*)


(*-----------pred elim preliminaries -----------------------*)

let get_max_var_lvl qbf c =
  let lits = PVE.clause_get_lits c in 
  assert (not (lits == []));
  let get_lvl_lit lit = 
    let v = PV.get_var_lit lit in 
    QE.qbf_get_var_level qbf v
  in
  let cmp_lit_lvl l1 l2 = Pervasives.compare (get_lvl_lit l1) (get_lvl_lit l2) in
  let max_lvl_lit = list_find_max_element cmp_lit_lvl lits in
  get_lvl_lit max_lvl_lit 

(* based on lvl weaker than based on dep *)
let not_to_elim_var_set qbf =     
  let f f_nte_rest_set c = 
    let lits = PVE.clause_get_lits c in 
    let max_lvl = get_max_var_lvl qbf c in 
    let g g_nte_rest_set lit =
      let v = PV.get_var_lit lit in
      let (lvl, quant) = QE.qbf_get_var_qlevel qbf v in          
      if (quant = QE.E) && (lvl < max_lvl) 
      then 
        PVSet.add v g_nte_rest_set
      else
        g_nte_rest_set
    in 
    List.fold_left g f_nte_rest_set lits
  in
  List.fold_left f PVSet.empty qbf.QE.qbf_clauses

(*can raise Not_found *)
let get_max_a_var_lvl_dep qbf var_dep c =
  let lits = PVE.clause_get_lits c in 
  assert (not (lits == []));
  let a_dep_var_set = 
    let f a_set lit = 
      let var = PV.get_var_lit lit in
      let (_lvl, quant) = QE.qbf_get_var_qlevel qbf var in
      match quant with 
      |QE.A -> PVSet.add var a_set 
      |QE.E -> 
          let v_a_set = QE.get_var_dep var_dep var in 
          PVSet.union v_a_set a_set
      |QE.D -> failwith "dvars are not suppored in get_max_a_var_lvl_dep"
    in
    List.fold_left f PVSet.empty lits
  in
  let a_dep_list = PVSet.elements a_dep_var_set in 
  let get_lvl_var v = QE.qbf_get_var_level qbf v
  in
  let cmp_lvl_var v1 v2 = Pervasives.compare (get_lvl_var v1) (get_lvl_var v2) in
  let max_lvl_var = list_find_max_element cmp_lvl_var a_dep_list in
  get_lvl_var max_lvl_var 

(*
let not_to_elim_var_set_dep qbf var_dep =     
  let f f_nte_rest_set c = 
    let lits = PVE.clause_get_lits c in 
    try 
      let max_lvl = get_max_a_var_lvl_dep qbf var_dep c in 
      let g g_nte_rest_set lit =
        let v = PV.get_var_lit lit in
        let (lvl, quant) = QE.qbf_get_var_qlevel qbf v in          
        if (quant = QE.E) && (lvl < max_lvl) 
        then 
          PVSet.add v g_nte_rest_set
        else
          g_nte_rest_set
      in
      List.fold_left g f_nte_rest_set lits
    with 
      Not_found -> f_nte_rest_set (* No a/a_dep_vars *)
  in
  List.fold_left f PVSet.empty qbf.QE.qbf_clauses
*)


let to_elim_symb_set qbf pf_env = 
  let nte_var_set = not_to_elim_var_set qbf in
  let f pvar symb elim_set = 
    let (_lvl, quant) = QE.qbf_get_var_qlevel qbf pvar in 
    if (quant = QE.E) && (not (PVSet.mem pvar nte_var_set))
    then
      SSet.add symb elim_set
    else 
      elim_set 
  in
  let prop_to_fof_symbs_map = get_prop_to_fof_symbs pf_env in 
  PVMap.fold f prop_to_fof_symbs_map SSet.empty 

(*-------new-----*)

let vset_to_fof_symb_set pf_env vset = 
  let f v rest = 
    SSet.add (prop_var_to_fsymb pf_env v) rest
  in
  PVSet.fold f vset SSet.empty
    

let get_d_or_e_vars qbf = 
  PVSet.filter (QE.qbf_is_d_or_e_var qbf) qbf.QE.qbf_vars

let filter_not_to_eliminate_dep qbf var_dep var_set = 
  let f f_rest_set c = 
    let c_vars = List.map PV.get_var_lit (PVE.clause_get_lits c) in   
    let c_dep_set = get_var_list_dep qbf var_dep c_vars in 
    let g g_rest_set var =      
      if (PVSet.mem var g_rest_set)
      then 
        let v_dep_set = get_var_list_dep qbf var_dep [var] in 
        if (not (PVSet.equal c_dep_set v_dep_set))
        then 
          (

           dbg D_trace (lazy ("filter_not_to_eliminate_dep:rm: "^(PV.var_to_string var)));
           PVSet.remove var g_rest_set             
          )
        else 
          (
           dbg D_trace (lazy ("filter_not_to_eliminate_dep:keep: "^(PV.var_to_string var)));
           g_rest_set
          )
      else
        g_rest_set
    in
    List.fold_left g f_rest_set c_vars
  in
  List.fold_left f var_set qbf.QE.qbf_clauses

let to_elim_var_set_dep qbf var_dep = 
  let d_or_e_vars = get_d_or_e_vars qbf in
  filter_not_to_eliminate_dep qbf var_dep d_or_e_vars

let to_elim_symb_set_dep qbf pf_env var_dep = 
  let elim_var_set = to_elim_var_set_dep qbf var_dep in
  let elim_symb_set = vset_to_fof_symb_set pf_env elim_var_set in
  elim_symb_set


(*
let all_d_or_e_symb_set qbf pf_env = 
  let f pvar symb e_set = 
    if ((QE.qbf_var_in_qbf qbf pvar) && (QE.qbf_is_d_or_e_var qbf pvar))
    then 
      SSet.add symb e_set
    else 
      e_set 
  in
  let prop_to_fof_symbs_map = get_prop_to_fof_symbs pf_env in 
  PVMap.fold f prop_to_fof_symbs_map SSet.empty 
*)


(*------------------------------------------------*)
let pred_elim_qbf qbf pf_env var_dep = 
  
  if (not dbg_pred_elim_qbf_flag)  (* (not !current_options.qbf_pred_elim) *)
  then 
    ()
  else   
    begin

      let fof_clauses = List.map (prop_clause_to_fof pf_env) qbf.QE.qbf_clauses in 

      let pred_elim_options = 
        {
	 pe_has_eq = false; 
	 pe_estim_num_of_lits =   5000;  (* 10000; *)

	 pe_conclusion_limit_test = 
         (fun c -> 
           (Clause.num_of_symb c) < 1000
         );

         pe_preprocess_conclusion_extern = 
         (fun c -> 

           let pclause = fof_clause_to_prop pf_env c in 
          
(* can raise Eliminated if pclause is a tautology which is ok *)
           let new_pclause = q_resolve_dep qbf var_dep pclause in 

           if (not (new_pclause == pclause)) 
           then 
             prop_clause_to_fof pf_env new_pclause 
           else 
             c

         );

(* NOT USED *) pe_elim_order_cmp_fun = (fun _context s1 s2 ->  Symbol.compare s1 s2); (*pred_elim_cmp_fun;*) (* NOT USED *)

	 pe_elimination_set = to_elim_symb_set_dep qbf pf_env var_dep; 

	 pe_keep_elim =  
         (fun  ~elim_symb ~clauses_before_elim ~clauses_after_elim ->           

           let pelim_var = fof_to_prop_symb pf_env elim_symb in 
           
           let pvar_cost var = 
             try 
               let v_dep_set = PVMap.find var var_dep in
               PVSet.cardinal v_dep_set
             with 
               Not_found -> 1
           in
           let plit_cost lit = pvar_cost (PV.get_var_lit lit) in 
           let pcl_cost pc = List.fold_left (fun rest lit -> (plit_cost lit) + rest) 0 (PVE.clause_get_lits pc) in 
           let cl_cost c = pcl_cost (fof_clause_to_prop pf_env c) in

           let cl_list_cost cl_list = List.fold_left (fun rest c -> (cl_cost c)  + rest) 0 cl_list in
           
           let cl_cost_before = cl_list_cost clauses_before_elim in
           let cl_cost_after  = cl_list_cost clauses_after_elim in
           
           dbg D_pred_elim (lazy ("eliminating: "^(PV.var_to_string pelim_var)));
           dbg D_pred_elim (lazy ("pe_keep_elim: dep cost: before: "^(string_of_int cl_cost_before)
                                  ^" after: "^(string_of_int cl_cost_after)));


           let keep_res = cl_cost_after <= cl_cost_before in 
(*           let keep_res = true in *)

           dbg D_pred_elim (lazy ("pe_keep_elim: keep ?: "^(string_of_bool keep_res)));            

           keep_res               
         );
(*
             let num_cl_before = (List.length clauses_before_elim) in 
             let num_cl_after  = (List.length clauses_after_elim) in
             let keep_res =             
               if num_cl_after = 0
               then 
                 ( 
                   dbg D_pred_elim (lazy ("pe_keep_elim: all clauses are simplified" ));
                   true 
                  )
               else 
                 begin
                   assert (num_cl_before > 1);
                   
(*
  let get_num_of_symb cl_list = 
  List.fold_left (fun rest c -> (Clause.num_of_symb c) + rest) 0 cl_list 
  in
 *) 
                   let get_num_of_lits cl_list =
                     List.fold_left (fun rest c -> (Clause.length c) + rest) 0 cl_list 
                   in 
                   let get_num_e_lits_clause cl = 
                     let f rest lit = 
                       let plit = fof_lit_to_prop pf_env lit in
                       let pvar = PV.get_var_lit plit in
                       if (QE.qbf_is_e_var qbf pvar) 
                       then 
                         rest+1 
                       else
                         rest
                     in
                     Clause.fold f 0 cl 
                   in
                   let get_num_e_lits cl_list = 
                     List.fold_left (fun rest c -> (get_num_e_lits_clause c) + rest) 0 cl_list 
                   in
(* 
   List.fold_left (fun rest c -> (Clause.length c) + rest) 0 cl_list 
 *)

                   let num_lits_before = get_num_of_lits clauses_before_elim in 
                   let num_lits_after = get_num_of_lits clauses_after_elim in 
                   
                   let num_e_lits_before = get_num_e_lits clauses_before_elim in 
                   let num_e_lits_after  = get_num_e_lits clauses_after_elim in 
                   
                   let cl_max_lits_before = list_find_max_element Clause.cmp_num_lits clauses_before_elim in 
                   let cl_max_lits_after = list_find_max_element Clause.cmp_num_lits clauses_after_elim in 
                   
                   let cl_max_e_lits_before_num = get_num_e_lits_clause cl_max_lits_before in 
                   let cl_max_e_lits_after_num =  get_num_e_lits_clause cl_max_lits_after in
                   
(*TODO: add varible square mesure per clause cl = \sum (num var lits)^2 *)
                   
                   dbg D_pred_elim (lazy ("pe_keep_elim: num_cl: before: "^(string_of_int num_cl_before)
                                          ^" after: "^(string_of_int num_cl_after)));
                   
                   dbg D_pred_elim (lazy ("pe_keep_elim: num_lits: before:  "^(string_of_int num_lits_before)
                                          ^" after: "^(string_of_int num_lits_after)));

                   dbg D_pred_elim (lazy ("pe_keep_elim: num_e_lits: before:  "^(string_of_int num_e_lits_before)
                                          ^" after: "^(string_of_int num_e_lits_after)));

                   dbg D_pred_elim (lazy ("pe_keep_elim: cl_max_e_lits: before:  "^(string_of_int cl_max_e_lits_before_num)
                                          ^" after: "^(string_of_int cl_max_e_lits_after_num)));
                   
                   (*----------------*)     

(*                  num_lits_after <=  num_lits_before
                    &&
 *)

                   num_e_lits_after <= num_e_lits_before                     
                     &&
                   ( num_e_lits_after <= !current_options.qbf_split
                   ||
                     cl_max_e_lits_after_num <= cl_max_e_lits_before_num
                    )
                 end
             in
             dbg D_pred_elim (lazy ("pe_keep_elim: keep ?: "^(string_of_bool keep_res)));            
             keep_res               
         ); 
(*-----------*)
*)         
	 (* (if (is_ver_epr ())   *)
	 (* then *)
	 (*   (fun ~num_cl_before ~num_cl_after ->  *)
	 (*     (num_cl_after <= num_cl_before)  || (num_cl_after <= 2)) (\* (num_cl_after <= 6) ) *\) *)
	 (* else *)
	 (*   (fun ~num_cl_before ~num_cl_after ->  *)
	 (*     (num_cl_after <= num_cl_before) (\* ||  (num_cl_after <= 6)*\) ) *)
	 (* ); *)


(* 1/4 of the remaining time *)
         pe_time_limit =
         
         (if (!current_options.time_out_real > 0.)
         then  
           let time_limit = pred_elim_time_limit () in 
           if (time_limit > 0.) 
           then              
             (
              dbg D_time (lazy (" pred_elim timelimit "^(string_of_float time_limit)));
              time_limit 
             )
           else
             1.
         else
           -1.
         );	
(* simplifications *)

(*	subs_cl_to_cl_limit = 100000; *)
	 subs_cl_to_cl_limit = 100000;  


(* sim prop *)
	 prop_glb_subs =   (* false;*)  true; 
(*
  (if (num_of_input_clauses < 100000 )
  then
  true  (* prop global subsumtion changed for finite models exp. *)
  else
  false
  );
 *)	
(* sim local *) 
	 
         lcl_add_to_sub_index_test = (fun _c -> true); (* (fun _c -> false); *)
(*
  (fun c ->
  (((Clause.num_of_var c) <= 100) && ((Clause.num_of_symb c) <= 1000))
  );
 *)
	 (* Options.res_subs_type: type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int *)
	 
	 lcl_fwd_subs =   (* false; *) true; 
(*
  (if (num_of_input_clauses < 200000)
  then
  true
  else
  false
  );
 *)      
	 lcl_fwd_subs_res =  (* false; *)  true;
(*
  (
  if (num_of_input_clauses < 100000 (* 100000*))
  then
  true
  else
  false
  else
  true (*  false *)
  );
 *)
	 
	 lcl_bwd_subs = Subs_Full; (* Subs_Subset; *)
         
(* Subs_Full; *)
(*  Subs_By_Length(2); *)
(*
  (if (is_ver_epr ())
  then
  if  (num_of_input_clauses < 100000) (* (num_of_input_clauses < 400000)*)
  then
  Subs_By_Length(1) (* Subs_By_Length(1) *)
  else
  Subs_Subset
  
  (* Subs_Subset*)  (*(Subs_By_Length(1)) *) (* Subs_Full *)
  else
  (* Subs_Full*)  Subs_By_Length(20) (* Subs_Subset *)(* (Subs_By_Length(2)) *) (* (Subs_Full) *)
  );
 *)
	 lcl_bwd_subs_res = Subs_Full; (*Subs_Subset; *)
(*
  lcl_bwd_subs_res =   (* Subs_Full;*)
  (if  (is_ver_epr ())
  then
  if (num_of_input_clauses < 100000 (* 100000*))
  then
  Subs_By_Length(1)
  else
  Subs_Subset
  
  (* Subs_Subset*) (*  (Subs_By_Length(1)) *)(* Subs_Full *)
  else
  (* Subs_Full *)  (Subs_By_Length(20))  (* Subs_Subset *)(* (Subs_By_Length(2))*) (* (Subs_Full) *)
  );
 *)
	 
(* sim global *)

         glb_add_to_sub_index_test =  (* (fun _c -> false); *)   (fun c -> (Clause.length c) <= 200); 
(*
  (fun c ->
  ((Clause.num_of_var c) <= 100)  && ((Clause.num_of_symb c) <= 1000));
 *)	
	 glb_fwd_subs = (*  false; *)  true; 
(*
  (if (is_ver_epr ())
  then
  if (num_of_input_clauses < 100000 (*200000 *))
  then
  true
  else
  false
  else
  true  (* false *)
  );
 *)	
	 glb_fwd_subs_res = (*false;*)  true; 
(*	(if (is_ver_epr ())
  then
  if (num_of_input_clauses < 100000 (* 100000 *) )
  then
  true
  else
  false
  else
  true  (* false; *) 
  );
 *)
	 glb_bwd_subs =  Subs_By_Length(10); (* Subs_Subset;*) (*Subs_By_Length(100);*)

(* (* Subs_Full; *)
   (if (is_ver_epr ())
   then
   if (num_of_input_clauses < 100000 (*200000*))
   then
   Subs_By_Length(1)
   else
   Subs_Subset (*  Subs_By_Length(1) *)  (*Subs_Full*)
   else
   (* Subs_Full; *) (* Subs_Subset *)  Subs_By_Length(10);  (* Subs_By_Length(4); *) 
   );
 *)	
	 glb_bwd_subs_res =  Subs_By_Length(10);  (* Subs_Subset; *)(*Subs_By_Length(100);*) (* Subs_Full;*)
(*
  (if (is_ver_epr ())
  then
  if (num_of_input_clauses < 100000 (* 200000 *))
  then
  Subs_By_Length(1)
  else
  Subs_Subset (* Subs_By_Length(1) *)(* Subs_Full*)
  else
  (* Subs_Full; *) (* Subs_Subset *) Subs_By_Length(10); (* Subs_By_Length(4); *) (*Subs_Full; *)
  );
 *)
       }
      in
      (*let fixed_point_reached = ref false in*)
      (* out_str (Clause.clause_list_to_string !current_list); *)

      let new_fof_clauses = PredElim.predicate_elimination pred_elim_options (Clause.CL_List (fof_clauses)) in
      let new_prop_clauses = List.map (fof_clause_to_prop pf_env) new_fof_clauses in 
      qbf.QE.qbf_clauses <- new_prop_clauses;    
    end


(*---------------------------------------*)
let merge_defs qbf pf_env =   
  let prop_clauses = qbf.QE.qbf_clauses in 
  let fof_clauses = List.map (prop_clause_to_fof pf_env) prop_clauses in 

  let old_opt_prep_def_merge_prop_impl = !current_options.prep_def_merge_prop_impl in
  !current_options.prep_def_merge_prop_impl <- true;

  out_str ("qbf: merge_defs: current_options.prep_def_merge_prop_impl <- true");

  let prep_fof_clauses = Bin_hyper_res.def_merge fof_clauses in

  !current_options.prep_def_merge_prop_impl <- old_opt_prep_def_merge_prop_impl;

  let prep_prop_clauses = List.map (fof_clause_to_prop pf_env) prep_fof_clauses in 
  qbf.QE.qbf_clauses <-prep_prop_clauses
 
(*------------*)
let get_var_dep qbf = 
  let var_dep_map = 
    if !current_options.qbf_sk_in 
    then 
      QE.qbf_inner_var_dep qbf
    else
      QE.qbf_outer_var_dep qbf
  in
  var_dep_map


(* remove all vars from prefix that are not in cnf *)
let reduce_vars_qbf qbf =   
  let get_var_set cl_list = 
    let f f_v_set c = 
      let g g_v_set lit = 
        PVSet.add (PV.get_var_lit lit) g_v_set 
      in
      List.fold_left g f_v_set (PVE.clause_get_lits c)
    in
    List.fold_left f PVSet.empty cl_list
  in
  let new_qbf_vars = get_var_set qbf.QE.qbf_clauses in 
  let reduce_qp lvl qb new_qp = 
    let new_qb_vars = PVSet.inter qb.QE.qb_vars new_qbf_vars in 
    if (PVSet.is_empty new_qb_vars)
    then
      new_qp
    else
      let new_qb =  {qb with QE.qb_vars = new_qb_vars } in 
      IntMap.add lvl new_qb new_qp
  in
  let new_qbf_pref = IntMap.fold reduce_qp qbf.QE.qbf_pref IntMap.empty in 
  let new_qbf_var_level = PVMap.filter (fun v _ -> (PVSet.mem v new_qbf_vars)) qbf.QE.qbf_var_level in
(*
    let f v lvlq new_vl = 
      if (PVSet.mem v new_qbf_vars) 
      then
        PVMap.add v lvlq new_vl
      else
        new_vl
    in
    PVMap.fold f qbf.QE.qbf_var_level PVMap.empty 
  in 
*)
  let new_qbf_dvar_map =  PVMap.filter (fun v _ -> (PVSet.mem v new_qbf_vars))  qbf.QE.qbf_dvar_map in
(*
    let f v dep_set new_dv_map in 
    if (PVSet.mem v new_qbf_vars) 
    then 
      PVMap.add v dep_set 
    else
  *)    

  qbf.QE.qbf_pref <- new_qbf_pref;
  qbf.QE.qbf_var_level <- new_qbf_var_level;
  qbf.QE.qbf_dvar_map <- new_qbf_dvar_map;
  qbf.QE.qbf_vars <- new_qbf_vars



(*-----  def_discovery ------*)

(* the gole is to reduce input pdef_var_dep based on discoved defintions in pdef_map *)
type prop_def_state = (* pds *)
    {
     pdef_qbf : QE.qbf_cnf;
     mutable pdef_var_dep : QE.qbf_var_dep;
     mutable pdef_vmap : (pvar list) list PVMap.t;
 (* for computing dependancies we ignore polarities; *)
 (* we also restrict to existantial vars on the left-hand-side *)
 (* TODO: add several def. lists  *)
 (* TODO: extend to univ. vars on the left-hand-side;*)
 (*       the simple case when x<-> e is covered as we also have e<->x in the fof def_map *)
 (*       but what happens when x<-> e1 & e2 ? *)

           (* e dependencies in the defintions:  e1 <-> .. e2... then e2 -> {..e1..} *)  
   mutable pdef_evar_def_dep : PVSet.t PVMap.t;

   } 

let fof_lit_to_pvar pf_env lit = PV.get_var_lit (fof_lit_to_prop pf_env lit) 

let fof_def_map_to_pdef_vmap pf_env fof_def_map = 
  let f lit def_list pdef_map = 
    let pvar = fof_lit_to_pvar pf_env lit in 
    let pdef_vlist = List.map (List.map (fof_lit_to_pvar pf_env)) def_list in 
    try (* there is a definition alredy in the map due to compl_lit *) 
      let old_pdef_vlist = PVMap.find pvar pdef_map in 
      PVMap.add pvar (old_pdef_vlist@pdef_vlist) pdef_map
(*
      if (List.length pdef_vlist) < (List.length old_pdef_vlist) (* prefer shorter defs. TODO add multiple defs *)
      then 
        PVMap.add pvar pdef_vlist pdef_map
      else
        pdef_map 
    with 
      Not_found -> 
        PVMap.add pvar pdef_vlist pdef_map
  in
*)
    with 
      Not_found -> 
        PVMap.add pvar pdef_vlist pdef_map
  in
  TMap.fold f fof_def_map PVMap.empty

let filter_pdef_vmap_vars_in_qbf qbf pdef_vmap = 
  let fitler_rhs_defs def_list = 
    List.filter (fun vlist -> (not (List.exists (fun rv -> not (QE.qbf_var_in_qbf qbf rv)) vlist ))) def_list in     
  let f v def_list new_def_map = 
    if (QE.qbf_is_d_or_e_var qbf v) 
    then
      let new_def_list = fitler_rhs_defs def_list in 
      if (new_def_list = [])  
      then 
        new_def_map
      else 
        PVMap.add v new_def_list new_def_map
    else
      new_def_map
  in
  PVMap.fold f pdef_vmap PVMap.empty

let get_pdef_evar_def_dep qbf pdef_vmap = 
  let f left_var pdef_list evar_def_dep = 
    List.fold_left (* add left_var to all right_evars *) 
      (fun dep right_var -> 
        if (QE.qbf_is_d_or_e_var qbf right_var) 
        then 
          let old_set = 
            try
              PVMap.find right_var evar_def_dep 
            with 
              Not_found -> PVSet.empty
          in
          let new_set = PVSet.add left_var old_set in 
          PVMap.add right_var new_set dep
        else (* skip avars; check d_vars! *)
          ( assert (QE.qbf_is_a_var qbf right_var);
            dep
           )
      )
      evar_def_dep
      (List.flatten pdef_list)
  in
  PVMap.fold f pdef_vmap PVMap.empty


(*-----------*)
let rec reduce_dep_map_pds' pds vars_to_process = 
(* vars_to_process  are vars whose dep is changed; initially all left-vars in def are for processing *)
  try 
    let left_var = PVSet.choose vars_to_process in 
    let vars_to_process_no_left_var = PVSet.remove left_var vars_to_process in 
    let left_var_dep = 
      try 
        PVMap.find left_var pds.pdef_var_dep
      with 
        Not_found -> failwith ("reduce_dep_map_pds' left_var should be in pds.pdef_var_dep: "^(PV.var_to_string left_var)^"\n")
    in
    let right_defs_list = 
      try
        PVMap.find left_var pds.pdef_vmap
      with 
        Not_found -> failwith "reduce_dep_map_pds' left_var should be in pds.pdef_vmap"
    in
    dbg D_def_discovery (lazy ("old dep: "^(PV.var_to_string left_var)^": "
                               ^(PV.var_list_to_string (PVSet.elements left_var_dep))));
    
    let f dep_set right_v_list  =      
      let right_deps = get_var_list_dep pds.pdef_qbf pds.pdef_var_dep right_v_list in 
      PVSet.inter dep_set right_deps
    in
    let new_left_var_dep = 
      List.fold_left f left_var_dep right_defs_list in
    if (PVSet.cardinal new_left_var_dep) < (PVSet.cardinal left_var_dep) (* left_var_dep changed  *)
    then
      begin
        pds.pdef_var_dep <- PVMap.add left_var new_left_var_dep pds.pdef_var_dep;
         dbg D_def_discovery (lazy ("new dep: "^(PV.var_to_string left_var)^": "
                                   ^(PV.var_list_to_string (PVSet.elements new_left_var_dep))));

(* get all vars for which left_var occur in the right side *)
        let new_vars_to_process = 
          let evar_def_dep = 
            try 
              PVMap.find left_var pds.pdef_evar_def_dep          
            with 
              Not_found -> PVSet.empty
          in
          PVSet.union evar_def_dep vars_to_process_no_left_var
        in          
        reduce_dep_map_pds' pds new_vars_to_process
      end
    else
      reduce_dep_map_pds' pds vars_to_process_no_left_var       
  with
    Not_found -> 
      (
       assert (PVSet.is_empty vars_to_process);
       pds.pdef_var_dep
      )
        
let reduce_dep_map_pds qbf pds peqds =
  let f v _ vset = PVSet.add v vset in 
  let vars_to_process_pds = PVMap.fold f pds.pdef_vmap PVSet.empty in  (* all keys in pds.pdef_vmap *)
  let vars_to_process = 
    List.fold_left
      (fun vset atom_list -> 
        PVSet.union 
          (PVSet.of_list 
             (List.filter 
                (QE.qbf_is_d_or_e_var qbf) 
                atom_list)) 
          vset) 
      vars_to_process_pds 
      peqds
  in 
  reduce_dep_map_pds' pds vars_to_process  

(*
let get_evar_def_equiv_dep peqds =
*)  

let init_pds qbf var_dep pdef_vmap =
  
  let pds = 
    {
     pdef_qbf     = qbf;
     pdef_var_dep = var_dep;

     pdef_vmap         = pdef_vmap;
     pdef_evar_def_dep = get_pdef_evar_def_dep qbf pdef_vmap;
     
(*   pdef_evar_def_equiv_dep = get_evar_def_equiv_dep peqds; *)

   }   
  in
  pds
    
let extend_pdf_peqds qbf pds peqds =
  let f pvar_list = 
    let g pvar = 
      if (QE.qbf_is_d_or_e_var qbf pvar) 
      then
        let rest_vars = List.filter (fun x -> not (x == pvar)) pvar_list in  

(* extend pds.pdef_vmap *)
        let old_defs = 
          try
            PVMap.find pvar pds.pdef_vmap
          with
            Not_found -> []
        in        
        pds.pdef_vmap <- PVMap.add pvar (rest_vars::old_defs) pds.pdef_vmap; 

(* extend pds.pdef_evar_def_dep *)
        let rest_d_or_e_vars = List.filter (QE.qbf_is_d_or_e_var qbf) rest_vars in
        let old_set = 
            try
              PVMap.find pvar pds.pdef_evar_def_dep
            with 
              Not_found -> PVSet.empty
        in
        let new_set = PVSet.union (PVSet.of_list rest_d_or_e_vars) old_set in 
        pds.pdef_evar_def_dep <- PVMap.add pvar new_set pds.pdef_evar_def_dep            
      else
        ()
    in
    List.iter g pvar_list;
  in
  List.iter f peqds

let qbf_def_discovery ?cmp qbf pf_env var_dep =  
  let fof_clauses = List.map (prop_clause_to_fof pf_env) qbf.QE.qbf_clauses in 
  let fof_def_map = Def_discovery.get_def_map ?cmp fof_clauses in 
  let fof_equiv_defs = Def_discovery.get_equiv_defs fof_clauses in 
  dbg_env  D_def_discovery
    (fun () -> 
      out_str "";
      dbg D_def_discovery (lazy "definiton discovery: & ");
      Def_discovery.out_def_map fof_def_map;
      out_str "";
      dbg D_def_discovery (lazy "definiton discovery: <->");
      Def_discovery.out_equiv_defs fof_equiv_defs;
      out_str "";
    );
  let pdef_vmap = filter_pdef_vmap_vars_in_qbf qbf (fof_def_map_to_pdef_vmap pf_env fof_def_map) in
  let pds = init_pds qbf var_dep pdef_vmap in
  let peqds = (* for depedencies we just join even/odd together *)
    let comb_peqds = fof_equiv_defs.Def_discovery.eqd_odd@fof_equiv_defs.Def_discovery.eqd_even in
    List.map (fun fof_atom_list -> List.map (fof_lit_to_pvar pf_env) fof_atom_list) comb_peqds
  in 
  extend_pdf_peqds 
    qbf 
    pds 
    peqds;
  let new_var_dep = reduce_dep_map_pds qbf pds peqds in
   (* TODO: assign var dep to qbf *)
   (* TODO: trace everywhere is_e_var and incorporate d_var *)
  dbg_env  D_def_discovery
    (fun () -> 
(*
      out_str "";
      dbg D_def_discovery (lazy "definiton discovery:");
      Def_discovery.out_def_map fof_def_map;
*)
      out_str "";
      dbg D_def_discovery (lazy "reduced var_dep:\n");
      QE.out_var_dep new_var_dep;
      dbg D_def_discovery (lazy "end reduced var_dep \n");
      dbg D_def_discovery (lazy "done; exiting");
    );
  new_var_dep

(*----- end def_discovery ------*)

(*----------- *)
let dbg_qbf_res_prep_flag = (* false *) true
(* SW
let _ = out_warning ("dbg_qbf_res_prep_flag: "^(string_of_bool dbg_qbf_res_prep_flag))
*)

let var_dep_inter dep1 dep2 = 
  let f v dset_opt1 dset_opt2 =
    match (dset_opt1, dset_opt2) with
    | (Some(dset1), Some(dset2)) -> Some(PVSet.inter dset1 dset2)
    | _-> None (* var was eliminated *)
  in
  PVMap.merge f dep1 dep2

(* with larger dependencies are smaller and if not in the map then larger; smaller eliminated first from defs *)
let dep_cmp dep_map p1 p2 = 
  match ((PVMap.mem p1 dep_map), (PVMap.mem p2 dep_map)) with
  |(true, true) -> 
      let card1 = PVSet.cardinal (PVMap.find p1 dep_map) in 
      let card2 = PVSet.cardinal (PVMap.find p2 dep_map) in 
      Pervasives.compare card1 card2
  |(false, true)  ->  1
  |(true,  false) -> -1
  |(false, false) ->  0

let dep_cmp_fof pf_env dep_map fp1 fp2 = 
  let p1 = (fof_lit_to_prop pf_env fp1) in 
  let p2 = (fof_lit_to_prop pf_env fp2) in 
  dep_cmp dep_map (PV.get_var_lit p1) (PV.get_var_lit p2)

(*----------------------------------*)

let is_dqbf qbf = not (PVMap.is_empty qbf.QE.qbf_dvar_map)

(*----------------------------------*)
let preprocess_qbf qbf = 
  print_string ((s_pref_str ())^"QBF preprocessing...");
  flush stdout;

(* TODO extend preprocessing with dvars *)
(*  assert (PVMap.is_empty qbf.QE.qbf_dvar_map); *)
  dbg_env D_final 
    (fun() -> 
      dbg D_final (lazy "");
      dbg D_final (lazy "--------Init var_dep-------\n\n");
      QE.out_var_dep (get_var_dep qbf);
      dbg D_final (lazy "--------Init QBF-------\n\n");
      QE.out_qbf qbf;
    );

  let (taut, non_taut) = List.partition PVE.is_tautology qbf.QE.qbf_clauses in 

  Statistics.incr_int_stat (List.length taut) Statistics.qbf_num_tautologies;

  let pf_env = pf_env_create () in 
  let var_dep_ref = ref (qbf_def_discovery qbf pf_env (get_var_dep qbf)) in
  
  qbf.QE.qbf_clauses <- non_taut;

  q_resolve_qbf ~var_dep:!var_dep_ref qbf;  
 
  merge_defs qbf pf_env; 
 
  prop_subsumption_exhaustive ~var_dep:!var_dep_ref qbf pf_env;

  (* TODO:*)
  (* qbf_def_discovery qbf pf_env; *)

  let repeat_pred_elim = ref true in 
  let cycle_num = ref 0 in 

(*  QE.qbf_split_clauses 64 qbf; *) 
  


  while (!repeat_pred_elim &&  ((!current_options.time_out_real <= 0.)  || (prep_qbf_remaining_time () > -5.)))
  do

    cycle_num:=!cycle_num + 1;
    Statistics.incr_int_stat 1 Statistics.qbf_prep_cycles;
    dbg D_trace (lazy (" start new cycle: "^(string_of_int !cycle_num)));
    dbg D_trace (lazy (" start new cycle stat: "^(string_of_int (Statistics.get_val_stat Statistics.qbf_prep_cycles))));
    
    let old_num_of_clauses = List.length qbf.QE.qbf_clauses in
    let old_num_of_lits = get_num_of_plits qbf.QE.qbf_clauses in
    
    (if dbg_qbf_res_prep_flag
    then
      (res_preprocess ~var_dep:!var_dep_ref qbf pf_env;)
    else
      ()
    );
    
(* let old_num_of_elim = Statistics.get_val_stat Statistics.pred_elim in *)

(*    let var_dep = qbf_def_discovery qbf pf_env (get_var_dep qbf) in*)

(* TODO: intersect with previous var_dep; question: if we eliminated the definition is it still sound to reduce dep based  on it ? should be still OK -- argument: 1) keep defs aside 2) dep reduction based on defs is an over-approx 3) when remove defs in 1. we  can keep over approx *)
 
    reduce_vars_qbf qbf;

(*
    (if not (is_dqbf qbf)
    then
*)

 
    dbg_env D_pred_elim
      (fun () -> 
        dbg D_pred_elim (lazy (" before pred_elim \n\n"));
        QE.out_qbf qbf;
        QE.out_var_dep !var_dep_ref;
      );

     pred_elim_qbf qbf pf_env !var_dep_ref;  
    
      dbg_env D_pred_elim
      (fun () -> 
        dbg D_pred_elim (lazy (" after pred_elim \n\n"));
        QE.out_qbf qbf;
        QE.out_var_dep !var_dep_ref;
      );

(*
    else 
      ()
    );
*)
(*    prop_subsumption qbf pf_env; *)

    prop_subsumption_exhaustive ~var_dep:!var_dep_ref qbf pf_env; 

    reduce_vars_qbf qbf;     (* TODO: fix Not_found on BLOCKS4ii.7.2.qdimacs after reduction *)
    let new_num_of_clauses = List.length qbf.QE.qbf_clauses in
    let new_num_of_lits = get_num_of_plits qbf.QE.qbf_clauses in
(*    let new_num_of_elim = Statistics.get_val_stat Statistics.pred_elim in*) (* TODO: fix statistics *)

    (
     if ((old_num_of_lits = new_num_of_lits) && (old_num_of_clauses = new_num_of_clauses))
         (* ((old_num_of_clauses = new_num_of_clauses))*)
     then 
       repeat_pred_elim := false 
         else
       ()
    );

(*
    var_dep_ref := 
      var_dep_inter
        (qbf_def_discovery qbf pf_env (get_var_dep qbf)) 
(*        (qbf_def_discovery qbf pf_env !var_dep_ref) *)
        !var_dep_ref;
 *)

    dbg_env D_trace
      (fun () -> 
        QE.out_qbf qbf;
        QE.out_var_dep !var_dep_ref;
      );
   
done;

out_str "";

  !var_dep_ref
  
(*
(*    end 
  with 
    QBF_prep_timeout ->  *)
(*      begin *)
  QE.qbf_split_clauses !current_options.qbf_split qbf;
  dbg_env D_final 
    (fun() -> 
      dbg D_final (lazy "--------Final var_dep-------\n\n");
      QE.out_var_dep (get_var_dep qbf);
      dbg D_final (lazy "--------Final QBF-------\n\n");
      QE.out_qbf qbf;
    )
*)
(*      end *)

        
 

(*
(* TODO: merge all in one *)
let preprocess_dqbf qbf = 
  print_string ((s_pref_str ())^"QBF preprocessing...");
  flush stdout;

  dbg_env D_final 
    (fun() -> 
      dbg D_final (lazy "");
      dbg D_final (lazy "--------Init var_dep-------\n\n");
      QE.out_var_dep (get_var_dep qbf);
      dbg D_final (lazy "--------Init QBF-------\n\n");
      QE.out_qbf qbf;
    );
  let (taut, non_taut) = List.partition PVE.is_tautology qbf.QE.qbf_clauses in 
  Statistics.incr_int_stat (List.length taut) Statistics.qbf_num_tautologies;
  qbf.QE.qbf_clauses <- non_taut;

  let pf_env = pf_env_create () in 
  merge_defs qbf pf_env;
  reduce_vars_qbf qbf;
  let init_var_dep = get_var_dep qbf in 
  let cmp' = dep_cmp_fof pf_env init_var_dep in 
  let var_dep = (qbf_def_discovery ?cmp:(Some(cmp')) qbf pf_env init_var_dep) in
  let old_q_res_stat = Statistics.get_val_stat Statistics.qbf_q_res in
  q_resolve_qbf_dep qbf var_dep;
  let new_q_res_stat = Statistics.get_val_stat Statistics.qbf_q_res in
  if (old_q_res_stat != new_q_res_stat) 
  then 
    let new_var_dep = (qbf_def_discovery ?cmp:(Some(cmp')) qbf pf_env var_dep) in
    new_var_dep
  else
    var_dep
*)
