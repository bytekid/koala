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
open Prop_var
open Prop_env


(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_qres
  | D_split

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_qres -> "qres"
  | D_split -> "split"

let dbg_groups =
  [
   D_trace;  
   D_qres;
(*   D_split;*)
 ]

let module_name = "qbf_env"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


module PV  = Prop_var
module PVSet = Prop_var.VSet
module PVMap = Prop_var.VMap

module PE    = Prop_env
type pclause = PE.clause


type quant = A | E | D 

let quant_to_qdimacs q = 
  match q with 
  | A -> "a"
  | E -> "e"
  | D -> "d" (* dependency quantifier *)

let quant_to_string = quant_to_qdimacs

exception Not_quant
let qdimacs_to_quant str = 
  match str with 
  |"a" -> A 
  |"e" -> E
  |"d" -> D

  |_-> raise Not_quant

(* type quant_block = quant * var list *) 
type quant_block = 
    {
     qb_quant  : quant;
     mutable qb_vars   : VSet.t;
     qb_level  : int; (* for now level and id are the same; lineary ordered from left to right *)
     (* later level can be changed to non-linear tree like dependences *)
   }

let qb_get_var_list qb = VSet.elements qb.qb_vars

let qb_is_empty qb = (qb.qb_vars == VSet.empty)

let qb_remove_var qb v = 
  qb.qb_vars <- VSet.remove v qb.qb_vars

(* TODO: clean up e/d vars !!! *)
let is_e_qb qb = (qb.qb_quant = E)
    
let is_a_qb qb = (qb.qb_quant = A) 

let is_d_qb qb = (qb.qb_quant = D) 

(*
  let quant_block_to_qdimacs qb =  
  ((quant_to_qdimacs qb.qb_quant)^" "^(var_list_to_string_0 (qb_get_var_list qb.qb_vars)))
 *)

let out_qb qb = 
  print_string (quant_to_qdimacs qb.qb_quant);
  print_string " ";
  out_str (var_list_to_string_0 (qb_get_var_list qb))

(* type quant_pref = quant_block list *)

type quant_pref = quant_block IntMap.t (* indexed by levels *)

(*
  type qbf_cnf = 

  {
  mutable quant_pref : quant_pref; 
  mutable qbf_clauses : clause list;
  }
 *)

(*
  type qbf_cnf = 

  {
  mutable quant_pref : quant_pref; 
  mutable qbf_clauses : clause list;
  }
 *)

type qbf_cnf = 
    {
     mutable qbf_pref : quant_pref; 
     mutable qbf_clauses : pclause list;
     mutable qbf_var_level : (int * quant) VMap.t; (* maps vars to level *)
     mutable qbf_vars : VSet.t;     
     (*  (qdimacs allows to have "free vars" which are implicitly outer-existentialy quantified) *)
     (* after parsing we create an existential qb of level 0 for such vars *)

(* TODO: currently inner Skolemization only makes sense without dvars; extend inner Skolemization with dvars*)
     mutable qbf_dvar_map : VSet.t VMap.t; (* map for dependency d vars -> a vars on which e depends *)
   }


let create_qbf_cnf () = 
  {
   qbf_pref = IntMap.empty;
   qbf_clauses = [];
   qbf_var_level = VMap.empty;
   qbf_vars = VSet.empty;
   qbf_dvar_map = VMap.empty;
 }

    
    
let add_qb_to_qbf qbf qb = 
  qbf.qbf_pref <- IntMap.add qb.qb_level qb qbf.qbf_pref;
  let add_var var = 
    qbf.qbf_var_level <- VMap.add var (qb.qb_level,qb.qb_quant) qbf.qbf_var_level;
    qbf.qbf_vars <- VSet.add var qbf.qbf_vars
  in
  VSet.iter add_var qb.qb_vars 

let add_clause_to_qbf qbf cl =
  qbf.qbf_clauses <-  cl::(qbf.qbf_clauses)

let add_clause_list_to_qbf qbf clist =
  qbf.qbf_clauses <-  clist@(qbf.qbf_clauses)


(*----------------*)


(* qbf_get_var_qlevel returns (lvl, quant) *)
(* can raise Not_found *)
let qbf_get_var_qlevel qbf var = 
  VMap.find var qbf.qbf_var_level

let qbf_get_var_level qbf var = 
  let (lvl,_qb) = VMap.find var qbf.qbf_var_level in 
  lvl

(* TODO:fix: d vars *)
let qbf_get_var_quant qbf var = 
  let (_lvl,quant) = qbf_get_var_qlevel qbf var in 
  quant

(* can raise Not_found *)
let qbf_get_lvl_qb qbf lvl = 
  IntMap.find lvl qbf.qbf_pref

(* can raise Not_found *)
let qbf_get_var_lvl_qb qbf var = 
  let (lvl, quant) = qbf_get_var_qlevel qbf var in
  let qb = qbf_get_lvl_qb qbf lvl in 
  (lvl, quant, qb)

(* only use after the qbf is build and all free variables are explicitly in outer exitsts block *)

let qbf_is_e_var qbf var = 
  try 
   (not (VMap.mem var qbf.qbf_dvar_map)) && (qbf_get_var_quant qbf var) == E
  with
    Not_found -> failwith "qbf_is_e_var: var is not in qbf"

let qbf_is_a_var qbf var = 
  try 
   (not (VMap.mem var qbf.qbf_dvar_map)) && (qbf_get_var_quant qbf var) == A
  with
    Not_found -> failwith "qbf_is_a_var: var is not in qbf"
        
let qbf_is_d_var qbf var = 
    VMap.mem var qbf.qbf_dvar_map 

let qbf_is_d_or_e_var qbf var = 
  (qbf_is_d_var qbf var) || (qbf_is_e_var qbf var)

let qbf_var_in_qbf qbf var = PVSet.mem var qbf.qbf_vars

(* returns max variable used in qbf; relies on VSet is orderd by ids *)
let qbf_get_max_var qbf = 
  VSet.max_elt qbf.qbf_vars 

let qbf_get_max_lvl qbf = 
  let (lvl, qb) = IntMap.max_binding qbf.qbf_pref in 
  lvl

let qbf_get_max_lvl_qb qbf = 
  let (lvl, qb) = IntMap.max_binding qbf.qbf_pref in 
  (lvl,qb)


(*  var_prefix_split outputs (prefix_left, qb of v, quant, lvl, prefix_right) *)
(* can raise Not_found *)
let qbf_split_quant_pref qbf var =
  let (lvl,quant,var_qb) = qbf_get_var_lvl_qb qbf var in
  let (pref_left,_, pref_right) = IntMap.split lvl qbf.qbf_pref in
  (pref_left,var_qb,quant,lvl,pref_right)


(* removes var form qbf; the user should make sure that the var does not remain in clauses *)
let qbf_remove_var qbf var = 
  try 
    let (lvl, _quant, qb) = qbf_get_var_lvl_qb qbf var in
    qb_remove_var qb var;
    (if (qb_is_empty qb) 
    then 
      (qbf.qbf_pref <- IntMap.remove lvl qbf.qbf_pref) 
    else ()
    );
    qbf.qbf_var_level <- VMap.remove var qbf.qbf_var_level;
    qbf.qbf_vars <- VSet.remove var qbf.qbf_vars 
  with 
    Not_found -> ()

(*let out_quant_block quant_block = *)

let out_quant_pref qp = 
  IntMap.iter (fun _lvl qb -> out_qb qb) qp

let out_dvar_pref qbf = 
  VMap.iter 
    (fun dv avars -> out_str ("d "^(var_to_string dv)^" "^(var_list_to_string_0 (VSet.elements avars))))
    qbf.qbf_dvar_map
  
let out_qbf qbf =
  out_str ("c numf of quant blocks: "^(string_of_int (IntMap.cardinal qbf.qbf_pref)));
  out_str ("c numf of vars: "^(string_of_int (VSet.cardinal qbf.qbf_vars)));
  out_str ("c numf of clauses: "^(string_of_int (List.length qbf.qbf_clauses))^"\n");
  out_quant_pref qbf.qbf_pref;
  out_dvar_pref qbf;
  out_clause_list qbf.qbf_clauses


type qbf_var_dep = VSet.t VMap.t (* maps existential  variables to sets of variables on which they depend *)


(*---------- Parsing ------------------*)

(*let qdimacs_stdin () =  *)

let qbf_parse_in_channel channel_name in_channel =  
(*  let rec parse qbf_cnf =  *)
  let qbf = create_qbf_cnf () in
  let qb_level = ref 1 in (* we start from 1 and remaning "free" variables will be of level 0 *)
  let free_vset = ref VSet.empty in
  let declared_num_of_vars = ref 0 in (* does not match*)
  try
    while true
    do
      begin
	let rec first_non_comment_line () = 
	  let to_skip l =  
	    if l = "" then true 
	    else
	      let first_char =  String.get l 0 in		
              if (first_char = 'p')
              then
                (
                 let str_list = Str.split (Str.regexp "[ \t]+") l in
                 (
                  try 
                    declared_num_of_vars := int_of_string (List.nth str_list 2);
                    dbg D_trace (lazy ("num of declared vars: "^(string_of_int !declared_num_of_vars)));
                  with
                    Failure _ | Invalid_argument _ -> ()
                 );
                 true
                )
              else
	        (first_char = 'c') 
	  in
	  let l = input_line in_channel in
	  if (to_skip l)
	  then first_non_comment_line ()
	  else l 
	in
	let line =  first_non_comment_line () in      
	let str_list = Str.split (Str.regexp "[ \t]+") line in	  

(* raise Not_quant if not a quantified block *) 

        let parse_quant_block str_list = 
          match str_list with 
          |quant_str::tl -> 
              begin
               let quant = qdimacs_to_quant quant_str in 
               match quant with 
               | D -> 
                   let var_list = var_str_list_to_var_list_0 tl in
                   (match var_list with 
                   | h::tl -> 
                       (assert (not (VMap.mem h qbf.qbf_dvar_map));
                        qbf.qbf_vars <- VSet.union qbf.qbf_vars (VSet.of_list var_list);
                        qbf.qbf_dvar_map <- VMap.add h (VSet.of_list tl) qbf.qbf_dvar_map 
                       )
                   |[] -> failwith "d var list should not be empty"
                   )
               | A|E ->
                   begin         
                     let var_list = var_str_list_to_var_list_0 tl in 
                     let quant_block = 
                       {
                        qb_quant  = quant;
                        qb_vars   = VSet.of_list var_list;
                        qb_level  = !qb_level; (* for now level and id are the same; lineary ordered from left to right *)
                  (* later level can be changed to non-linear tree like dependences *)
                      }                 
                     in
                     add_qb_to_qbf qbf quant_block;
                     qb_level:=!qb_level+1;
                   end
              end
          |[] -> raise Not_quant
        in

        let parse_clause str_list = 
          let lit_list = lit_str_list_to_lit_list_0 str_list in 
          List.iter 
            (fun lit -> 
              let var = (get_var_lit lit) in 
              (if (not (VSet.mem var qbf.qbf_vars)) 
              then 
                free_vset := VSet.add (get_var_lit lit) !free_vset 
              )
            )
            lit_list;
	  let clause = clause_create lit_list P_Input in
          (if (is_empty_clause clause) 
          then
            raise (Unsatisfiable clause);
          );
          qbf.qbf_clauses <- clause::qbf.qbf_clauses
        in
        let parse_str str_list = 
          try 
            parse_quant_block str_list 
          with 
            Not_quant -> 
              parse_clause str_list 
        in
        parse_str str_list
      end
    done;
    qbf (* never happens *)
  with 
    End_of_file -> 
      (
       if (!free_vset = VSet.empty)
       then
         qbf
       else (* the are some free variables which are implicitely existentionally outer-quantified *)
         (
(*
(* TODO: merge if the outer quantifier block is already E *)
  let f free_var_set clause = 
  let lits = clause_get_lits clause in
  let vars = List.map get_var_lit lits in
  let g ext_fv_set var = 
  if (VSet.mem var qbf.qbf_vars) 
  then (* bound *)
  ext_fv_set
  else (* free *)
  VSet.add var ext_fv_set 
  in
  List.fold_left g free_var_set vars
  in
  let free_var_set = List.fold_left f VSet.empty qbf.qbf_clauses in          
 *)
          let quant_block = 
            {
             qb_quant  = E;
             qb_vars   = !free_vset;
             qb_level  = 0; (* outer_most block*)
           }                 
          in
          add_qb_to_qbf qbf quant_block;
          qbf
         )
      )

        
let qbf_parse_stdin () =
  let channel_name = "stdin" in 
  qbf_parse_in_channel channel_name stdin
    

(*--------------- q-resolve ----------------*)

(* can raise Eliminated *)
let q_resolve_clause qbf c = 
  let lits = clause_get_lits c in
  (if (is_tautology c)
  then
    (Statistics.incr_int_stat 1 Statistics.qbf_num_tautologies;
     raise Eliminated)
  );
  let max_e_lvl = ref 0 in 
  let e_list = ref [] in 
  let a_list = ref [] in 
  let f lit = 
    let var = get_var_lit lit in
    let (level,quant) = 
      try
        qbf_get_var_qlevel qbf var 
      with 
        Not_found -> failwith "q_resolve: var is not in qbf"
    in
    if (quant = E)
    then
      (
       e_list := (level,lit)::!e_list;
       (if level > !max_e_lvl 
       then
         (max_e_lvl:=level)
       ) 
      )
    else
      (
       a_list:= (level,lit)::!a_list
      )
  in
  List.iter f lits;
  let g a_rest (level,a_lit) = 
    if (level > !max_e_lvl) 
    then (* remove this lit *)
      (a_rest)
    else (* keep *)
      (a_lit::a_rest)
  in
  let a_lits_remain = List.fold_left g [] !a_list in 
  if ((List.length a_lits_remain) != (List.length !a_list))
  then (* some lits got eliminated *)    
    (* TODO: remove a_var if it got eliminated from all clauses containing it *)
    let (_,e_lits) = List.split !e_list in 
    let new_lits = a_lits_remain@e_lits in 
    let new_clause = clause_create new_lits (Q_Res c) in 
    Statistics.incr_int_stat 1 Statistics.qbf_q_res;
    dbg D_qres (lazy ((clause_to_string new_clause)^" <- "^(clause_to_string c)));
    (if (is_empty_clause new_clause) 
    then
      raise (Unsatisfiable new_clause);
    );
    new_clause
  else
    c

      
let qbf_q_resolve qbf = 
  let f cl_list cl = 
    try 
      (q_resolve_clause qbf cl)::cl_list
    with 
      Eliminated -> cl_list
  in
  let new_clause_list = List.fold_left f [] qbf.qbf_clauses in
  qbf.qbf_clauses <- new_clause_list

(*----------- splitting -------------*)

type sp_cl_part = (lit list) list 

let partion_lits part_size lits =
  list_partition part_size lits 

(*let create_split_clauses max_var part_ll = *)
let split_clause_once max_var sp_part_size lits (* parent_cl*) = (* TODO: add parents *) 
  let part_ll = partion_lits sp_part_size lits in 
  assert (not (part_ll == []));
  let f (cur_var, split_vars, split_def_cls) part_lits = 
    let sp_var = make_var ((get_var_id cur_var) + 1) in 
    let sp_lit = var_to_lit false sp_var in (* ~sp \/ C *)
    let sp_clause = clause_create (sp_lit::part_lits) P_Input in (* TODO: change P_Input to P_Split *)
    (sp_var, sp_var::split_vars, (sp_clause::split_def_cls))
  in  
  let (new_max_var, sp_vars, sp_def_cls) = List.fold_left f (max_var, [], []) part_ll in 
  (* let sp_pos_cl = clause_create (List.map (var_to_lit true) sp_vars) P_Input in*) (* TODO: change P_Input to P_Split *)
  (new_max_var, sp_vars, sp_def_cls)

(*
  let split_clause_once max_var sp_part_size cl = 
  let parts = partion_clause sp_part_size cl in 
  create_split_clauses max_var parts 
 *)

let split_clause qbf max_var sp_part_size cl = 
  assert (sp_part_size >= 2);
  (* split recursively until sp_pos_cl size is less than sp_part_size *)
  let rec f curr_max_var curr_sp_vars lits_to_split sp_def_cls = 
(*    *)
    if (List.length lits_to_split) < 2*sp_part_size 
    then 
      (curr_max_var, curr_sp_vars, lits_to_split, sp_def_cls)
    else
      let (new_max_var, sp_cl_vars, next_sp_def_cls) = split_clause_once curr_max_var sp_part_size lits_to_split in 
      let new_sp_def_cls = next_sp_def_cls@sp_def_cls in
      let new_sp_vars = sp_cl_vars@curr_sp_vars in
      let new_lits_to_split = List.map (var_to_lit true) sp_cl_vars in
      f new_max_var new_sp_vars new_lits_to_split new_sp_def_cls      
  in
  let lits_to_sp = clause_get_lits cl in
  let (e_lits,a_lits) = List.partition (fun lit -> (qbf_is_e_var qbf (get_var_lit lit))) lits_to_sp in
  let (new_max_var, sp_vars, lits_remainder, sp_def_clauses) = f max_var [] lits_to_sp [] in
  let pos_and_a_lits = lits_remainder@a_lits in 
  let sp_pos_cl = clause_create pos_and_a_lits P_Input in (* TODO: change P_Input to P_Split *)
  let sp_clauses = sp_pos_cl::sp_def_clauses in
  (new_max_var, sp_vars, sp_clauses)

let split_clause_list qbf max_var sp_part_size cl_list = 
  let f (curr_max_var,sp_vars_rest, sp_rest) cl = 
    let (new_max_var, sp_cl_vars, sp_clauses) = split_clause qbf curr_max_var sp_part_size cl in
    (new_max_var, sp_cl_vars@sp_vars_rest, (sp_clauses@sp_rest))
  in
  List.fold_left f (max_var,[],[]) cl_list 
    
let qbf_split_clauses sp_part_size qbf  = 
  if (qbf.qbf_clauses == []) 
  then
    () (* empty qbf *)
  else
    begin
      let max_var = qbf_get_max_var qbf in
      let (max_lvl, max_qb) = qbf_get_max_lvl_qb qbf in
      let (_new_max_var, sp_vars, sp_clauses) = split_clause_list qbf max_var sp_part_size qbf.qbf_clauses in 
      let quant_block = 
        if (max_qb.qb_quant == E) 
        then
          {
           qb_quant  = E;
           qb_vars   = VSet.union (VSet.of_list sp_vars) max_qb.qb_vars;
           qb_level  = max_qb.qb_level; (* outer_most block*)
         }
        else 
          {
           qb_quant  = E;
           qb_vars   = VSet.of_list sp_vars;
           qb_level  = max_lvl+1; (* outer_most block*)
         }                 
      in
      add_qb_to_qbf qbf quant_block;
      dbg D_split (lazy ("Clauses after splitting:\n"));
      dbg_env D_split 
        (fun () -> (out_clause_list sp_clauses));
      qbf.qbf_clauses <-  sp_clauses
    end
      
      
      

(*---- var dependencies ------------*)

let out_var_dep var_dep = 
  let f v vset = 
    let vlist = VSet.elements vset in
    print_string (var_to_string v);
    print_string " -> ";
    out_str (var_list_to_string vlist);
    out_str ""
  in
  out_str "c ------- var depend map --------\n";
  VMap.iter f var_dep;
  out_str "c ----- end var depend map ------\n"


let get_var_dep var_dep var = 
  try 
    VMap.find var var_dep 
  with 
    Not_found -> VSet.empty

(*----------------outer dep ------------------*)

(* returns updated var_dep map: var-> v_set  *)
let outer_add_var_dep qbf lvl qb var_dep =   
  if (is_e_qb qb)
  then
    let (pref_left, _, pref_right) = IntMap.split lvl qbf.qbf_pref in
    let collect_a_set _lvl left_qb rest = 
      if (is_a_qb left_qb)
      then 
        (VSet.union left_qb.qb_vars rest)
      else
        rest
    in
(* all vars in qb have the same dep set *)
    let dep_var_set = IntMap.fold collect_a_set pref_left VSet.empty in
    (* add for each var in qb dep_var_set as dep set *)
    let f e_var curr_var_dep = VMap.add e_var dep_var_set curr_var_dep in 
    VSet.fold f qb.qb_vars var_dep 
  else
    var_dep (*A qb; do not do anything *)

let qbf_outer_var_dep qbf = 
  let e_var_out_dep = 
    IntMap.fold (outer_add_var_dep qbf) qbf.qbf_pref VMap.empty
  in
  let var_dep = VMap.union (fun  _ -> failwith "e and d vars should not be mixed") e_var_out_dep qbf.qbf_dvar_map in 
  var_dep


(*--------- inner dependences --------*)

type var_to_clauses = (clause list) VMap.t

(* we do not need to include d vars here *)
let get_e_var_to_clauses_map qbf = 
  let process_clause vmap clause = 
    let lits = clause_get_lits clause in
    let f vmap_rest lit = 
      let var = get_var_lit lit in                              
      if (qbf_is_e_var qbf var)
      then
        let old_cl_list =
          try 
            VMap.find var vmap_rest
          with 
            Not_found -> []      
        in
        let new_cl_list = clause::old_cl_list in 
(*        dbg D_trace (lazy (("get_e_var_to_clauses_map: var: "
          ^" var "^(var_to_string var)
          ^" new_cl_list: "^(clause_list_to_string new_cl_list)))
          ); 
 *)
        VMap.add var new_cl_list vmap_rest  
      else
        vmap_rest
    in
    List.fold_left f vmap lits
  in
  List.fold_left process_clause VMap.empty qbf.qbf_clauses

(* local a_cloud: an A var_a is in a local cloud of an v_e if there is a clause in which both v_a and v_e occur 
   and lvl_v_a > lvl_v_e *)
(* lcl_a_cloud: v_e -> v_a_set  *)

(* v_e1 ~ v_e2  using e_uf if v_e1 is connected via cluase connection to v_e2; here levels can be mixed *)


let get_lcl_a_cloud_and_e_uf qbf e_var_to_clauses = 
  let e_uf = VUF.create 50 in 

  let process_clause_set e_var clause_set lcl_a_cloud_rest =     
    VUF.add e_uf e_var;
    let e_var_lvl = qbf_get_var_level qbf e_var in

    let process_clause e_var_a_dep_set clause =       
      let lits = clause_get_lits clause in    
      
      let f e_var_a_dep_set_rest c_lit = 
        let c_var = get_var_lit c_lit in 
        let (c_v_lvl, c_v_q) = qbf_get_var_qlevel qbf c_var in 
        dbg D_trace (lazy (("get_lcl_a_cloud_and_e_uf: c_var: ")
                           ^(var_to_string c_var)
                           ^" c_v_lvl: "^(string_of_int c_v_lvl)
                           ^" quant: "^(quant_to_string c_v_q)));
        match c_v_q with 
        |E ->
            (
             VUF.add e_uf c_var;
             VUF.union e_uf c_var e_var;
             e_var_a_dep_set_rest
            )
        |A ->
            if (c_v_lvl < e_var_lvl)
            then 
              VSet.add c_var e_var_a_dep_set_rest
            else
              e_var_a_dep_set_rest
        |D ->
  (* do not need to add dvar into e_uf *)
            VSet.union e_var_a_dep_set_rest (VMap.find c_var qbf.qbf_dvar_map)
(* failwith "dvars are not suppored in inner deps" *)
      in
      List.fold_left f e_var_a_dep_set lits
    in
    let e_var_a_dep_set = List.fold_left process_clause VSet.empty clause_set in 
    let new_lcl_a_cloud = VMap.add e_var e_var_a_dep_set lcl_a_cloud_rest in
    new_lcl_a_cloud 
  in
  let lcl_a_cloud = VMap.fold process_clause_set e_var_to_clauses VMap.empty in 
  (e_uf, lcl_a_cloud)


(* first compute var deps for nomral forms in e_uf; we restict levels of a_vars later  *)
let norm_uf_var_dep e_uf lcl_a_cloud = 
  let norm_glb_a_cloud_map = ref lcl_a_cloud in
  let f var norm_var = 
    let old_norm_a_dep_set = get_var_dep !norm_glb_a_cloud_map norm_var in
    let var_a_dep_set = get_var_dep !norm_glb_a_cloud_map var in
    let new_norm_a_dep_set = VSet.union var_a_dep_set old_norm_a_dep_set in 
    norm_glb_a_cloud_map := VMap.add norm_var new_norm_a_dep_set !norm_glb_a_cloud_map
  in
  VUF.iter f e_uf;
  !norm_glb_a_cloud_map

let get_glb_a_cloud e_uf lcl_a_cloud =
  let norm_a_cloud = norm_uf_var_dep e_uf lcl_a_cloud in 
  let f var _old_dep_set dep_map = 
    let norm_var = 
      try
        VUF.find e_uf var 
      with 
        Not_found ->
          var (* some vars occur in quant prefix but not in the clauses... *)
    in 
    let new_dep_set = get_var_dep norm_a_cloud norm_var in
    VMap.add var new_dep_set dep_map
  in
  VMap.fold f norm_a_cloud norm_a_cloud


let reduce_glb_a_cloud outer_dep glb_a_cloud = 
  let f v_e v_e_glb_set_old curr_reduced_glb_a_cloud = 
    let outer_dep_set = get_var_dep outer_dep v_e in 
    let glb_a_dep_set = get_var_dep glb_a_cloud v_e in 
    let new_dep_set = VSet.inter outer_dep_set glb_a_dep_set in 
    let new_reduced_glb_a_cloud = VMap.add v_e new_dep_set curr_reduced_glb_a_cloud in     
    new_reduced_glb_a_cloud
  in
  VMap.fold f glb_a_cloud VMap.empty

    

let qbf_inner_var_dep_old qbf = 
  let e_var_to_clauses = get_e_var_to_clauses_map qbf in
  let (e_uf,lcl_a_cloud) = get_lcl_a_cloud_and_e_uf qbf e_var_to_clauses in 
  let glb_a_cloud = get_glb_a_cloud e_uf lcl_a_cloud in 
  let outer_dep = qbf_outer_var_dep qbf in
  let e_var_dep = reduce_glb_a_cloud outer_dep glb_a_cloud in
  let var_dep = VMap.union (fun  _ -> failwith "e and d vars should not be mixed") e_var_dep qbf.qbf_dvar_map in 
  dbg_env D_trace 
    (fun () ->
      out_str "\n";
      out_str "Inner dep var map: ";
      out_var_dep var_dep       
    );  
  var_dep


(*------------- reduced graph inner var dep. ----------*)

(* level var *)
module LVarKey =  
  struct  
    type t = int * var
(*    let compare (lvl1, v1) (lvl2, v2) = lex_combination [Pervasives.compare; Pervasives.compare]      *)
    let compare = Pervasives.compare     
    let equal (lvl1, v1) (lvl2, v2) = (lvl1 = lvl2) && ((PV.get_var_id v1) = (PV.get_var_id v2))
    let hash (lvl, v) = (lvl lsl 6) + (get_var_id v)
  end

module LVUF = Union_find.Make(LVarKey)
module LVMap = Map.Make(LVarKey)
module LVSet = Set.Make(LVarKey)

(*
type labelled_node = 
    {
     lbl_var : PV.var;
     lbl_a_set : PVSet.t
   }
*)

type labelled_graph = 
    {
     mutable lg_labels : LVSet.t PVMap.t;
     mutable lg_adj : LVSet.t LVMap.t;
   }
      
let create_lg () = 
  {
   lg_labels = PVMap.empty;
   lg_adj    = LVMap.empty;
 }

let lg_add_edge lg v1 v2 = 
  let old_adj_set = 
    try 
      LVMap.find v1 lg.lg_adj
    with 
      Not_found -> LVSet.empty
  in
  let new_adj_set = LVSet.add v2 old_adj_set in 
  lg.lg_adj <- LVMap.add v1 new_adj_set lg.lg_adj

(* resturns PVSet.empty if  Not_found *)
let lg_get_lbl lg v = 
  try
    PVMap.find v lg.lg_labels 
  with 
    Not_found -> LVSet.empty

let lg_get_adj_set lg v = 
  try
    LVMap.find v lg.lg_adj 
  with 
    Not_found -> LVSet.empty

let lg_assign_lbl lg v label = 
  lg.lg_labels <- PVMap.add v label lg.lg_labels 

let lg_assign_adj_set lg v adj_set = 
  lg.lg_adj <- LVMap.add v adj_set lg.lg_adj

let lg_add_var_lbl lg v a_v = 
  let old_lbl = 
    try 
      PVMap.find v lg.lg_labels 
    with 
      Not_found -> LVSet.empty
  in
  let new_lbl = LVSet.add a_v old_lbl in
  lg.lg_labels <-  PVMap.add v new_lbl lg.lg_labels
      

exception LVL_equal

(* can raise LVL_equal *)
let order_lvl_var (lvl1,v1) (lvl2,v2) = 
  if (lvl1 < lvl2) 
  then  
  ((lvl1,v1), (lvl2,v2))
  else
    if (lvl2 < lvl1)
    then
      ((lvl2,v2), (lvl1,v1))
    else
      raise LVL_equal


(*
  let add_lvl_ordered_edge lg (lvl1,v1) (lvl2,v2) = 
  let ((r_lvl, r_v), (l_lvl, l_v)) = order_lvl_var (lvl1, v1) (lvl2, v2) in (* from larger lvl to smaller *)
  lg_add_edge lg l_v r_v
 *)


(* TODO: merge with get_lcl_a_cloud_and_e_uf where lvl are not taken into account *)
let get_init_lg_and_e_luf qbf e_var_to_clauses = 
  let e_uf = LVUF.create 50 in 
  let lg = create_lg () in 
  let process_clause_set e_var clause_set (* lcl_a_cloud_rest *) =     
    let e_var_lvl = qbf_get_var_level qbf e_var in
    let e_lv = (e_var_lvl,e_var) in
    LVUF.add e_uf e_lv;

    let process_clause e_var_a_dep_set clause =       
      let lits = clause_get_lits clause in    
      
      let f e_var_a_dep_set_rest c_lit = 
        let c_var = get_var_lit c_lit in 

        if (qbf_is_d_var qbf c_var) 
        then 
          e_var_a_dep_set_rest
        else
          begin
            let (c_v_lvl, c_v_q) = qbf_get_var_qlevel qbf c_var in 
            let c_lv = (c_v_lvl, c_var) in
            dbg D_trace (lazy (("get_lcl_a_cloud_and_e_luf: c_var: ")
                               ^(var_to_string c_var)
                               ^" c_v_lvl: "^(string_of_int c_v_lvl)
                               ^" quant: "^(quant_to_string c_v_q)));
            match c_v_q with 
            |E ->
                if (e_var_lvl = c_v_lvl)
                then 
                  (LVUF.add e_uf c_lv;
                   LVUF.union e_uf c_lv e_lv;
                   e_var_a_dep_set_rest
                  )
                else
                  (
                   lg_add_edge lg e_lv c_lv;
                   e_var_a_dep_set_rest
                  )
            |A ->
                if (c_v_lvl < e_var_lvl)
                then 
                  LVSet.add c_lv e_var_a_dep_set_rest
                else
                  e_var_a_dep_set_rest

            |D -> 
(* do not need to add dvar into e_uf *)
                let c_var_dep_set = VMap.find c_var qbf.qbf_dvar_map in
                let f a_dep_var rest = 
                  LVSet.add ((qbf_get_var_level qbf a_dep_var), a_dep_var) rest 
                in
                VSet.fold f c_var_dep_set e_var_a_dep_set_rest
(* failwith "dvars are not suppored in inner deps" *)
          end
      in
      List.fold_left f e_var_a_dep_set lits
    in
    let e_var_a_dep_set = List.fold_left process_clause LVSet.empty clause_set in 
    lg_assign_lbl lg e_var e_var_a_dep_set;
  in
  VMap.iter process_clause_set e_var_to_clauses;
  (e_uf,lg)

(*---move to prop_var *)
let lvset_map f lvset = 
  let g el rest_set = 
    LVSet.add (f el) rest_set
  in
  LVSet.fold g lvset LVSet.empty

(* norm_lg between nomral froms in e_uf *)
let norm_lg e_uf lg = 
  let norm_lg = create_lg () in
  let f ((lvl,var) as lv) ((norm_lvl,norm_var) as lnv) = 
    assert (lvl = norm_lvl);
(* new label *)
    let old_norm_lbl = lg_get_lbl norm_lg norm_var in
    let var_lgl_lbl  = lg_get_lbl lg var in
    let new_nrom_lbl = LVSet.union old_norm_lbl var_lgl_lbl in
    lg_assign_lbl norm_lg norm_var new_nrom_lbl;

(* new connections *)
    let old_adj_set = lg_get_adj_set norm_lg lnv in 
    let var_adj_set = lvset_map (LVUF.find e_uf) (lg_get_adj_set lg lv) in (* normalise adjs of var *)
    let new_adj_set = LVSet.union old_adj_set var_adj_set in
    lg_assign_adj_set norm_lg lnv new_adj_set
  in
  LVUF.iter f e_uf;
  norm_lg
  
(* leo - labelling expansion *)
let lg_norm_leo lg ((lvl1,v1) as lv1) ((lvl2,v2) as lv2) =
  try 
    let ((lvl_s,v_s), (lvl_g,v_g)) = order_lvl_var lv1 lv2 in
    assert (lvl_s < lvl_g);
    let old_lbl_s = lg_get_lbl lg v_s in
    let old_lbl_g = lg_get_lbl lg v_g in
    let new_lbl_g = LVSet.union old_lbl_g old_lbl_s in
    lg_assign_lbl lg v_g new_lbl_g;
    let new_lbl_s = 
      let lbl_g_filtered = LVSet.filter (fun (lvl,v) -> lvl < lvl_s) old_lbl_g in      
      LVSet.union lbl_g_filtered old_lbl_s 
    in
    lg_assign_lbl lg v_s new_lbl_s;
  with 
    LVL_equal-> 
      (
       assert (lvl1 = lvl2);
       let new_lbl = LVSet.union (lg_get_lbl lg v1) (lg_get_lbl lg v2) in
       lg_assign_lbl lg v1 new_lbl;
       lg_assign_lbl lg v2 new_lbl;
      )

(* med -- minimal e-dependency graph *)
let lg_norm_med norm_lg = 
  let all_e_norm_lvars = 
    let f e_lvar _lbl e_lvars_rest = 
      e_lvar::e_lvars_rest
    in
    LVMap.fold f norm_lg.lg_adj [] 
  in
  let rec main p q = 
    match q with 
    | ((lvl,var) as lv)::q_tl -> 
        let adj_set = lg_get_adj_set norm_lg lv in 
        let p_restricted_adj_set = LVSet.inter adj_set p in
        let process_adj_nodes ((adj_lvl,adj_v) as adj_node) (p_rest, q_rest)= 
          let old_adj_lbl_size = LVSet.cardinal (lg_get_lbl norm_lg adj_v) in
          lg_norm_leo norm_lg 
            lv 
            adj_node;
          let new_adj_lbl_size = LVSet.cardinal (lg_get_lbl norm_lg adj_v) in
          let (new_p, new_q) = 
            if (not (old_adj_lbl_size = new_adj_lbl_size))
            then              
              (LVSet.remove adj_node p_rest,  adj_node::q_rest)
            else
              (p_rest,q_rest)
          in
          (new_p, new_q)
        in
        let (p_adj,new_q) = LVSet.fold process_adj_nodes p_restricted_adj_set (p,q_tl) in
        let new_p = LVSet.add lv p_adj in
        main new_p new_q
    | [] -> ()
  in
  main LVSet.empty all_e_norm_lvars


let strip_lvl_lvset lvset = 
  let f (_lvl,v) rest_v_set = 
    PVSet.add v rest_v_set
  in
  LVSet.fold f lvset PVSet.empty

let lg_get_var_dep_norm_lg norm_lg e_luf =
  let var_dep_lvl = ref VMap.empty in 
  let f (_lvl_v, var) (_lvl_norm,var_norm) =    
    let norm_lbl = lg_get_lbl norm_lg var_norm in
    var_dep_lvl:= VMap.add var norm_lbl !var_dep_lvl
  in
  LVUF.iter f e_luf;
  let var_dep = PVMap.map strip_lvl_lvset !var_dep_lvl in
  var_dep


let lg_get_var_dep qbf = 
 let e_var_to_clauses = get_e_var_to_clauses_map qbf in 
 let (e_luf, lg) = get_init_lg_and_e_luf qbf e_var_to_clauses in
 let norm_lg = norm_lg e_luf lg in 
 lg_norm_med norm_lg;
 let e_var_dep = lg_get_var_dep_norm_lg norm_lg e_luf in 
 let var_dep = VMap.union (fun  _ -> failwith "e and d vars should not be mixed") e_var_dep qbf.qbf_dvar_map in 
 dbg_env D_trace 
    (fun () ->
      out_str "\n";
      out_str "Inner labelled graph dep var map: ";
      out_var_dep var_dep       
    );  
 var_dep
 
let qbf_inner_var_dep qbf = 
(*  assert (VMap.is_empty qbf.qbf_dvar_map); *)
  lg_get_var_dep qbf 

(*------------- OLD ----------*)
(*
(*------ inner inter_level -------*)
  let inner_collect_e_dep_vars_inter_lvl qbf var_to_cl_map var_dep_map lvl var = 
  let collect_e_dep_vars_clause e_dep_vars clause = 
  let lits = clause_get_lits clause in
  let f e_dep_vars_rest c_lit = 
  let c_var = get_var_lit c_lit in 
  let (c_v_lvl, c_v_q) = qbf_get_var_qlevel qbf c_var in 
  dbg D_trace (lazy (("inner_collect_e_dep_vars_inter_lvl: c_var: ")
  ^(var_to_string c_var)
  ^" c_v_lvl: "^(string_of_int c_v_lvl)
  ^" quant: "^(quant_to_string c_v_q)));
  if (c_v_lvl < lvl) 
  then
  if (c_v_q == A) 
  then
  VSet.add c_var e_dep_vars_rest
  else
  (
  try 
  let c_v_dep = VMap.find c_var var_dep_map in
  VSet.union c_v_dep e_dep_vars_rest
  with 
  Not_found -> e_dep_vars_rest
  )
  else
  e_dep_vars_rest
  in
  List.fold_left f e_dep_vars lits
  in
  let clause_list = 
  try 
  VMap.find var var_to_cl_map
  with 
  Not_found -> []
  in
  dbg D_trace (lazy (("inner_collect_e_dep_vars_inter_lvl: var "
  ^(var_to_string var)
  ^" clause_list: "
  ^(clause_list_to_string clause_list))));     
  List.fold_left collect_e_dep_vars_clause VSet.empty clause_list

  let var_set_to_string vset =
  let vlist = VSet.elements vset in 
  list_to_string var_to_string vlist " "



  let inner_add_var_dep_inter_lvl qbf var_to_cl_map lvl qb var_dep_map =   
  if (is_e_qb qb)
  then
  let f var var_dep_map_rest = 
  let var_dep_set = inner_collect_e_dep_vars_inter_lvl qbf var_to_cl_map var_dep_map_rest lvl var in
  dbg D_trace (lazy ("inner_add_var_dep_inter_lvl: var:"
  ^(var_to_string var)
  ^" lvl:"^(string_of_int lvl)
  ^" var_dep_set: "^(var_set_to_string var_dep_set)));
  VMap.add var var_dep_set var_dep_map_rest
  in
  VSet.fold f qb.qb_vars var_dep_map     
  else
  var_dep_map (*A qb; do not do anything *)


  
(*------ inner eq_level -------*)


  let get_e_union_find_lvl_map_eq_lvl qbf =   
  let process_clause uf_lvl_map clause = 
  (* use a map:  lvl_normv_map: lvl -> e_var within the clause and uf every other var of the the same lvl *)
  (* lvl_normv_map is local for each clause *)
  let lits = clause_get_lits clause in
  let f (curr_uf_lvl_map, curr_lvl_normv_map) lit = 
  let var = get_var_lit lit in
  let (lvl, quant) = qbf_get_var_qlevel qbf var in
  if (quant == E)
  then
  begin
  let lvl_uf = 
  try 
  IntMap.find lvl curr_uf_lvl_map
  with 
  Not_found -> VUF.create 50  
  in
  VUF.add lvl_uf var;
  let lvl_norm_var =             
  try 
  IntMap.find lvl curr_lvl_normv_map 
  with 
  Not_found -> var
  in
  VUF.union lvl_uf var lvl_norm_var;
  let new_uf_lvl_map = IntMap.add lvl lvl_uf curr_uf_lvl_map in 
  let new_lvl_normv_map = IntMap.add lvl lvl_norm_var curr_lvl_normv_map in 
  (new_uf_lvl_map, new_lvl_normv_map)
  end
  else
  (curr_uf_lvl_map, curr_lvl_normv_map) 
  in
  let (new_uf_lvl_map,_new_lvl_normv_map) = List.fold_left f (uf_lvl_map,IntMap.empty) lits in
  new_uf_lvl_map
  in
  let uf_lvl_map = List.fold_left process_clause IntMap.empty qbf.qbf_clauses in
  uf_lvl_map

(* first computer var deps for nomral forms in uf_eq_lvl *)
  let norm_uf_var_dep uf var_dep_inter_lvl = 
  let norm_dep_map = ref var_dep_inter_lvl in
  let f var norm_var = 
  let old_norm_dep_set = 
  try 
  VMap.find norm_var !norm_dep_map
  with
  Not_found -> 
  (
  let norm_dep_set_inter_lvl = get_var_dep var_dep_inter_lvl norm_var in
  norm_dep_set_inter_lvl
  )
  in
  let var_dep_set_inter_lvl = get_var_dep var_dep_inter_lvl var in
  let new_norm_dep_set = VSet.union var_dep_set_inter_lvl old_norm_dep_set in 
  norm_dep_map := VMap.add norm_var new_norm_dep_set !norm_dep_map
  in
  VUF.iter f uf;
  !norm_dep_map

  let var_dep_inter_to_var_dep uf var_dep_inter_lvl =
  let norm_dep_map = norm_uf_var_dep uf var_dep_inter_lvl in 
  let f var _old_dep_set dep_map = 
  let norm_var = 
  try
  VUF.find uf var 
  with 
  Not_found ->
  var (* some vars occur in quant prefix but not in the clauses... *)
  in 
  let new_dep_set = get_var_dep norm_dep_map norm_var in
  VMap.add var new_dep_set dep_map
  in
  VMap.fold f var_dep_inter_lvl norm_dep_map

(*----inner main ---*)

  

  let qbf_inner_var_dep qbf = 
  let var_to_cl_map = get_e_var_to_clauses_map qbf in
  let uf_lvl_map = get_e_union_find_lvl_map_eq_lvl qbf in
  let f lvl qb var_dep_map = 
  let inter_lvl_processed_map = inner_add_var_dep_inter_lvl qbf var_to_cl_map lvl qb var_dep_map in
  let uf = 
  try 
  IntMap.find lvl uf_lvl_map
  with 
  Not_found -> VUF.create 50 (* should not really happen *)
  in
  let in_lvl_processed_map = var_dep_inter_to_var_dep uf inter_lvl_processed_map in 
  in_lvl_processed_map
  in
  let var_dep = IntMap.fold f qbf.qbf_pref VMap.empty in
  dbg_env D_trace 
  (fun () ->
  out_str "\n";
  out_str "Inner dep var map: ";
  out_var_dep var_dep       
  );
  var_dep

(*
  let var_dep_inter_lvl = qbf_inner_var_dep_inter_lvl qbf in 
  dbg_env D_trace 
  (fun () ->
  out_str "\n";
  out_str "Inner dep var inter lvl  map:\n\n ";
  out_var_dep var_dep_inter_lvl       
  );
  
  let var_dep = var_dep_inter_to_var_dep uf var_dep_inter_lvl in 
  dbg_env D_trace 
  (fun () ->
  out_str "\n";
  out_str "Inner dep var map: ";
  out_var_dep var_dep       
  );
  var_dep
 *)

 *)

(* debug *)
(*
  let _ = 
  let num_list_str nlist = list_to_string string_of_int nlist "," in 
  let num_list_list_str nll = list_to_string num_list_str nll ";" in 
  let part_list = list_partition 5 [1;2;3;4;5;6;7;8;9;10;11] in 
  out_str ("part_list: "^(num_list_list_str part_list))
 *)



(*-------------*)
let qbf_cnf_test_parser () = 
  let qbf = qbf_parse_stdin () in     
  qbf_q_resolve qbf;
(*
  out_str ("c preprocessed qbf\n");
  out_qbf qbf;
  out_str ("c preprocessed qbf\n");
 *)
  let var_dep = qbf_outer_var_dep qbf in 
  out_var_dep var_dep

(*
  let q_resolution qbf= 
 *)
(*--------dependences --------*)


(* returns var_dep *)
(* let get_outer_dep qbf = *)
    
