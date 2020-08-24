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
open Statistics
open Options

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace


let dbg_gr_to_str = function 
  | D_trace -> "trace"

let dbg_groups =
  [
   D_trace;
 ]
    
let module_name = "propSolver"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)


exception Create_lit_error

(*
type solver_name   = MiniSat | ZChaff
let current_solver = MiniSat
*)

type solver_out = Sat  | Unsat
(* used in unsta_test:  AUnsat unsat under assumptions*)
type fast_solve = FSat | FUnsat | FUnknown
type lit_val    = True | False | Any
type lit_sign   = Pos  | Neg
type var_id = int

(*
module SatSolver = CMinisat 
*)

module SatSolver =  Minisat (* CMinisat *)   (* in src/cMinisat.ml *) (* can also use Minisat (c++ version as in proof extraction) *)



module SatSolverUC = Minisat  (* in util/src/minisat.ml *)


type lit = SatSolver.literal

type lit_uc = SatSolverUC.literal

type solver = SatSolver.solver

type solver_uc = SatSolverUC.solver

let lit_var solver lit = SatSolver.lit_var solver lit
    
let lit_sign solver lit = SatSolver.lit_sign solver lit

let lit_var_uc solver lit = SatSolverUC.lit_var solver lit
    
let lit_sign_uc solver lit = SatSolverUC.lit_sign solver lit

(* to_strings *)

let pp_lit = SatSolver.pp_literal 

let pp_lit_dimacs = pp_lit 

let rec pp_lit_list_dimacs solver ppf = function
  | [] -> 
    Format.fprintf ppf "0"
  | l::tl -> 
    Format.fprintf ppf "%a " (pp_lit_dimacs solver) l; 
    pp_lit_list_dimacs solver ppf tl
    
let lit_to_string solver lit = 
  SatSolver.literal_to_string solver lit

let lit_uc_to_string solver_uc lit_uc = 
  SatSolverUC.literal_to_string solver_uc lit_uc


let lit_list_to_string solver lit_list = 
(* in DIMACS format *)
  ( (Lib.list_to_string (lit_to_string solver) lit_list " ")^" 0")

let lit_uc_list_to_string solver_uc lit_uc_list = 
(* in DIMACS format *)
  ( (Lib.list_to_string (lit_uc_to_string solver_uc) lit_uc_list " ")^" 0")


let solver_out_to_string = function
  |Sat   -> "Satisfiable"
  |Unsat -> "Unsatisfiable"
  


let lit_val_to_string = function 
  |True  -> "True"
  |False -> "False"
  |Any   -> "Any"

let lit_sign_to_string = function
  |Pos  -> "Positive"
  |Neg  -> "Negative"


let create_solver is_sim = 
  SatSolver.create_solver is_sim

let reset_solver solver = 
  SatSolver.reset_solver solver

let delete_solver solver = 
  SatSolver.delete_solver solver

let delete_solver_uc solver_uc = 
  SatSolverUC.delete_solver solver_uc

let reset_solver_uc solver_uc = 
  SatSolverUC.reset_solver solver_uc

let create_solver_uc is_sim = 
  SatSolverUC.create_solver is_sim

let is_simplification solver = 
  SatSolver.is_simplification solver

let num_of_solver_calls solver = 
  SatSolver.num_of_solver_calls solver

let num_of_fast_solver_calls solver = 
  SatSolver.num_of_fast_solver_calls solver


let num_of_vars solver =
  SatSolver.num_of_vars solver

let num_of_clauses solver =
  SatSolver.num_of_clauses solver

let sign_to_bool = function
  |Pos -> true
  |Neg -> false
	
let bool_to_sign = function
  | true -> Pos
  | false -> Neg
	
let add_var_solver solver var_id =
  SatSolver.add_var solver var_id

let create_lit solver sign var =
  SatSolver.create_lit solver (sign_to_bool sign) var
    
let create_lit_uc solver sign var =
  SatSolverUC.create_lit solver (sign_to_bool sign) var
    
(* can raise Unsatisfiable_gr_na *)
let add_clause solver lits_in =
  try
    SatSolver.add_clause solver lits_in
  with
    SatSolver.Unsatisfiable_prop_na -> raise Unsatisfiable_gr_na
      
let add_clause_with_id solver id_in lits_in = 
  try
    SatSolverUC.add_clause_with_id solver id_in lits_in
  with SatSolverUC.Unsatisfiable_prop_na -> 
    (
     (* Format.eprintf "Unsatisfiable with added clause in unsat core solver@."; *)
     raise Unsatisfiable_gr_na
    )
      
let clauses_with_id solver =
  SatSolverUC.clauses_with_id solver


let bool_option_to_val = function
  | Some true -> True 
  | Some false -> False
  | None -> Any

        
let remove_Any_val solver lit lit_val = 
  let lit_sign = lit_sign solver lit in
  match lit_val with 
  | Any ->  
      (
       
       let new_val = if lit_sign then True else False in   (* positive default value *)
       (* let new_val = if lit_sign then False else True in *)(* neg default *) 
       dbg D_trace (lazy ("lit_val: "^(lit_to_string solver lit)^" Any -> "^(lit_val_to_string new_val)));
       new_val
      )
  | x -> x


(*  cannot mach a int constant ...
  | l_True    -> True 
  | l_False   -> False
  | l_Undef   -> Any
*)
 
(*	
let lit_val solver lit  = 
  int_to_val (lit_val_minisat solver lit.minisat_val (sign_to_bool lit.sign))
  *)  


(* TODO: *)
(* KK fix Any in change_model_solver in prop_solver_exchange *)

let lit_val solver lit  = 
  remove_Any_val solver lit (bool_option_to_val (SatSolver.model_value solver lit))

(* can raise Unsatisfiable_gr_na *)
let solve ?(reset=false) solver =
  try
    let start_time = Unix.gettimeofday () in
    let outcome = SatSolver.solve ~reset:reset solver in  
    let end_time = Unix.gettimeofday () in
    add_float_stat (end_time -. start_time) prop_solver_time;
    if outcome = true then Sat else Unsat
  with
    SatSolver.Unsatisfiable_prop_na -> 
      (
       raise Unsatisfiable_gr_na
      )
(*
  with SatSolver.Unsatisfiable -> 
    (
      (* Format.eprintf "Unsatisfiable on solve call@."; *)
      raise Unsatisfiable
    )
*)

let set_important_lit solver lit = 
  SatSolver.set_important_lit solver lit
      
(* implemented only in C++ version of minisat *)
let set_decision_var solver is_decision lit = 
  SatSolver.set_decision_var solver is_decision lit

(* implemented only in C++ version of minisat *)
let set_decision_var_uc solver_uc is_decision lit_uc = 
  SatSolverUC.set_decision_var solver_uc is_decision lit_uc



let solve_uc solver =
  try 
    let start_time = Unix.gettimeofday () in
    let outcome = SatSolverUC.solve solver in  
    let end_time = Unix.gettimeofday () in
    add_float_stat (end_time -. start_time) prop_solver_time;
    if outcome = true then Sat else Unsat
  with SatSolverUC.Unsatisfiable_prop_na -> 
    (
      (* Format.eprintf "Unsatisfiable on solve call@."; *)
      raise Unsatisfiable_gr_na
    )
      
(* can raise Unsatisfiable_gr_na *)
let solve_assumptions  ?(reset=false) solver assumptions =
  try
    let start_time = Unix.gettimeofday () in
    let result = SatSolver.solve_assumptions ~reset:reset solver assumptions in
    let end_time = Unix.gettimeofday () in
    add_float_stat (end_time -. start_time) prop_solver_time;
    (match result with 
      | true -> Sat    (* under assumption *) 
      | false -> Unsat)  (* under assumption *) 
  with 
    SatSolver.Unsatisfiable_prop_na -> 
      raise
        ( 
        Unsatisfiable_gr_na
         )
let solve_assumptions_uc solver assumptions =
  try 
    let start_time = Unix.gettimeofday () in
    let result = SatSolverUC.solve_assumptions solver assumptions in
    let end_time = Unix.gettimeofday () in
    add_float_stat (end_time -. start_time) prop_solver_time;
    (match result with 
      | true -> Sat    (* under assumption *) 
      | false -> Unsat)  (* under assumption *) 
  with SatSolverUC.Unsatisfiable_prop_na -> 
    (
      (* Format.eprintf "Unsatisfiable without assumptions@."; *)
      raise Unsatisfiable_gr_na
    )

let solve_assumptions_upto_id_uc solver assumptions max_id =
  try 
    let start_time = Unix.gettimeofday () in
    let result = 
      SatSolverUC.solve_assumptions_upto_id solver assumptions max_id 
    in
    let end_time = Unix.gettimeofday () in
    add_float_stat (end_time -. start_time) prop_solver_time;
    (match result with 
      | true -> Sat    (* under assumption *) 
      | false -> Unsat)  (* under assumption *) 
  with SatSolverUC.Unsatisfiable_prop_na -> 
    (
      (* Format.eprintf "Unsatisfiable without assumptions@."; *)
      raise Unsatisfiable_gr_na
    )

(* can raise Unsatisfiable_gr_na *)
let fast_solve solver assumptions =
  try
    let start_time = Unix.gettimeofday () in
    let result = SatSolver.fast_solve solver assumptions in
    let end_time = Unix.gettimeofday () in
    add_float_stat (end_time -. start_time) prop_fast_solver_time;
    (match result with 
      | Some false -> FUnsat    (* under assumption *) 
      | Some true-> FUnknown  (* under assumption *) 
      | None  -> FUnknown)  
  with 
    SatSolver.Unsatisfiable_prop_na -> 
      raise 
        (         
                  Unsatisfiable_gr_na 
                 )
        


let get_conflicts solver = 

(*  let start_core_time = Unix.gettimeofday () in*)
  let basic_core = SatSolverUC.get_conflicts solver in
(*  let end_core_time = Unix.gettimeofday () in
  out_str ("\n\n core time: "^(string_of_float (end_core_time -. start_core_time))^"\n");*)
(*
  let start_min_core_time = Unix.gettimeofday () in*)
  let core = 
    if !current_options.min_unsat_core 
    then 
      let min_core = SatSolverUC.minimise_core solver basic_core in
      min_core
    else
      basic_core
  in
(*  let end_min_core_time = Unix.gettimeofday () in
  out_str ("\n\n min core time: "^(string_of_float (end_min_core_time -. start_min_core_time))^"\n");
*)

(*
  Format.eprintf 
    "Core size: %d, minimal core size: %d@." 
    (List.length core) 
    (List.length min_core); 
*) 
 (* Format.eprintf
    "Core: %a@.@\nMinimal core: %a@.@\n" 
    (pp_int_list " ") core
    (pp_int_list " ") min_core; *)
(*  min_core *)
  core



let get_next_implied_unit solver = SatSolver.get_next_implied_unit solver
let get_next_ass_implied_unit solver = SatSolver.get_next_ass_implied_unit solver


(*---- prop literal key/map/hash ----*)

let lit_equal l1 l2 =  (SatSolver.get_lit_id l1) = (SatSolver.get_lit_id l2) 
let lit_compare l1 l2 = Pervasives.compare (SatSolver.get_lit_id l1)  (SatSolver.get_lit_id l2)
let lit_hash l = SatSolver.get_lit_id l


module PLKey = 
  struct
    type t      = lit
    let equal   = lit_equal  
    let hash    = lit_hash 
    let compare = lit_compare
  end


module PLMap = Map.Make(PLKey)
    
module PLSet = Set.Make(PLKey)

module PLHashtbl = Hashtbl.Make(PLKey)


(*--------*)
