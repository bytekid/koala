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
open Statistics
open Logic_interface
open Instantiation_loop
open Resolution_loop


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_mem
  | D_solve
  | D_shared_clauses

let dbg_gr_to_str = function 
  | D_trace -> "true"	
  | D_mem -> "mem"
  | D_solve -> "solve"
  | D_shared_clauses -> "shared_clauses"

let dbg_groups =
  [
(*   D_trace; *)
(*   D_mem; *)
(* D_solve; *)
D_shared_clauses
 ]
    
let module_name = "proof_search_loop"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(* change Sched_Time_Out to PS_loop_timeout *)

exception PS_loop_time_out of int

let check_sched_time ~start_time ~time_limit full_loop_counter =
  match time_limit with
  | Undef -> ()
  | Def time_limit ->
      if ((Unix.gettimeofday ()) -. start_time ) > time_limit
      then
	(
	 raise (PS_loop_time_out full_loop_counter)
	)
      else ()


let time_to_string time =
  match time with
  | Def(float) -> string_of_float float
  | Undef -> "Unbounded"


(*------------ proof search state --------------------*)
        
type ps_state = 
    {
     mutable ps_res_state  : res_state param; 
     mutable ps_inst_state : inst_state param;
   }

(*
let ps_create_state () = 
  {
   ps_res_state = Def(res_create_state ~res_prep_only:false);
   ps_inst_state = Def(inst_create_state ());
 }
*)

(* TODO add option *)

let res_create_state_shared () = 
   let res_state = res_create_state ~res_prep_only:false in
   (if !current_options.share_sel_clauses
   then
     (let shared_clauses = CSet.elements (Shared_clauses.get_all_shared_clauses ()) in 
     dbg D_shared_clauses (lazy ("res adding: "^(Clause.clause_list_to_string shared_clauses)));
     res_add_clause_list res_state shared_clauses;
     )
   );
   res_state

let inst_create_state_shared () = 
  let inst_state = inst_create_state () in
  (if !current_options.share_sel_clauses
  then     
    (let shared_clauses = CSet.elements (Shared_clauses.get_all_shared_clauses ()) in 
    dbg D_shared_clauses (lazy ("inst adding: "^(Clause.clause_list_to_string shared_clauses)));
    inst_add_clause_list inst_state shared_clauses;
    )
  );
  inst_state


let ps_create_state () = 
  {
   ps_res_state = Def(res_create_state_shared ());
     
   ps_inst_state = Def(inst_create_state_shared ());
 }

(* END DEBUG *)

let ps_reset_state ps_state = 
  dbg_env D_mem 
    (fun () -> 
      print_objsize "ps_state" ps_state
    );
  Prop_solver_exchange.clear_soft_assumptions ();
  let reset_fun () = 
    ps_state.ps_inst_state <- Def(inst_create_state ());
    ps_state.ps_res_state  <- Def(res_create_state ~res_prep_only:false);
  in  
  if not dbg_flag then reset_fun ();
  dbg_env D_mem 
    (fun () -> 
      print_mem_time_fun reset_fun ();
      out_basic_mem () 
    )
      
let ps_inst_clear ps_state = ps_state.ps_inst_state <- Undef
let ps_res_clear ps_state  = ps_state.ps_res_state <- Undef

let ps_clear_state ps_state = 
  ps_inst_clear ps_state;
  ps_res_clear ps_state

let ps_get_inst_state ps_state = get_param_val ps_state.ps_inst_state
let ps_get_res_state ps_state  = get_param_val ps_state.ps_res_state

(*
type prover_functions = {
    mutable inst_lazy_loop_body : (int ref -> int ref -> unit) param;
    mutable inst_add_clause : (clause -> unit) param;
    mutable inst_get_all_input_clauses : (unit -> clause list) param;
    mutable inst_clear_all : (unit -> unit) param;
    mutable res_discount_loop_exchange : (unit -> unit) param;
    mutable res_add_clause : (clause -> unit) param;
    mutable res_get_all_input_clauses : (unit -> clause list) param;
    mutable res_simplified_input : context param;
    mutable res_clear_all : (unit -> unit) param
  }
*)

(*
let provers_list = ref []


let provers_register pf =
  provers_list:= pf:: (!provers_list)
*)

(*
let clear_all_provers prover_functions =
  apply_fun_if_def prover_functions.inst_clear_all ();
  apply_fun_if_def prover_functions.res_clear_all ()
*)

(*
let provers_clear_and_remove_all () =
  List.iter 
    (fun pf -> 
      clear_all_provers pf; 
      pf.inst_lazy_loop_body <- Undef;
      pf.inst_add_clause <-Undef;
      pf.inst_get_all_input_clauses <-Undef;
      pf.inst_clear_all <- Undef;
      pf.res_discount_loop_exchange <- Undef; 
      pf.res_add_clause <- Undef;
      pf.res_get_all_input_clauses <-Undef;
      pf.res_simplified_input <- Undef;
      pf.res_clear_all <- Undef; 
    )
    !provers_list; 
  provers_list := []

let provers_clear_and_remove_top () =
  match !provers_list with
  | h:: tl ->
      clear_all_provers h;
      provers_list:= tl
  |[] -> ()

let get_inst_name_param_from_options () = 
  if !current_options.instantiation_flag 
  then
    Def("Inst")
  else 
    Undef		

let get_res_name_param_from_options () = 
  if !current_options.resolution_flag 
  then
    Def("Res")
  else 
    Undef		
      
      
let create_provers ~inst_name_param ~res_name_param input_clauses =
*)
(* reseting here is a problem; can have unsat without assumptions when it is unsat with assumptions...
 (if !current_options.reset_solvers
 then
   (Prop_solver_exchange.reset_solvers ())
 );
*)
(*
  let prover_functions = {
    inst_lazy_loop_body = Undef;
    inst_add_clause = Undef;
    inst_get_all_input_clauses = Undef;
    inst_clear_all = Undef;
    res_discount_loop_exchange = Undef;
    res_add_clause = Undef;
    res_get_all_input_clauses = Undef;
    res_simplified_input = Undef;
    res_clear_all = Undef
  } in
  (
   (*if !current_options.instantiation_flag 
     then*)
   match inst_name_param with 
   | Def(inst_name) ->
       let module InstInput =
	 struct
	   let inst_module_name = inst_name
	   let input_clauses = input_clauses
	 end in
       let module InstM = Instantiation.Make (InstInput) in
       prover_functions.inst_lazy_loop_body <- Def(InstM.lazy_loop_body);
       prover_functions.inst_add_clause <- Def(InstM.add_clause);
       prover_functions.inst_get_all_input_clauses <- Def(InstM.get_all_input_clauses);
       prover_functions.inst_clear_all <- Def(InstM.clear_all);
   | Undef ->	()
	 (*	else ()*)
  );
  ((*if !current_options.resolution_flag
     then *)
   match res_name_param with 
   | Def(res_name) ->
       
       let module ResInput =
	 struct
	   let res_module_name = res_name
	   let input_clauses = input_clauses
	   let is_res_prepocessing = false
	 end in
       let module ResM = Discount.Make (ResInput) in
       prover_functions.res_discount_loop_exchange <- Def(ResM.discount_loop_exchange);
       prover_functions.res_add_clause <- Def(ResM.add_clause);
       prover_functions.res_get_all_input_clauses <- Def(ResM.get_all_input_clauses);
       prover_functions.res_simplified_input <- Def(!ResM.simplified_input);
       prover_functions.res_clear_all <- Def(ResM.clear_all)
   | Undef ->	()
	 (*	else()*)
  );
  provers_register prover_functions;
  prover_functions

let create_provers_current_options input_clauses = 
  create_provers 
    ~inst_name_param:(get_inst_name_param_from_options ())
    ~res_name_param:(get_res_name_param_from_options ())
    input_clauses

*)

(* TODO: restore simplify_input *)  
(*
let simplify_input prover_functions clauses =
  if !current_options.res_sim_input
  then
  (  

(* TODO: experiment with preprocess!
     out_warning ("proof_search_loop: simplify_input -> preprocess \n\n");

   let prep_clauses =  
    Preprocess.preprocess ~is_eq_problem:(Problem_properties.has_equality clauses)  clauses in
   prep_clauses
*)
    match prover_functions.res_simplified_input with 
    | Def (simplified_input) -> 
	Clause.context_replace_by_clist simplified_input clauses
    |Undef -> clauses
)
  else 
    clauses 
*)

(*--- economical options output ---*)

(* last printed options *)
let last_used_options = ref None

(* set options and print them *)
let save_and_print_options () =
  (* save current options *)
  last_used_options := Some !current_options;
  (* print options *)
  out_str ((s_pref_str ())^"Current options:\n"^(options_to_str !current_options)^"\n\n");
  (* that's it *)
  ()

(* print options if they are changed *)
let print_options_if_new () =
  match !last_used_options with
  (* same options -- don't print *)
  | Some op when (op = !current_options) -> ()
  (* not the same options -- save and print *)
  | _ -> save_and_print_options ()

(*----------------------Full Loop--------------------------------------*)

let ps_full_loop ~time_limit input_clauses =
  let o = !current_options in  
  let start_time = (Unix.gettimeofday ()) in
  
  print_options_if_new ();
  
  out_str "\n";
  print_string ((s_pref_str ())^"Proving...\n");
  flush stdout;

  let ps_state = ps_create_state () in
  dbg D_trace (lazy ("adding clauses to ps_state: "));
  dbg D_trace (lazy (Clause.clause_list_to_string input_clauses));
  (if o.instantiation_flag then inst_add_clause_list (ps_get_inst_state ps_state) input_clauses); 
  (if o.resolution_flag    then res_add_clause_list (ps_get_res_state ps_state) input_clauses);  
  dbg D_trace (lazy ("done adding clauses "));

  let learning_bound = ref o.inst_learning_start in
  let learning_counter = ref 0 in
  let resolution_counter = ref 0 in
  let instantiation_counter = ref 0 in
  let full_loop_counter = ref 0 in
  while true do
    (     
     check_sched_time ~start_time ~time_limit !full_loop_counter;
     full_loop_counter:= !full_loop_counter +1;
     if (not o.resolution_flag) && (not o.instantiation_flag) then failwith "both --resolution_flag false and --instantiation_flag false";
     if (o.comb_res_mult = 0) && (o.comb_inst_mult =0) then failwith "both comb_res_mult=0  and comb_inst_mult=0";

     dbg D_trace (lazy (" loop: "^(string_of_int !full_loop_counter)));

     dbg D_trace (lazy ("o.resolution_flag: "^(string_of_bool o.resolution_flag)
                        ^" o.comb_res_mult: "^(string_of_int o.comb_res_mult)
                        ^" !resolution_counter: "^(string_of_int !resolution_counter)));

      dbg D_trace (lazy ("o.instantiation_flag: "^(string_of_bool o.instantiation_flag)
                        ^" o.comb_inst_mult: "^(string_of_int o.comb_inst_mult)
                        ^" !instantiation_counter: "^(string_of_int !instantiation_counter)));
    
     if (o.resolution_flag &&
	 (!resolution_counter < o.comb_res_mult))
     then
       (
	resolution_counter:= !resolution_counter + 1;
	(*num_resolution_loops := !num_resolution_loops+1;*)
	(try
	  assign_discount_time_limit (o.res_time_limit);
	  assign_discount_start_time ();
	  resolution_loop_exchange (ps_get_res_state ps_state);
          unassign_discount_time_limit ();
	with Timeout ->
	  unassign_discount_time_limit ();
	  out_str (pref_str^"Switching off resolution: loop timeout \n");
	  (if (not (o.instantiation_flag))
	  then 
	    (
	     out_warning "Switching on instantiation";
	     o.instantiation_flag <- true;
             inst_add_clause_list (ps_get_inst_state ps_state) input_clauses
	    )
	  ); 
	  if (o.instantiation_flag) then
	    (  o.resolution_flag <- false; 
(* TODO:       input_clauses_ref := simplify_input prover_functions !input_clauses_ref;*)
	       ps_res_clear ps_state;
	       clear_memory ()
	      )
	  (* switching_off_discount ()*)
	 (* else failwith "Inst is off and Resolution is TimeOut: see --res_time_limit" *)
	);
	(*       out_str ("Resolution flag: "^(string_of_bool !resolution_flag)^"\n");*)
	
	(* let f clause =
	   if (not (ClauseAssignDB.mem clause !clause_db_ref))
	   then ( clause)
	   else ()
	   in
	 *)
	(* List.iter
	   (Prop_solver_exchange.add_clause_to_solver gr_by) exchange_clauses;*)
	(* out_str ("\n Exchange Clauses: "
	   ^(Clause.clause_list_to_string exchange_clauses)^"\n") *)
       )
     else (* end of resolution part *)
       (
	if o.instantiation_flag &&
	  (!instantiation_counter < o.comb_inst_mult)
	then
	  (instantiation_counter := !instantiation_counter + 1;
	   if ((not o.inst_learning_loop_flag) ||
	   (!learning_counter < !learning_bound))
	   then
	     (
	      learning_counter:=!learning_counter +1;
	      incr_int_stat 1 inst_num_of_loops;
              inst_lazy_loop_body (ps_get_inst_state ps_state);
	     )
	   else
	     (* learning: !current_options.inst_learning_loop_flag & !learning_counter >= !learning_bound *)
	     ((* Format.eprintf "Learning restart in instantiation@."; *)
	      learning_bound:=!learning_bound * o.inst_learning_factor;
	      learning_counter:=0;
	      
	      incr_int_stat 1 inst_num_of_learning_restarts;
(*	      (if (Prop_solver_exchange.solve ~reset:  true ()) = PropSolver.Unsat*)
              dbg D_solve (lazy "ps_full_loop");
              ps_reset_state ps_state;
	      (if (Prop_solver_exchange.solve ~reset:false ()) = PropSolver.Unsat
	      then
		(* Raise separate exception, solver is not in an invalid state
		   and can be satisfiable without assumptions *)
		(* raise PropSolver.Unsatisfiable *)
		raise Unsatisfiable_gr
	      );
              
              (* run solve on solver_sim to infer more units in solver_sim *)

              if ((get_val_stat inst_num_of_learning_restarts) >= o.inst_start_prop_sim_after_learn)
              then
                (
                 let solver_sim_result =(Prop_solver_exchange.solve ~solver_in:Prop_solver_exchange.solver_sim ()) in 
                 assert (not (solver_sim_result = PropSolver.Unsat));
                 (* solver_sim should not be unsat if solver is not unsat *)
                );

              (if o.instantiation_flag then inst_add_clause_list (ps_get_inst_state ps_state) input_clauses);  
              (if o.resolution_flag    then res_add_clause_list (ps_get_res_state ps_state) input_clauses);  

 	      
(*              ps_clear_state ps_state; *)
	      (* simplify current_input_clauses with the new solver state *)
	      (* when simpl. given and new are switched off *)
	      (* not very good?  *)
	      (* let simplify_clause rest clause =
		 (Prop_solver_exchange.prop_subsumption clause):: rest
		 in
		 current_input_clauses := List.fold_left
		 simplify_clause [] !current_input_clauses;
	       *)
	      (* debug *)
	      (*
		out_str ("\n New Input Length: "
		^(string_of_int (List.length !current_input_clauses))^"\n");
	       *)
	      (* out_str "\nNon Horn Clauses:\n";
		 List.iter
		 (fun c ->
		 if (not (Clause.is_horn c))
		 then
		 out_str (Clause.to_string c)
		 else())
		 !current_input_clauses;
	       *)
	      (*		*)
	      (* out_str ("\n Simplifying input clauses after restart...");
		 let simp_input_clauses = List.map Prop_solver_exchange.prop_subsumption input_clauses in
		 out_str ("done\n");
	       *)
	      (* end debug *)
	      
(* TODO:      input_clauses_ref := simplify_input prover_functions !input_clauses_ref;  *)
(*
	      let module InstInput =
		struct
		  let inst_module_name =
		    ("Inst Restart "
		     ^(string_of_int (get_val_stat inst_num_of_learning_restarts)))
		      
		      (*		    let input_clauses = !current_input_clauses		  *)
		      (*		    let input_clauses = simp_input_clauses	       	*)
(*		  let input_clauses = !input_clauses_ref *)
		  let input_clauses = apply_fun prover_functions.inst_get_all_input_clauses ()
		end in
	      let module InstM = Instantiation.Make (InstInput) in
	      prover_functions.inst_lazy_loop_body <- Def(InstM.lazy_loop_body);
	      prover_functions.inst_add_clause <- Def(InstM.add_clause);
	      prover_functions.inst_get_all_input_clauses <- Def(InstM.get_all_input_clauses);
	      prover_functions.inst_clear_all <-Def(InstM.clear_all);
	      (*	      prover_functions.inst_learning_restart input_clauses;*)
*)
	      clear_memory ()
	     )
	  )
	else (* instantiation_counter > instantiation_mult *)
	  (resolution_counter:= 0;
	   instantiation_counter:=0
	  )
	    
       )
    )
  done
