(*----------- solver/model based selection for instantiation_loop --------*)

open Lib
open Logic_interface
open Statistics
open Options
open Prop_solver_exchange
open Instantiation_env

(*------------------------- instantiation selection -----------------------*)

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =  
  | D_trace
  | D_gr_term 
  | D_selection_renew
  | D_selection_renew_lit
  | D_solve

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_gr_term -> "gr_term"
  | D_selection_renew -> "selection_renew"
  | D_selection_renew_lit -> "selection_renew_lit"
  | D_solve -> "solve"

let dbg_groups_ref =
  ref
    [
     D_trace;
     D_gr_term;  
     D_selection_renew_lit;    
     D_selection_renew;    
     D_solve;  
   ]
    
let module_name = "instantiation_sel"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag !dbg_groups_ref group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag !dbg_groups_ref group f
  
(*----- debug -----*)


(* selection returns (L,L\gr, ) *)

type inst_sel_result =  
    {
     mutable sel_lit : lit; 
     mutable sel_lit_gr : lit; 
     mutable sel_mv_from_active_to_passive : lit list;
   }

(* let pp_truth_val ppf = function *)
(*   | Undef -> Format.fprintf ppf "Undef" *)
(*   | Def PropSolver.True -> Format.fprintf ppf "True" *)
(*   | Def PropSolver.False -> Format.fprintf ppf "False" *)
(*   | Def PropSolver.Any -> Format.fprintf ppf "Any" *)

  

(*--------------*)
let get_lit_activity lit =
  let var_entry = get_prop_var_entry lit in
  if (Term.is_neg_lit lit) then
    get_var_entry_neg_activity var_entry
  else
    get_var_entry_pos_activity var_entry
      
let activity_condition lit =
  let activity = get_lit_activity lit in
  ((activity < ((get_val_stat inst_max_lit_activity) lsr 2 ))
 ||
   (activity < !lit_activity_threshold)
)

(*
let consistent_with_model_activity lit =
  (* remove true later*)
  if (activity_condition lit)
  then consistent_with_model_gr lit
  else false
*)

(* let consistent_with_solver_activity lit = *)
(*   (\* remove true later*\) *)
(*   if (activity_condition lit) *)
(*   then consistent_with_solver_gr lit *)
(*   else false *)



(*let solver_calls_renew = ref 0*)

let sel_consistent_with_solver cl_param = 
  try 
    let sel_lit = inst_cp_get_sel_lit cl_param in
    get_solver_lit_val_gr sel_lit    
  with 
    Inst_sel_lit_undef -> false


let get_sel_lit_solver selection_fun clause =   
  try
    (
     let sel_lit =
       (*	       selection_fun consistent_with_solver_activity clause in	 *)
       selection_fun get_solver_lit_val_gr clause in
     sel_lit
       (*	     out_str ("----------------------------\n");*)
    )
  with 
    Not_found ->
      (
       dbg D_solve (lazy (" selection_renew_solver: "^(Clause.to_string clause)));
     
(* TODO revise *)
(*     Clause.iter (set_decision_var true) clause; *)
       match (solve ()) with
       | PropSolver.Unsat ->
	 ( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_solver@."; *)
           dbg D_solve (lazy ("Unsatisfiable_gr in selection_renew_solver"));
	   raise Unsatisfiable_gr (* solve () can have default assumptions *)
	  ) 
       | PropSolver.Sat ->
	   let new_solver_sel_lit =
	     try
	       selection_fun get_solver_lit_val_gr clause
	     with Not_found ->
	     (
	      raise (Failure (Format.sprintf "No selection possible for %s@." (Clause.to_string clause))))
	   in
           new_solver_sel_lit
      )

(*---------------------------------------------------------------------*)
(* lit_selector chooses some literals from clause i.e. true in a model *)
let inst_lit_sel lit_selector clause = 
  let candidate_list = Clause.find_all lit_selector clause in
  let cmp_fun = (Term.lit_cmp_type_list_to_lex_fun 
		   !current_options.inst_lit_sel) in
  list_find_max_element cmp_fun candidate_list


(*---------------------------------------------------------------------*)
let inst_selection clause = get_sel_lit_solver inst_lit_sel clause

(*---------------------------------------------------------------------*)
exception Activity_Check
(*---------------------------------------------------------------------*)


(*
let rec selection_renew_solver move_lit_from_active_to_passive selection_fun clause =
  
  (* Format.eprintf
     "selection_renew_solver for clause %s@."
     (Clause.to_string clause); *)
  
  try
    (
     let solver_sel_lit =
       (*	       selection_fun consistent_with_solver_activity clause in	 *)
       selection_fun consistent_with_solver_gr clause in
     let solver_sel_var_entry = get_prop_gr_var_entry solver_sel_lit in
     (*  out_str ("Before change\n");*)

     change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;

     (*     out_str "Change here \n";*)
     (* out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
	^"Sel_lit entry: "
	^(var_entry_to_string solver_sel_var_entry));*)
     Clause.inst_assign_sel_lit solver_sel_lit clause;
     ass_if_consistent solver_sel_lit clause
       (*	     out_str ("----------------------------\n");*)
    )
  with Not_found ->
    ((*num_of_solver_calls := !num_of_solver_calls +1;*)
     (* solver_calls_renew:= !solver_calls_renew +1;
	out_str ("solver_calls renew "^(string_of_int !solver_calls_renew));*)

     dbg D_solve (lazy (" selection_renew_solver: "^(Clause.to_string clause)));
     
(* TODO revise *)
(*     Clause.iter (set_decision_var true) clause; *)
     match (solve ()) with
     | PropSolver.Unsat ->
	 ( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_solver@."; *)
           dbg D_solve (lazy ("Unsatisfiable_gr in selection_renew_solver"));
	   raise Unsatisfiable_gr (* solve () can have default assumptions *)
	  ) 
     | PropSolver.Sat ->
	 let new_solver_sel_lit =
	   try
	     selection_fun consistent_with_solver_gr clause
	   with Not_found ->
	     (
	      raise (Failure (Format.sprintf "No selection possible for %s@." (Clause.to_string clause))))
	 in
	 let new_solver_sel_var_entry =
	   get_prop_gr_var_entry new_solver_sel_lit in
	 (*		 out_str "\n Change here!!!!\n";*)
	 change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
	 (* out_str ("Solver select:"^
	    "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
	    ^"Sel_lit entry: "
	    ^(var_entry_to_string new_solver_sel_var_entry)^"\n");*)
	 Clause.inst_assign_sel_lit new_solver_sel_lit clause;
	 ass_if_consistent new_solver_sel_lit clause
    )
*)
(* let _ = out_str "\n\n !!!selection_renew_main later switch to  selection_renew_tmp!!!\n\n " *)

(*
let selection_renew x =

  match !current_options.inst_sel_renew with
  | Inst_SR_Solver ->
      selection_renew_solver x
  | Inst_SR_Model ->
      selection_renew_model x
*)



(*---------------------------------------------------------------------*)



(*------------Instantiation Lit Activity -----------------------------*)
(*
exception Activity_Check
exception Activity_Undef

let lit_activity_check lit =
  if (not !current_options.inst_lit_activity_flag)
  then ()
  else
    begin
      try
	let var_entry = get_prop_gr_var_entry lit in
	let model_truth_val =
	  match var_entry.truth_val with
	  | Def(PropSolver.True) -> true
	  | Def(PropSolver.False) -> false
	  | _ -> raise Activity_Undef
	in
	if ((model_truth_val = false)
	      (* && (var_entry.neg_activity >
		 (var_entry.pos_activity + !lit_activity_threshold + (!max_lit_activity lsr 2))) *)
	      && (var_entry.neg_activity > var_entry.pos_activity + var_entry.change_activity_limit)
	   )
	then
	  (
	   
	   dbg D_solve (lazy ("lit_activity_check"));  
	   (* set_important_for_prop_lit lit; *)
	   match (solve_assumptions solver [(get_prop_var_var_entry var_entry)])
	   with
	   | PropSolver.Unsat ->
	       (var_entry.change_activity_limit <- 1000000; (*any big number*)
		(* match (PropSolver.solve solver)
		   with PropSolver.Unsat -> raise Unsatisfiable
		   | PropSolver.Sat -> () *) )
	   | PropSolver.Sat -> (
	       incr_int_stat 1 inst_lit_activity_moves;
	       var_entry.pos_activity <- 0;
	       var_entry.neg_activity <- 0;
	       var_entry.change_activity_limit <-
		 (2 * var_entry.change_activity_limit);
	       (* out_str ("Act Lit: "^(Term.to_string lit)^"\n"
		  ^"Before Change: "
		  ^(var_entry_to_string solver var_entry)^"\n");
		*)
	       change_model_solver move_lit_from_active_to_passive var_entry;
	       
	       (* out_str ("After Chnage: "
		  ^(var_entry_to_string solver var_entry)^"\n");
		*)
	       raise Activity_Check)
		 
	  )
	else
	  if ((model_truth_val = true)
		(* && (var_entry.pos_activity > (var_entry.neg_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
		&& (var_entry.pos_activity > (var_entry.neg_activity + var_entry.change_activity_limit))
	     )
	  then
	    (
	     (* set_important_for_prop_lit lit; *)
	     dbg D_solve (lazy ("lit_activity_check"));  
	     match (solve_assumptions solver [(get_prop_neg_var_var_entry var_entry)])
	     with
	     | PropSolver.Unsat ->
		 (var_entry.change_activity_limit <- 1000000; (*any big number*)
		  (* match (PropSolver.solve solver)
		     with PropSolver.Unsat -> raise Unsatisfiable
		     | PropSolver.Sat -> () *))
		   (* (out_str ("Act_Check Unsat with assumption: "
		      ^(PropSolver.lit_to_string
		      (get_prop_neg_var_var_entry var_entry))^"\n")) *)
	     | PropSolver.Sat -> (
		 incr_int_stat 1 inst_lit_activity_moves;
		 var_entry.neg_activity <- 0;
		 var_entry.pos_activity <- 0;
		 var_entry.change_activity_limit <-
		   (2 * var_entry.change_activity_limit);
		 (* out_str ("Act Lit: "^(Term.to_string lit)^"\n"
		    ^"Before Change: "
		    ^(var_entry_to_string solver var_entry)^"\n");
		  *)
		 change_model_solver move_lit_from_active_to_passive var_entry;
		 (*
		   out_str ("After Chnage: "
		   ^(var_entry_to_string solver var_entry)^"\n");
		  *)
		 raise Activity_Check)
		   
	    )
	  else ()
      with Activity_Undef -> ()
    end

let increase_lit_activity i lit =
  try
    let var_entry = get_prop_gr_var_entry lit in
    let model_truth_val =
      match var_entry.truth_val with
      | Def(PropSolver.True) -> true
      | Def(PropSolver.False) -> false
      | _ -> raise Activity_Undef
    in
    if (model_truth_val = false)
    then
      (var_entry.neg_activity <- var_entry.neg_activity + i;
       if var_entry.neg_activity > (get_val_stat inst_max_lit_activity)
       then (assign_int_stat var_entry.neg_activity inst_max_lit_activity
	       (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		  ^(var_entry_to_string var_entry)) *)
	    )
      )
    else
      (var_entry.pos_activity <- var_entry.pos_activity + i;
       if var_entry.pos_activity > (get_val_stat inst_max_lit_activity)
       then (assign_int_stat var_entry.pos_activity inst_max_lit_activity
	       (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		  ^(var_entry_to_string var_entry)) *)
	    )
      )
  with Activity_Undef -> ()


*)
(*------------Instantiation Lit Activity -----------------------------*)
(*
exception Activity_Check
exception Activity_Undef
let lit_activity_check move_lit_from_active_to_passive lit =
  if (not !current_options.inst_lit_activity_flag)
  then ()
  else
    begin
      try
	let var_entry = get_prop_gr_var_entry lit in
	let model_truth_val =
	  match var_entry.truth_val with
	  | Def(PropSolver.True) -> true
	  | Def(PropSolver.False) -> false
	  | _ -> raise Activity_Undef
	in
	if ((model_truth_val = false)
	      (* && (var_entry.neg_activity >
		 (var_entry.pos_activity + !lit_activity_threshold + (!max_lit_activity lsr 2))) *)
	      && (var_entry.neg_activity > var_entry.pos_activity + var_entry.change_activity_limit)
	   )
	then
	  (
	   
	   dbg D_solve (lazy ("lit_activity_check"));  
	   (* set_important_for_prop_lit lit; *)
	   match (solve_assumptions solver [(get_prop_var_var_entry var_entry)])
	   with
	   | PropSolver.Unsat ->
	       (var_entry.change_activity_limit <- 1000000; (*any big number*)
		(* match (PropSolver.solve solver)
		   with PropSolver.Unsat -> raise Unsatisfiable
		   | PropSolver.Sat -> () *) )
	   | PropSolver.Sat -> (
	       incr_int_stat 1 inst_lit_activity_moves;
	       var_entry.pos_activity <- 0;
	       var_entry.neg_activity <- 0;
	       var_entry.change_activity_limit <-
		 (2 * var_entry.change_activity_limit);
	       (* out_str ("Act Lit: "^(Term.to_string lit)^"\n"
		  ^"Before Change: "
		  ^(var_entry_to_string solver var_entry)^"\n");
		*)
	       change_model_solver move_lit_from_active_to_passive var_entry;
	       
	       (* out_str ("After Chnage: "
		  ^(var_entry_to_string solver var_entry)^"\n");
		*)
	       raise Activity_Check)
		 
	  )
	else
	  if ((model_truth_val = true)
		(* && (var_entry.pos_activity > (var_entry.neg_activity + !lit_activity_threshold+(!max_lit_activity lsr 2))) *)
		&& (var_entry.pos_activity > (var_entry.neg_activity + var_entry.change_activity_limit))
	     )
	  then
	    (
	     (* set_important_for_prop_lit lit; *)
	     dbg D_solve (lazy ("lit_activity_check"));  
	     match (solve_assumptions solver [(get_prop_neg_var_var_entry var_entry)])
	     with
	     | PropSolver.Unsat ->
		 (var_entry.change_activity_limit <- 1000000; (*any big number*)
		  (* match (PropSolver.solve solver)
		     with PropSolver.Unsat -> raise Unsatisfiable
		     | PropSolver.Sat -> () *))
		   (* (out_str ("Act_Check Unsat with assumption: "
		      ^(PropSolver.lit_to_string
		      (get_prop_neg_var_var_entry var_entry))^"\n")) *)
	     | PropSolver.Sat -> (
		 incr_int_stat 1 inst_lit_activity_moves;
		 var_entry.neg_activity <- 0;
		 var_entry.pos_activity <- 0;
		 var_entry.change_activity_limit <-
		   (2 * var_entry.change_activity_limit);
		 (* out_str ("Act Lit: "^(Term.to_string lit)^"\n"
		    ^"Before Change: "
		    ^(var_entry_to_string solver var_entry)^"\n");
		  *)
		 change_model_solver move_lit_from_active_to_passive var_entry;
		 (*
		   out_str ("After Chnage: "
		   ^(var_entry_to_string solver var_entry)^"\n");
		  *)
		 raise Activity_Check)
		   
	    )
	  else ()
      with Activity_Undef -> ()
    end

let increase_lit_activity i lit =
  try
    let var_entry = get_prop_gr_var_entry lit in
    let model_truth_val =
      match var_entry.truth_val with
      | Def(PropSolver.True) -> true
      | Def(PropSolver.False) -> false
      | _ -> raise Activity_Undef
    in
    if (model_truth_val = false)
    then
      (var_entry.neg_activity <- var_entry.neg_activity + i;
       if var_entry.neg_activity > (get_val_stat inst_max_lit_activity)
       then (assign_int_stat var_entry.neg_activity inst_max_lit_activity
	       (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		  ^(var_entry_to_string var_entry)) *)
	    )
      )
    else
      (var_entry.pos_activity <- var_entry.pos_activity + i;
       if var_entry.pos_activity > (get_val_stat inst_max_lit_activity)
       then (assign_int_stat var_entry.pos_activity inst_max_lit_activity
	       (* out_str ("\n Max Lit Act: "^(Term.to_string lit)^"\n"
		  ^(var_entry_to_string var_entry)) *)
	    )
      )
  with Activity_Undef -> ()

*)


(*
let preserve_model_solver (* move_lit_from_active_to_passive *) (*var_entry*) =
  let prop_var = get_prop_var_var_entry var_entry in
  let prop_neg_var = get_prop_neg_var_var_entry var_entry in
  let new_truth_val = PropSolver.lit_val solver prop_var in
  (* out_str ("Var entry:"^(var_entry_to_string solver var_entry)^"\n");
     out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match (get_var_entry_truth_val var_entry) with
  | Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any)
      then
	(* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(set_var_entry_truth_val var_entry (Def(new_truth_val));
	 (*debug check *)
	 (* (if var_entry.sel_clauses !=[]
	    then out_str "preserve_model_solver: sel_clauses should be empty \n");
	  *)
	 true)
      else
	if (old_truth_val = new_truth_val) || (new_truth_val = PropSolver.Any)
	then true
	else
	  (
	   let assumption =
	     if old_truth_val = PropSolver.True
	     then prop_var
	     else prop_neg_var
	   in
	   (
	    dbg D_solve (lazy (" preserve_model_solver"));  
           (*num_of_solver_calls := !num_of_solver_calls +1;*)
	    match(solve_assumptions solver [assumption])
	    with
	    | PropSolver.Sat -> true
	    | PropSolver.Unsat (*| PropSolver.FUnknown*) ->
		( (*out_str "Prop unsat \n"; *)
(*
		  let new_truth_val = PropSolver.lit_val solver prop_var in
		  set_var_entry_truth_val var_entry (Def(new_truth_val));
		  let move_cl_from_active_to_passive clause =
		    if (Clause.get_ps_in_active clause)
		    then
		      (let sel_lit = Clause.inst_get_sel_lit clause in
		      (* moves all clauses indexed by sel_lit *)
		      move_lit_from_active_to_passive sel_lit)
		    else ()
		  in
		  List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
		  var_entry.sel_clauses <- [];
*)		  
		  (* out_str ("Preserve Model: Unsat: "
		     ^"Assum: "^(PropSolver.lit_to_string assumption)^"  "
		     ^(var_entry_to_string solver var_entry)^"\n");*)
		  
		  (* (match (solve ())
		     with PropSolver.Unsat -> raise Unsatisfiable
		     | PropSolver.Sat -> ());*)
		  
		  false)
	   ))
	    
  | Undef ->
      (var_entry.truth_val <- Def(new_truth_val);
       true)
(*with Not_found -> failwith "Nor_found here"*)
*)

(*
(* if model value is  defferent from solver then chage the model value *)
let change_model_solver move_lit_from_active_to_passive var_entry =
  let prop_var = get_prop_var_var_entry var_entry in
  (*  let prop_neg_var  = get_prop_neg_var_var_entry var_entry in*)
  let new_truth_val = PropSolver.lit_val solver prop_var in
  (* out_str ("Var enty:"^(var_entry_to_string solver var_entry)^"\n");
     out_str ("Solver truth val:"^(PropSolver.lit_val_to_string new_truth_val)^"\n");*)
  match var_entry.truth_val with
  | Def(old_truth_val) ->
      if (old_truth_val = PropSolver.Any)
      then
	(* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(
	 (*debug*)
	 (* (if var_entry.sel_clauses !=[]
	    then out_str "change_model_solver: sel_clauses should be empty \n");*)
	 var_entry.truth_val <- Def(new_truth_val))
      else
	if (old_truth_val = new_truth_val) (* || (new_truth_val = PropSolver.Any) *)
	then ()
	else
	  (
	   (* out_str ("Change_model_solver: "^
	      (var_entry_to_string var_entry)^"\n");*)
	   var_entry.truth_val <- Def(new_truth_val);
	   let move_cl_from_active_to_passive clause =
	     if (Clause.get_ps_in_active clause)
	     then
	       (let sel_lit = Clause.inst_get_sel_lit clause in
	       (*  out_str ("Change_model in Active: "^(Clause.to_string clause)^"\n");*)
	       (* moves all clauses indexed by sel_lit *)
	       move_lit_from_active_to_passive sel_lit
	       )
	     else ()
	   in
	   List.iter move_cl_from_active_to_passive var_entry.sel_clauses;
	   var_entry.sel_clauses <- []
	  )
	    
  | Undef ->
      var_entry.truth_val <- Def(new_truth_val)

(* auxilary function for below, apply only if lit is consitent with the model!*)

let ass_if_consistent lit clause =
  let var_entry = get_prop_gr_var_entry lit in
  if (get_var_entry_truth_val_def var_entry = PropSolver.Any)
  then
    (
     (*debug check *)
     
       (if var_entry.sel_clauses !=[]
       then Format.eprintf "ass_if_consistent: sel_clauses should be empty@.");
      
     var_entry.sel_clauses <- [clause];
     if (Term.is_neg_lit lit)
     then var_entry.truth_val <- Def(PropSolver.False)
     else var_entry.truth_val <- Def(PropSolver.True))
  else
    var_entry.sel_clauses <- clause:: (var_entry.sel_clauses)
(* we assume that the clause is from passive and therefore *)
(* not assigned in to any of var_entry.sel_clauses         *)
(* we try to keep the old selection                        *)
(*
  let find_nex_true_lit
 *)

let remove_undef_model clause =
  (* Format.eprintf
     "remove_undef_model %a@."
     Clause.pp_clause clause; *)
  let remove_undef_lit lit =
    (* Format.eprintf
       "remove_undef_lit %a@."
       Term.pp_term lit; *)
    let var_entry = get_prop_gr_var_entry lit in
    match var_entry.truth_val with
    | Def(PropSolver.Any) | Undef ->
	(* if truth_val = Def(Any) the we assume that sel_clauses=[] *)
	(let prop_var = get_prop_var_var_entry var_entry in
	let new_truth_val = PropSolver.lit_val solver prop_var in
	(* Format.eprintf
	   "Changing model for atom %s from %a to %a@."
	   (Term.to_string (Term.get_atom lit))
	   pp_truth_val var_entry.truth_val
	   pp_truth_val (Def new_truth_val); *)
	var_entry.truth_val <- Def(new_truth_val))
    | _ -> ()
	  (* Format.eprintf
	     "Keeping model for atom %s as %a@."
	     (Term.to_string (Term.get_atom lit))
	     pp_truth_val var_entry.truth_val *)
  in
  Clause.iter remove_undef_lit clause

exception Sel_Changed
exception Solver_Sel
let rec selection_renew_model move_lit_from_active_to_passive selection_fun clause =

  dbg D_selection_renew  (lazy ("clause:"^(Clause.to_string clause)));   
  (* Format.eprintf
     "selection_renew_model for clause %s@."
     (Clause.to_string clause); *)
  
  (*  out_str (" selection_renew clause:  "^(Clause.to_string clause)^"\n");*)
  (*
    let accord lit =
    let var_entry = get_prop_gr_var_entry lit in
    let _ = model_accords_solver solver var_entry in () in
    Clause.iter accord clause; *)
  (* do not try, it will cycle!
     let preserve_mod lit =
     let var_entry = get_prop_gr_var_entry lit in
     let _ = preserve_model_solver move_lit_from_active_to_passive solver var_entry in () in
     Clause.iter preserve_mod clause; *)
  try
    let sel_lit = Clause.inst_get_sel_lit clause in
    let sel_var_entry = get_prop_gr_var_entry sel_lit in
    if
      (consistent_with_model_gr sel_lit)
    then
      if
	(preserve_model_solver move_lit_from_active_to_passive sel_var_entry)
      then
	((* Format.eprintf "Selection is consistent and can be preserved@."; *)
	 ass_if_consistent sel_lit clause)
      else
	((* Format.eprintf "Selection is consistent but cannot be preserved@."; *)
	 raise Sel_Changed)
    else
      ((* Format.eprintf "Selection is not consistent@."; *)
       raise Sel_Changed)
  with
    Sel_Changed | Clause.Inst_sel_lit_undef ->
      (
       try
	 (
	  remove_undef_model clause;
	  
	  dbg_env D_selection_renew  
	    (fun () ->
	      (out_str ("\n----------------------------\n");
	       out_str ("Try consist with Model:");
	       let out_entry lit =
		 let var_entry = get_prop_gr_var_entry lit in
		 out_str ("\n Lit: "^(Term.to_string lit)^"\n"
			  ^(var_entry_to_string var_entry)^"\n"
			  ^"Consist_with_Model: "
			  ^(string_of_bool (consistent_with_model_gr lit))^"\n");
	       in Clause.iter out_entry clause; 
	      ));
	  let model_sel_lit =
	    selection_fun consistent_with_model_activity clause in
	  (* let model_sel_lit =
	     selection_fun consistent_with_model clause in *)
	  (*             out_str ("Consist_model: "^(Term.to_string model_sel_lit)^"\n");*)
	  let model_sel_var_entry = get_prop_gr_var_entry model_sel_lit in
	  if (preserve_model_solver move_lit_from_active_to_passive model_sel_var_entry) then
	    ((*change_model_solver model_sel_var_entry;*)
	     Clause.inst_assign_sel_lit model_sel_lit clause;
	     ass_if_consistent model_sel_lit clause;
	     (* out_str ("preserve model:  "^
		(var_entry_to_string model_sel_var_entry)^"\n");
		out_str ("----------------------------\n") *)
	    )
	  else
	    (* optional change_model*)
	    (
	     change_model_solver move_lit_from_active_to_passive model_sel_var_entry;
	     raise Solver_Sel)
	 )
       with Not_found | Solver_Sel ->
	 try (
	   (*debug*)
	   (* out_str ("----------------------------\n");
	      out_str ("No consist with Model:");
	      let out_entry lit =
	      let var_entry = get_prop_gr_var_entry lit in
	      out_str ("\n Lit: "^(Term.to_string lit)^"\n"
	      ^(var_entry_to_string var_entry)^"\n"
	      ^"Consist_with_Model: "
	      ^(string_of_bool (consistent_with_model lit))^"\n");
	      in Clause.iter out_entry clause;*)
	   
(* new *)
	   add_clause_to_solver clause;

	   let solver_sel_lit =
	     selection_fun consistent_with_solver_activity clause in
	   let solver_sel_var_entry = get_prop_gr_var_entry solver_sel_lit in
	   (*  out_str ("Before change\n");*)
	   change_model_solver move_lit_from_active_to_passive solver_sel_var_entry;
	   (*     out_str "Change here \n";*)
	   (* out_str("Sel_Lit: "^(Term.to_string solver_sel_lit)^"  "
	      ^"Sel_lit entry: "
	      ^(var_entry_to_string solver_sel_var_entry));*)
	   Clause.inst_assign_sel_lit solver_sel_lit clause;
	   ass_if_consistent solver_sel_lit clause
	     (*	     out_str ("----------------------------\n");*)
	  )
	 with Not_found ->
	   ((*num_of_solver_calls := !num_of_solver_calls +1;*)
	    dbg D_solve (lazy (" selection_renew_model"));
	    match (solve ()) with
	    | PropSolver.Unsat ->
		( (* Format.eprintf "Unsatisfiable after solve call in selection_renew_model@."; *)
		  raise Unsatisfiable_gr (* solve () can have default assumtions *)
		 )
	    | PropSolver.Sat ->
		
		let new_solver_sel_lit =
		  try
		    selection_fun consistent_with_solver_gr clause
		  with
		    Not_found ->

		      (
		       out_warning ("\n Selection is not found for clause: "
				    ^(Clause.to_string clause)^"\n"
				    (*^" is in prop_solver "
				     ^(string_of_bool (Clause.in_prop_solver clause))*));

		       dbg_env D_selection_renew 
			 ( fun () -> 
			   dbg_groups_ref:=(D_selection_renew_lit ::(!dbg_groups_ref));
			   let f lit = 
			     dbg D_selection_renew  
			       (lazy 
				  (" lit "^(Term.to_string lit)
				   ^" consistent with solver: "^(string_of_bool (consistent_with_solver_gr lit))
						  )
			       );
			   in Clause.iter f clause 
			  );

		      raise (Failure "selection_renew_model") )
			
		in
		let new_solver_sel_var_entry =
		  get_prop_gr_var_entry new_solver_sel_lit in
		(*		 out_str "\n Change here!!!!\n";*)
		change_model_solver move_lit_from_active_to_passive new_solver_sel_var_entry;
		(*
		  out_str ("Solver select:"^
		  "Sel_Lit: "^(Term.to_string new_solver_sel_lit)^"\n"
		  ^"Sel_lit entry: "
		  ^(var_entry_to_string new_solver_sel_var_entry)^"\n");
		 *)
		Clause.inst_assign_sel_lit new_solver_sel_lit clause;
		ass_if_consistent new_solver_sel_lit clause
		  
	   )
      )
*)
(*
  exception Sel_Unchanged
  let apply_new_model solver =
  let sel_is_changed = ref false in
  let change_entry var_entry =
  let prop_var = get_prop_var_var_entry var_entry in
  match var_entry.truth_val with
  | Def(_) ->
  if (change_model_solver move_lit_from_active_to_passive var_entry)
  then ()
  else sel_is_changed:= true
  | Undef ->
  (    (* sel_is_changed:=true; *)
  let new_truth_val = PropSolver.lit_val solver prop_var in
  var_entry.truth_val <- Def(new_truth_val)
  )
  in
  TableArray.iter change_entry var_table;
  if !sel_is_changed then ()
  else
  raise Sel_Unchanged
 *)
