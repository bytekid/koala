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
(*open Logic_interface *)


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_parents

let dbg_gr_to_str = function 
  | D_trace   -> "trace"
  | D_parents -> "get_parents"
	
let dbg_groups =
  [
    D_trace; 
(*  D_parents; *)
 ]
    
let module_name = "tstpProof"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)



module ClauseHashtbl=Clause.CHashtbl

(* Get parent leaf clauses of a list of clauses *)
let rec get_leaves' visited accum = function
    
    (* No more clause histories to recurse *)
  | [] -> accum
	
	(* Clause already seen *)
  | (clause :: tl) when ClauseHashtbl.mem visited clause ->
      
      (* Skip clause *)
      get_leaves' visited accum tl
	
	(* New clause *)
  | clause :: tl ->
      
      (* Remember clause *)
      ClauseHashtbl.add visited clause ();
      
      (* Get source of clause *)
      match
	(try
	  Clause.get_tstp_source clause
	with Failure _ ->
	  raise
	    (Failure
	       (Format.sprintf "Source of clause %s not defined" (Clause.to_string clause))))
      with
	
	(* Clause is from input or theory axioms *)
      | Clause.TSTP_external_source _
      | Clause.TSTP_internal_source _ ->
	  
	  (* Add clause as leaf *)
	  get_leaves' visited (clause :: accum) tl
	    
	    (* Clause is from global propositional subsumption *)
      | Clause.TSTP_inference_record
	  (Clause.Global_subsumption max_clause_id, [parent]) ->
	    

	    (* Get justification for simplification of clause *)
	    let parents' =
	      Prop_solver_exchange.justify_prop_subsumption
		max_clause_id
		parent
		clause
	    in
	    dbg D_parents (lazy ("TSTP_inference_record: Global_subsumption: parent:"^(Clause.to_tptp parent)));
	    dbg D_parents (lazy ("TSTP_inference_record: Global_subsumption: parents:"^(Clause.clause_list_to_tptp parents')));	    
	    (* Recurse to get parents of premises *)
	    get_leaves' visited accum ((parent :: parents') @ tl)
	      
	      (* Clause is from other inference *)
      | Clause.TSTP_inference_record (_, parents) ->
	  
	  (* Recurse to get parents of premises *)
	  get_leaves' visited accum (parents @ tl)

(* Get parent clauses of a list of clauses *)
let get_leaves clause_list =
  get_leaves' (ClauseHashtbl.create 101) [] clause_list

(* Order clauses topologically: leaves at the beginning, root at the
   end. First add all parents of a clause, then the clause.

   visited is a hash table of clauses seen and a flag if the
   clause has been added to the accumulator: a clause in the hash
   table with a false value has been seen but not added to the list, a
   clause with a true value is already in the list.
 *)
let rec get_parents' ignore_parents visited accum = function
    
  (* No more clause histories to recurse *)
  | [] -> accum
	
  (* Clause for which no parents are necessary *)
  | (clause :: tl) when (ignore_parents clause) ->

    dbg D_parents (lazy ("ignored: "^(Clause.to_string clause)));

    (* Remember insertion of clause into list *)
    ClauseHashtbl.add visited clause true;
    (* Add clause to list *)
    get_parents' ignore_parents visited (clause :: accum) tl

	(* Clause already seen or *)
  | (clause :: tl) when (ClauseHashtbl.mem visited clause) ->
     
    dbg D_parents (lazy ("visited: "^(Clause.to_string clause)));
     
    (* Clause is already in the list, then skip it *)
    if ClauseHashtbl.find visited clause then
    	get_parents' ignore_parents visited accum tl
    else (
      (* Remember insertion of clause into list *)
      ClauseHashtbl.add visited clause true;
      (* Add clause to list *)
      get_parents' ignore_parents visited (clause :: accum) tl
    )

	  (* New clause *)
  | clause :: tl ->
      
    dbg D_parents (lazy ("new: "^(Clause.to_string clause)));
      
    (* Remember recursion into parents of clause *)
    ClauseHashtbl.add visited clause false;
      
      (* Get source of clause *)
      match
	(try
	  Clause.get_tstp_source clause
	with Failure _ ->
	  raise
	    (Failure
	       (Format.sprintf "Source of clause %s not defined" (Clause.to_string clause))))
      with
	
        (* Clause is from input or theory axioms *)
        (* or obtained from init/lemmas by lifting them up *)
      | Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, _)
      | Clause.TSTP_external_source _
      | Clause.TSTP_internal_source _ ->
	  
	  (
	   (* Remember insertion of clause into list *)
	   ClauseHashtbl.add visited clause true;
	   
	   (* Add clause as leaf *)
	   get_parents' ignore_parents visited (clause :: accum) tl
	  )
	    
	    (* Clause is from global propositional subsumption *)
      | Clause.TSTP_inference_record
	  (Clause.Global_subsumption max_clause_id, [parent]) ->
	   
	    (* Get justification for simplification of clause *)
	    let parents' =
	      Prop_solver_exchange.justify_prop_subsumption
		max_clause_id
		parent
		clause
	    in
	    (
             dbg D_parents (lazy ("TSTP_inference_record: Global_subsumption: parent:"^(Clause.to_tptp parent)));      
             dbg D_parents (lazy ("TSTP_inference_record: Global_subsumption: parents:"^(Clause.clause_list_to_tptp parents')));
	    (* Recurse to get parents of premises *)
	    get_parents' ignore_parents
	      visited
	      accum
	      ((parent :: parents') @ (clause :: tl))
	    ) 
	      (* Clause is from other inference *)
      | Clause.TSTP_inference_record (_, parents) ->
	  
	  (* Recurse to get parents of premises *)
	  get_parents' ignore_parents
	    visited
	    accum
	    (parents @ (clause :: tl))

(* Get parent clauses of a list of clauses *)
let get_parents_filter ignore_parents clause_list =
  dbg D_parents (lazy ("Query for parents with method"));
  List.rev (get_parents' ignore_parents (ClauseHashtbl.create 101) [] clause_list)

(* Get parent clauses of a list of clauses *)
let get_parents clause_list =
  dbg D_parents (lazy ("Query for parents by default"));
  get_parents_filter (fun x -> false) clause_list

let global_subsumption_justification_fun max_clause_id parent clause =
  let parents' =
    Prop_solver_exchange.justify_prop_subsumption
      max_clause_id
      parent
      clause
  in
  parents'

let pp_clause_with_source_gs ?(clausify_proof = false) ppf clause	=
  Clause.pp_clause_with_source ppf 
    ~global_subsumption_justification_fun:(Some(global_subsumption_justification_fun)) 
    ~clausify_proof clause


(* Output a list of integers *)
let rec pp_clausify_proof_parents ppf = function
  | [] -> ()
  | [p] -> Format.fprintf ppf "%d" p
  | p :: tl ->
      pp_clausify_proof_parents ppf [p];
      Format.fprintf ppf ",";
      pp_clausify_proof_parents ppf tl

(* Output one entry of the hash table for the clausification proof *)
let pp_clausify_proof_line ppf f = function
  | s, p ->
      Format.fprintf ppf "%d: %a@\n%s@." f pp_clausify_proof_parents p s

(* Output contents of hash table for the clausification proof *)
let pp_clausify_proof ppf p =
  dbg D_trace (lazy ("pp_clausify_proof"));
  Hashtbl.iter (pp_clausify_proof_line ppf) p

(* Output clausification *)
let rec pp_clausification' visited clausify_proof ppf = function
    
    (* All parent clauses printed *)
  | [] -> ()
	
	(* Clause already printed *)
  | fof_id :: tl when Hashtbl.mem visited fof_id ->
      pp_clausification' visited clausify_proof ppf tl
	
	(* Clause not already printed *)
  | fof_id :: tl ->
      
      (
       
       try
	 
	 (* Get clause and parents from hash table *)
	 let fof_clause, parents = Hashtbl.find clausify_proof fof_id in
	 
		 (* Mark clause as printed *)
	 Hashtbl.add visited fof_id true;
	 
	 (* Output parent clauses *)
	 pp_clausification' visited clausify_proof ppf (parents @ tl);

	 (* Print clause *)
	 Format.fprintf ppf "%s@." fof_clause
	 
       with Not_found -> ()
	   
      )

(* Output clausification if clause is an input clause *)
let pp_clausification visited clausify_proof ppf clause =
  
  match Clause.get_tstp_source clause with
    
    (* Clause is from a file *)
  | Clause.TSTP_external_source (Clause.TSTP_file_source (_, name)) ->
      
      (
       
       let get_fof_id name = 
	 try 
	   Scanf.sscanf name "u%d" (function i -> i) (* vclausify id *)
	 with  Scanf.Scan_failure _ ->
	   try 
	     Scanf.sscanf name "c_0_%d" (function i -> i) (* eprover id *)
	   with 
	     Scanf.Scan_failure _ -> raise Not_found 
       in
       try
	 
	 (* Scan name of clause into u<n> *)
	 let fof_id = get_fof_id name in
	 
	 (* Output clausification *)
	 pp_clausification' visited clausify_proof ppf [fof_id]
	   
	   (* Skip if name of clause is not u<n> *)
       with Not_found -> ()
	   
      )
	
	(* Ignore clauses that are not input clauses *)
  | _ -> ()

(* Print derivation of clauses including clausification *)
let pp_clauses_with_clausification ppf clauses =
  
  (* Get parent clauses of unsat core clauses *)
  let parent_clauses = get_parents clauses in
  
  if
    
    (* Must output clausification for FOF problems *)
    ((!Parser_types.input_problem_type = Some Parser_types.FOF)
  (* ||
     (!Parser_types.input_problem_type = Some Parser_types.TFF)
   *)
    )
      &&
    
    (* but cannot clausify again when input is stdin *)
    (not !current_options.stdin)
      
  then
    (    
    (* ( *)
    (*  match (!Parser_types.input_problem_type) with  *)
    (*  |Some ipt -> *)
    (*      (dbg D_trace (lazy ("format:"^(Parser_types.input_problem_type_to_string ipt)));) *)
         
    (*  | None ()-> () *)
    (* ); *)
  (* Hash table for proof of clausification *)
    let clausify_proof = Hashtbl.create 1001 in
     
     (* Get command and options for clausification *)
     let clausify_cmd, clausify_arg =
       ParseFiles.clausifier_cmd_options ~pure_cnf_flag:false
     in
     
     (* $TPTP for includes has already been set in ParseFiles on
	first clausification *)
     
     (* Array of arguments for clausify command *)
     let clausify_cmd_args =
       Array.of_list
	 (clausify_cmd ::
	  (Str.split (Str.regexp "[ ]+") (clausify_arg)))
     in
     
     (* Fill hash table with proof of clausification *)
     (
      
      (* Later support more than one clausifier, distinguish by
	 name of executable *)

      try

	  
	  (* Clausify one input file and store proof in hash
	     table *)
	let clausify_file file =
	   (* 
	    (* Additional arguments for clausification proof *)
	    let clausify_cmd_args_proof =
	      [| "--print_clausifier_premises"; "on";
		 "--proof"; "tptp";
		 "--input_file"; file |]
	    in
	    *)
	    (* Add arguments to previous arguments of
	       clausification *)

 (* Additional arguments for clausification proof *)
	  dbg D_trace (lazy ( "Using clausifier: "^ clausify_cmd^"\n"));
	  let clausify_cmd_args_proof = 
	    match Filename.basename clausify_cmd with
	    | "vclausify_rel" -> 	(* Vampire clausifier *)
		[| 
                   "--print_clausifier_premises"; "on";
		   "--proof"; "tptp";
                  (* "--mode"; "clausify";*)
		   "--input_file"; file
                 |]
	    | "eprover" -> (* E clausifier *)
		dbg D_trace (lazy ("\n Using E clausifier\n"));
		[| "--proof-object"; file |]
	    |_-> raise Not_found 
	  in
	  
	    let clausify_cmd_args' =  Array.append clausify_cmd_args clausify_cmd_args_proof in
	    
            dbg D_trace (lazy ( "clausify_cmd_args': "^(String.concat " " (Array.to_list clausify_cmd_args'))^"\n"));

	    (* Copy of environment *)
	    let env = Unix.environment () in
	    
	    (* Create pipe for stderr of command *)
	    let cmd_stderr_out, cmd_stderr_in =
	      Unix.pipe ()
	    in
	    
	    (* Create input channel of pipe output *)
	    let cmd_stderr_out_ch =
	      Unix.in_channel_of_descr cmd_stderr_out
	    in
	    
	    (* Open /dev/null for reading *)
	    let devnull_in =
	      Unix.openfile "/dev/null" [Unix.O_RDONLY] 0o640
	    in
	    
	    (* Open /dev/null for writing *)
	    let devnull_out =
	      Unix.openfile "/dev/null" [Unix.O_WRONLY] 0o640
	    in
	    (* in vclausify_rel output is split: fof part into stderr and cnf into stdout *)
	    (* Create process *)
	    let cmd_pid =
	      Unix.create_process_env
		clausify_cmd
		clausify_cmd_args'
		env
		devnull_in
(*		devnull_out  *)
		cmd_stderr_in  
		cmd_stderr_in
	    in
	    
	    (* Close all files of process to prevent blocks *)
	    Unix.close devnull_in;
	    Unix.close devnull_out;
	    Unix.close cmd_stderr_in; 
	    
            dbg D_trace (lazy ( "ext clausify: finished")); 

	    (* Parse output of clausifier *)
	    let parse_out =
	      Lexer_fof.parse clausify_proof cmd_stderr_out_ch
	    in
            dbg D_trace (lazy ( "parse: finished")); 

	    (* Wait for process to terminate *)
	    let _cmd_pid_, _cmd_status =
	      Unix.waitpid [Unix.WUNTRACED] cmd_pid
	    in
            dbg D_trace (lazy ( "clausify process: finished")); 
	    Unix.close cmd_stderr_out;
	    parse_out
	      (*
		(* Only continue if exited with 0 *)
		if cmd_status = Unix.WEXITED 0 then
		
		(* Parse output of clausifier *)
		Lexer_fof.parse clausify_proof cmd_stderr_out_ch
	       *)
	  in
	  
	  (* Clausify all input files again *)
	  List.iter
	    clausify_file
	    !current_options.problem_files
      with Not_found ->    
        (
              dbg D_trace (lazy ("tstpProof: Unsupported clausifier "));
        )   (* Unsupported clausifier *)
	    
     );
     (*
       Format.eprintf
       "%a@."
       pp_clausify_proof
       clausify_proof;
      *)
   
      
   (* Print derivation of clauses from input formulae *)
     List.iter
       (pp_clausification (Hashtbl.create 1001) clausify_proof ppf)
       parent_clauses;
  
 (* Print derivation of clauses in unsat core with rewriting
	of input clauses *)
     List.iter
       (pp_clause_with_source_gs ~clausify_proof:true ppf)
       parent_clauses;
     
   )
      
  else
    
    (
     
     (* Print derivation of clauses in unsat core *)
     List.iter (pp_clause_with_source_gs ppf) parent_clauses;
     
    )

(* Print leaf clauses first *)
let pp_tstp_proof_resolution ppf clause =
  
  (* Print derivation of empty clause including clausification *)
  pp_clauses_with_clausification ppf [clause]

(*
  List.iter (pp_clause_with_source false ppf) (get_parents [clause])
 *)

let pp_tstp_proof_unsat_core ppf clauses =
  
  (* Set width of line to 72, that works with emails *)
  Format.set_margin 72;
  
  (* Print derivation of clauses including clausification *)
  pp_clauses_with_clausification ppf clauses;
  
  (* Separate non-ground clauses *)
  let gnd_clauses, non_gnd_clauses =
    List.partition Clause.is_ground clauses
  in
  
  (* Ground non-ground clauses *)
  let non_gnd_clauses' =
    List.map Prop_solver_exchange.ground_clause non_gnd_clauses
  in
  
  (* Print grounding of non-ground clauses in unsat core *)
  List.iter
    (pp_clause_with_source_gs ppf)
    non_gnd_clauses';
  
  (* Replace a non ground clause with its ground clause in the list *)
  let rec fold_with_gnd_clauses accum gnd_clauses = function
    | [] -> List.rev accum
    | c :: tl when Clause.is_ground c ->
	fold_with_gnd_clauses (c :: accum) gnd_clauses tl
    | c :: tl ->
	fold_with_gnd_clauses
	  (List.hd gnd_clauses :: accum)
	  (List.tl gnd_clauses)
	  tl
  in
  
  (* Replace each non ground clause with its ground clause *)
  let clauses' = fold_with_gnd_clauses [] non_gnd_clauses' clauses in
  
  (*
    (* Get assumptions in solver *)
    let assumptions = Prop_solver_exchange.get_solver_assumptions_sat () in
   *)
  
  (* Print refutation by minisat as a single inference *)
  Format.fprintf ppf
    "@[<hv 4>cnf(contradiction,plain,@,( $false ),@,@[<hv 10>inference(minisat,@,[status(thm)],@,@[<hov 1>[%a]@]@]) ).@]@\n@."
    (*    (pp_any_list Clause.pp_clause_name ",") (gnd_clauses @ non_gnd_clauses') *)
    (pp_any_list Clause.pp_clause_name ",") clauses'
