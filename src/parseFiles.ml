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
open Printf
open Parser_types
open Options



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
    
let module_name = "parseFiles"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


(*type includes = Parser_types.includes*)

let parser_main_fun = Parser_tptp.main
let lexer_token = Lexer_tptp.token

(* when clausifier is used (the propblem is in fof), includes are assumed to be unfolded by the clausifier *)


(* include path ex:  "/home/TPTP-v3.0.1/Problems/"  include('Axioms/SET003-0.ax').*)
let remove_double_quotes str =
  let str_ln = String.length str in
  if str_ln > 1 then
    if (str.[0] = '\"') && (str.[(str_ln-1)] = '\"')
    then 
      if  str_ln > 2 
      then 
	String.sub str 1 (str_ln-2) 
      else ""
    else str
  else str



(*--------------------------*)

let append_iprover_path file_name =
  Filename.concat (iprover_exe_path ()) file_name


let clausifier_cmd_options ~pure_cnf_flag = 

(* find clausifier in the following sequence: *)
(* 1) --clausifier if not "" then take clausifier options from --clausifier_options *)
(* 2) environment vars CLAUSIFIER and CLAUSIFIER_OPTIONS *)
(* 3) from iprover_dir/VClausifier/vclausify_rel with  vlclausifier_default_options*)
(* 4) form iprover_dir/E_Prover/eprover with eprover_default_options *)
(*    *)

  let vlcausify_rel_cmd           = append_iprover_path "VClausifier/vclausify_rel" in
  let eprover_cmd                 = append_iprover_path "E_Prover/eprover_pure_cnf.sh" in
  let clausifier_env_name         = "CLAUSIFIER" in
  let clausifier_env_options_name = "CLAUSIFIER_OPTIONS" in
  
  let cpu_limit = 
    if input_options.time_out_virtual > 0. then
      (int_of_float input_options.time_out_virtual)+1 
    else 
      if input_options.time_out_real > 0. then
	(int_of_float input_options.time_out_real)+1
      else
	0
  in  
(*
  let default_vclausify_rel_options  = 
  " --mode clausify "
  ^(if cpu_limit > 0 then ("-t "^(string_of_int cpu_limit)) else "")
  in
 *)
(* new version of vclausify_rel *)
  let default_vclausify_rel_options  = 

(*    " --mode clausify --epr_preserving_skolemization on --equality_propagation on "*)

   (* need  -icip on -updr off for soundness *)
(*    let vclausify_mode_str = if (!input_problem_type = Some(TFF)) then " --mode tclausify -icip on -updr off " else " --mode clausify -icip on -updr off " in
*)
    let vclausify_mode_str = if (!input_problem_type = Some(TFF)) then " --mode tclausify " else " --mode clausify " in
    if (!current_options.sat_mode || 
    (!current_options.schedule = Options.Schedule_sat))
    then
      begin 
(* vclausify option --predicate_definition_inlining non_growing seems problemtic *)
(* so for now use default options *)
(*	" --mode clausify  --equality_propagation on --predicate_equivalence_discovery all_atoms --predicate_definition_inlining non_growing --epr_restoring_inlining on --predicate_definition_merging on -fde none "
*)
        vclausify_mode_str
	^(if cpu_limit > 0 then ("-t "^(string_of_int cpu_limit)) else "-t 1000000")
      end
    else
      begin

(*	" --mode clausify  --equality_propagation on --predicate_definition_inlining non_growing  --predicate_definition_merging on -fde none "
*)
        vclausify_mode_str
	^(if cpu_limit > 0 then ("-t "^(string_of_int cpu_limit)) else "-t 1000000")
      end
  in
(* need  --no-eq-unfolding otherwise negation_conjecture can be eliminated which can result in wrong Unsatisfiable for Theorem *)
  let default_eprover_options = 
    " --definitional-cnf=24 --no-eq-unfolding --tstp-format --free-numbers --free-objects --split-method=1  --silent --cnf --proof-object "^
    (if cpu_limit > 0 then (" --cpu-limit="^(string_of_int cpu_limit)) else "")
  in
  
  let check_clausifier cmd = 
    if cmd = "" 
    then
      false
    else
      if (Sys.file_exists cmd)
      then 
	true 
      else
	failwith ("cannot find clausifier: "^cmd^
		  ", please specify an appropriate --clausifier")    
  in  
  let eprover_to_eprover_pure_cnf clausifer_with_full_path =    
    if pure_cnf_flag 
    then 
      match (Filename.basename clausifer_with_full_path) with 
      |"eprover" | "eprover_pure_cnf.sh" -> 
	  let eprover_pure_cnf = Filename.concat (Filename.dirname clausifer_with_full_path) "eprover_pure_cnf.sh" in 
	  assert (Sys.file_exists eprover_cmd);
          dbg D_trace (lazy ("eprover_pure_cnf: "^(eprover_pure_cnf)));
	  eprover_pure_cnf
      | s -> s
    else 
      (       
       clausifer_with_full_path
      )
  in
  let (cmd, options) = 
    if (check_clausifier !current_options.clausifier)
    then 
      if (!current_options.clausifier_options = "")
      then
	match (Filename.basename !current_options.clausifier) with 
	|"vclausify_rel" -> (!current_options.clausifier, default_vclausify_rel_options)
	|"eprover" | "eprover_pure_cnf.sh" ->  
	    ((eprover_to_eprover_pure_cnf !current_options.clausifier), default_eprover_options)
	|_ -> (!current_options.clausifier, !current_options.clausifier_options)
      else 
	(!current_options.clausifier, !current_options.clausifier_options)
    else
      let cmd_env_name = 
	try 
	  remove_double_quotes (Unix.getenv clausifier_env_name)
	with Not_found -> ""
      in
      if (check_clausifier cmd_env_name)
      then
	let options =
	  try 
	    remove_double_quotes (Unix.getenv clausifier_env_options_name)
	  with
	    Not_found -> ""
	in 
	(cmd_env_name, options)
      else	
	if (Sys.file_exists vlcausify_rel_cmd) 
	then
	  (vlcausify_rel_cmd, default_vclausify_rel_options)
	else
	  if (Sys.file_exists eprover_cmd)
	  then 
	    ((eprover_to_eprover_pure_cnf eprover_cmd), default_eprover_options)
	  else
	    (failwith 
	       ("cannot find clausifier, please specify using --clausifier and --clausifier_options"))
	      
  in    	    
  dbg D_trace (lazy (" "));
  dbg D_trace (lazy (cmd^" "^options));
  (cmd,options)


(*-------------------------------------------*)

let check_clausifier_error_channel error_channel =   
  ()

(* We ignore output into the error_channel for now *)

(* OLD checks of error_channel for eprover, now all ignored, we just check the exit status 

   (* Ignore warnings *)
   let ignore_regexp = Str.regexp "eprover: Warning: " in

   (* Save lines read from stderr *)
   let error_line = ref [] in
   try 
   
   (* Read from stderr until end *)
   let rec f () = 
   
   (* Read one line *)
   let add_line = input_line error_channel in      
   if 
   
   (* Error is only a warning? *)
   Str.string_match ignore_regexp add_line 0	  
   then
   
   (* Ignore line *)
   (
   Printf.printf "Ignoring \"%s\"\n%!" add_line
   )	  
   else	
   (
   
   (* Kepp error line *)
   error_line := (add_line)::(!error_line)
   );

   (* Loop until end of file *)
   f ()
   in 
   (* Read all lines from stderr *)
   f ()
   
   with End_of_file -> 
   ( 	
   if 

   (* No error messages on stderr? *)
   !error_line = [] 
   then 
   (* Continue *)
   ()
   else 
   (* Fail *)
   (out_str "\n\n# SZS status: Unknown\n"; 		
   failwith ("fail to clausify by E prover: "
   ^(String.concat "\n" (List.rev !error_line)))
   )
   )
 *)

let check_clausifier_process_status process_status =
  match process_status with 
(*	The process terminated normally by exit; the argument is the return code.	*)
  | 	Unix.WEXITED int  -> 
      if int = 0 then ()
      else 
	failwith ("Clausification error: "^(!current_options.clausifier)^" exits with an error status: "
		  ^(string_of_int int))

(*	The process was killed by a signal; the argument is the signal number.	*)
  | 	Unix.WSIGNALED int -> 
      failwith ("Clausification error: "^(!current_options.clausifier)^" prover was killed by a signal: "
		^(string_of_int int))
	(*	The process was stopped by a signal; the argument is the signal number.	*)
  | 	Unix.WSTOPPED int ->
      failwith ("Clausification error: "^(!current_options.clausifier)^" was stopped by a signal: "
		^(string_of_int int))

let get_line_num_lexbuf lexbuf = 
  let position = (Lexing.lexeme_end_p lexbuf) in
  let line_number = position.Lexing.pos_lnum in
  line_number


    
let parse_channel channel_name in_channel = 
  let lexbuf = (Lexing.from_channel in_channel) in
  let () = init_lexbuf channel_name lexbuf in
  Parser_types.assign_current_buffer_name (channel_name);
  try     
    (parser_main_fun lexer_token lexbuf) 
  with 
  |Parsing_fails when !input_problem_type = Some(CNF)  (* for dbg comment when *) -> (* otherwise continue with the exception *)
      let line_number = (get_line_num_lexbuf lexbuf) in
      let fail_str = "Parse error in: "^(buffer_name_to_string channel_name)
	^" line: "^(string_of_int line_number)
	^" near token: \'"^(Lexing.lexeme lexbuf)^"\'" in 
      failwith fail_str

	


(*---------- Clausifying by an external clausifier and parsing by iProver -------*)

let clausify_parse_channel clausifier_full_cmd channel_name in_channel = 

  let env = Unix.environment () in  

  let cl_out_pipe_out, cl_out_pipe_in = Unix.pipe () in
  let cl_out_pipe_out_ch = Unix.in_channel_of_descr  cl_out_pipe_out in 
(* won't need *)
  let _cl_out_pipe_in_ch  = Unix.out_channel_of_descr cl_out_pipe_in in 

(*
  let cl_err_pipe_out, cl_err_pipe_in = Unix.pipe () in
  let cl_err_pipe_out_ch = Unix.in_channel_of_descr cl_err_pipe_out in 
 *)

(* won't need *)
(*  let _cl_err_pipe_in_ch  = Unix.out_channel_of_descr cl_err_pipe_in in *)

(* add redirection of cl_error into error_channel *)

  let cmd_args_list 
      =  Str.split (Str.regexp "[ ]+") (clausifier_full_cmd) in
  let cmd_args = Array.of_list cmd_args_list in
  let cmd_name = cmd_args.(0) in

  let in_dscr = (Unix.descr_of_in_channel in_channel) in

  prerr_newline ();
  let cl_pid = 
    Unix.create_process_env cmd_name cmd_args env
      in_dscr cl_out_pipe_in Unix.stderr (*cl_err_pipe_in*)
  in

  prerr_newline ();
(* cat_pid is used for testing: just redirects input into output *)
(*
  let cat_pid = 
  Unix.create_process_env "cat" (Array.of_list ["cat"]) env
  (Unix.descr_of_in_channel in_channel)
  e_out_pipe_in e_err_pipe_in
  in
 *)

(* ! We need to close this end of pipe since it is copyied to the process !*)
(* Otherwise EOF is not sent which creats a bolck*)
  Unix.close in_dscr;
  Unix.close cl_out_pipe_in;
(*  Unix.close cl_err_pipe_in;*)

  add_child_process cl_pid;
  parse_channel channel_name cl_out_pipe_out_ch;
  let cl_pid_, cl_status = Unix.waitpid [Unix.WUNTRACED] cl_pid in 
(*  check_clausifier_error_channel stderr cl_err_pipe_out_ch;*)
  Unix.close cl_out_pipe_out;
  check_clausifier_process_status cl_status



(*----------------------------------------------------------------------------*)
(* parse file (input files and includes)                                      *)


let adjust_input_file_name file_name = 
  if Filename.is_relative file_name 
  then
    (Filename.concat 
       (remove_double_quotes !current_options.problem_path) file_name)
  else 
    file_name


      

(*---------- Clausifying by an external clausifier and parsing by iProver ---------*)

let ext_clausify_parse problem_files =
  let (clausifier_cmd,options) = clausifier_cmd_options ~pure_cnf_flag:true  in
  let clausifier_full_cmd = clausifier_cmd^" "^options in
  let clausifier_short_name = Filename.basename clausifier_cmd in
  print_string 
    ("\n"^(s_pref_str ())^"Clausification by "^clausifier_short_name^"  & Parsing by iProver");
  flush stdout;
  (   
      try 	
	(* Check if environment variable set *)
	ignore (Unix.getenv "TPTP")	  
      with Not_found ->
	(* Pass include path on to E via $TPTP *)
	if not (!current_options.include_path = "")
	then
  	  Unix.putenv "TPTP" !current_options.include_path	  
	else ()
     );

  (* we assume that includes are infolded by the external clausifier *)
  begin
    if !current_options.stdin then
      ( print_string " from stdin...";
	flush stdout;
	clausify_parse_channel clausifier_full_cmd (*"sdtin"*) Stdin stdin
       )    
    else
      (print_string "...";
       flush stdout;    
       let parse_one_file file_name = 
	 let full_file_name = (adjust_input_file_name file_name) in 
	 let in_channel = open_in full_file_name in
	 clausify_parse_channel 
	   clausifier_full_cmd (* (FileName(full_file_name))*) (Parser_types.Clausifier("clausifier")) in_channel 
       in
       List.iter parse_one_file problem_files
      )
  end




(*--------------parsing with iProver (without ext. clausifier)--------------*)

    (* parse all includes *)
    
let include_full_file_name includes =
  if Filename.is_relative includes.includes_file_name
  then 
    if not (!current_options.include_path = "") (* input option takes priority *)
    then
      (Filename.concat 
	 (remove_double_quotes !current_options.include_path) 
	 includes.includes_file_name)
    else
      (* check whether the file is in the dirctory of the source file *)
      let source_dir =  
	match includes.include_source_file_name with 
	|FileName source_file_name -> Filename.dirname source_file_name
	|Stdin | Clausifier _ -> Filename.current_dir_name 
      in 
      let full_file_name = Filename.concat source_dir includes.includes_file_name in 
      if (Sys.file_exists full_file_name) 
      then 
	full_file_name 
      else
	try 
	  let tptp_path = (Unix.getenv "TPTP")	in	
	  (Filename.concat tptp_path includes.includes_file_name)  	   
	with Not_found ->
	  includes.includes_file_name     	     
  else (* absolute path *)
    includes.includes_file_name
      

module StrSet = Set.Make (String)

(* not used ?*)
(*
let get_file_name_from_buffer_name  bn = 
  match bn with 
  | FileName str -> str
  | Stdin -> failwith "get_file_name_from_buffer_name: should not be Stdin"
  | Clausifier _ -> 	ailwith "get_file_name_from_buffer_name: should not be Clausifier"
*)
	
let parse_files problem_files = 
  print_string ((s_pref_str ())^"Parsing");
  flush stdout;
  let parsed_file_set_ref = ref StrSet.empty in
  
(*----- Parse includes after parsing a file ----*)
  let rec parse_includes (*current_file_name*) () =
    let current_includes = !includes in
    includes := [];
    List.iter 
      (fun current_include -> 
	if current_include.include_formula_list != []
	then 
	  failwith "Formula selection is not supported in includes"
	else
	  (
	   let include_file_name = include_full_file_name current_include in
	   parse_one_file include_file_name
	  )
      )
      current_includes;
  and
      parse_one_file file_name = 
    let full_file_name = (* (adjust_input_file_name file_name)*) file_name in
    if (not (StrSet.mem full_file_name !parsed_file_set_ref)) 
    then
      (
(* out_str ("\n open full_file_name: "^full_file_name^"\n");*)
       
       let in_channel = open_in full_file_name in
       parse_channel (FileName (full_file_name)) in_channel; 
       close_in in_channel;
       parsed_file_set_ref := StrSet.add full_file_name !parsed_file_set_ref;
       parse_includes ();
      )
    else (* already parsed this file *) 
      ()
  in  
  begin
    if !current_options.stdin then
      (print_string " from stdin...";
       flush stdout;
       parse_channel (*"stdin"*) Stdin stdin      
      )
    else
      (print_string "...";
       flush stdout;
       List.iter parse_one_file problem_files
      )
  end;
  out_str "successful\n"
    
(*
let parse_qbf () = 
  print_string ((s_pref_str ())^"Parsing QBF ");
  flush stdout;
  let clause_list =
    if !current_options.stdin then
      (print_string "from stdin...";
       flush stdout;
       Qbf_fof.qbf_parse_to_fof_stdin ()
      )
    else
      (print_string "...";
       flush stdout;
       let input_file = (List.hd !current_options.problem_files) in 
       (if ((List.length !current_options.problem_files) > 1) 
       then 
         out_warning ("QBF processing only first file; the rest are ignored");
       );
       Qbf_fof.qbf_parse_to_fof_file input_file
      )
  in
  out_str "successful\n";
  Parser_types.parsed_clauses := clause_list
  *)
    
let parse () = 
  begin
(* with "--stdin true" and "--fof true" we need to parse with clausifier*)
(* otherwise we first try to parse iprover and if it raises *)
(* Parser_types.FOF_format then parse with a clausifier *)

    if !current_options.aig_mode
    then 
      failwith "Aiger input is not supported"
    else 
      if !current_options.qbf_mode
      then 
      begin (* TODO *)
        input_problem_type:= Some(QBF);
(* qbf are parsed later *)        
      end
      else
(*
      if !current_options.qbf_mode
      then 
      begin (* TODO *)
        input_problem_type:= Some(QBF);
        parse_qbf ();
      end
      else
*)
        if (false && !current_options.stdin)
        then
        (input_problem_type:= Some(FOF);
         dbg D_trace (lazy ("input_problem_type: FOF"));
         ext_clausify_parse !current_options.problem_files)
        else
        (try
 	  (
(* Empty_clause can be raised during parsing so we need to assign problem_type before *)
	   input_problem_type:= Some(CNF); 
           dbg D_trace (lazy ("input_problem_type: CNF"));
	   parse_files !current_options.problem_files;	 
	  ) 
        with 
        |Parser_types.FOF_format
        |Parser_types.Parsing_fails when !input_problem_type = Some(FOF)
          ->
	    (
	     input_problem_type:=Some(FOF);
             dbg D_trace (lazy ("input_problem_type: FOF"));
	     ext_clausify_parse !current_options.problem_files;	  
	    )
        |Parser_types.TFF_format 
        |Parser_types.Parsing_fails when !input_problem_type = Some(TFF)
          ->
	    (
	     input_problem_type:=Some(TFF);
             dbg D_trace (lazy ("input_problem_type: TFF"));
	     ext_clausify_parse !current_options.problem_files;	  
	    )

(*        |Parser_types.TFF_format -> failwith "TFF_format is not supported" *)
        |Parser_types.THF_format -> failwith "THF_format is not supported"
        )
  end




(*------------------------Commented----------------------*)
