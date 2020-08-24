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

let ()= out_str "\n---------------- rProver v0.1 ---------------\n"

type options = 
    {mutable problem_path : string; 
     mutable include_path : string; 
     mutable problem_files : string list}

(* --problem_path /home/TPTP-v3.0.1/Problems/ --input_file  Problems/ANA/ANA002-1.p*)      
(* --include_path /home/TPTP-v3.0.1/Problems/  "include('Axioms/SET003-0.ax')." *)

let default_options = 
  {problem_path  = "";
   include_path  = ""; 
   problem_files = []}

let options  = default_options
    
(*files are added in reverse order *)

let add_file_options options file_name = 
  options.problem_files <- file_name::options.problem_files
					
let default_arg_fun = add_file_options options

let input_file_fun  = default_arg_fun     

let problem_path_fun path = 
  options.problem_path <- path 

let include_path_fun path = 
  options.include_path <- path 

let spec_list = 
  [
   ("--problem_path", Arg.String(problem_path_fun), "problem path prefix");
   ("--include_path", Arg.String(include_path_fun), "include path prefix");
   ("--input_file", Arg.String(input_file_fun), "input file name")
 ]
    
let usage_msg = 
  "iproveropt [--problem_path path_prefix] [--include_path path_prefix] [--input_file file] input_file_1 ... input_file_n"
    
let read_args() = 
  Arg.parse spec_list default_arg_fun usage_msg
    
let () = read_args(); 
  if options.problem_files = [] then failwith "No problem files to solve"

let () = 
  let add_path fn = options.problem_path^fn in
  options.problem_files <- (List.map add_path options.problem_files)

(*
  let problem_files_out = 
  out_str_debug ("%Problem files: "^(list_of_str_to_str options.problem_files ",")^"\n")
 *) 

let parsed_all = 
  ParseFiles.parse_files options.include_path options.problem_files

let _ = Parsed_input_to_db.parsed_input_to_db parsed_all

(*let ()=out_str_debug ("debug iprover:\n "
  ^(Clause.clause_list_to_string !Parsed_input_to_db.clause_list_ref))
 *) 

(****************************************)
let () = Discount.start_discount ()
(****************************************)



(***********************various tests****************)



(*let ()=Discount.try_matching_all () *)

(*let ()=Discount.try_subsumption_all ()*)

(*
  module DTParam = struct let num_of_symb = (SymbolDB.size !symbol_db_ref) end
  module DiscrTreeM =  DiscrTree.Make(DTParam)
  
  let unif_index_ref = ref (DiscrTreeM.create ())

  let fill_unif_index term_db unif_index_ref= 
  let f term = 
  let elem_ref = DiscrTreeM.add_term_path term unif_index_ref in
  match !elem_ref with
  |Elem(elem)  -> elem_ref:= Elem(term::elem)
  |Empty_Elem  -> elem_ref:= Elem([term]) 
  in
  TermDB.iter f term_db 
  
  let () = fill_unif_index !term_db_ref unif_index_ref 

  let term_list_to_string t_list = 
  list_to_string Term.to_string t_list ";"

  let () = 
  let f clause =  
  out_str_debug ((Clause.to_string clause)^"--"
  ^"["^( term_list_to_string (Selection.literal_neg_selection clause))^"]") 
  in
  ClauseAssignDB.iter f !clause_db_ref

 *)

(*
  let () = 
  let f t = 
  let g s = 
  let cmp = Orderings.simple_kbo t s in  
  if cmp > cequal 
  then out_str_debug ("("^(Term.to_string t)^" greater than "^(Term.to_string s)^")") 
  else 
  if cmp =0 
  then  
  out_str_debug ("("^(Term.to_string t)^" greater or equal than "
  ^(Term.to_string s)^")")
  else 	
  out_str_debug ("("^(Term.to_string t)^" NOT greater or equal than "
  ^(Term.to_string s)^")")
  in
  TermDB.iter g !term_db_ref
  in TermDB.iter f !term_db_ref
 *)
(*
  let () = 
  let f term =
  let unif_cand_str =  
  term_list_to_string (DiscrTreeM.unif_candidates !unif_index_ref term ) in
  out_str_debug
  ( "Unif candidates for "^(Term.to_string term)^" is " 
  ^unif_cand_str^"\n") in
  TermDB.iter f !term_db_ref
 *)
