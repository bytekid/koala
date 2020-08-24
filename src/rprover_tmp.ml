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







(* processing args can be moved later in iprover.ml*)
open Lib
open Printf
open Parser_types

let parser_main_fun = Parser_tptp.main
let lexer_token = Lexer_tptp.token
type options = {mutable problem_files : string list}
      
      
let default_options = {problem_files = []}
let options  = default_options
    
(*files are added in reverse order *)

let add_file_options options file_name = 
  options.problem_files <- file_name::options.problem_files
					
let default_arg_fun = add_file_options options
let input_file_fun  = default_arg_fun     
let spec_list = 
  [("-input_file", Arg.String(input_file_fun), "input file name")]
        
let usage_msg = "read_input [--input_file file] input_file_1 ... input_file_N"
    
let read_args() = 
  Arg.parse spec_list default_arg_fun usage_msg
    
let () = read_args(); 
  if options.problem_files = [] then failwith "No problem files to solve"

(*
let problem_files_out = 
  out_str_debug ("%Problem files: "^(list_of_str_to_str options.problem_files ",")^"\n")
*) 


let parse_list file_name_list= 
  let parse_one_file rest file_name = 
    let file = open_in file_name in
    let lexbuf = (Lexing.from_channel file) in
    let ()= init_lexbuf lexbuf in
    let add_parsed_list=
      try (parser_main_fun lexer_token lexbuf) 
      with  
      |Parsing_fails -> 
         let position = (Lexing.lexeme_end_p lexbuf) in
	 let line_number = position.Lexing.pos_lnum in
	  let fail_str = "Parse error in file: "
	    ^file_name^" line: "^(string_of_int line_number) in 
          failwith fail_str
      |_ -> failwith "parse unknown error"
   in
    let ()= close_in file in
    add_parsed_list@rest 
  in
  List.fold_left parse_one_file [] file_name_list
    
let parsed_input_files = parse_list options.problem_files

 
  
(* circular inputs detected and added once*)
let rec unfold_includes' parsed_list added_files_ref= 
  match parsed_list with
  |Include(file_name,[])::tl ->  
      if List.mem file_name !added_files_ref 
      then (unfold_includes' tl added_files_ref)
      else
	(added_files_ref:= file_name::!added_files_ref;
      let add_parsed_list = parse_list [file_name] in 
 (*         out_str file_name; *)
          unfold_includes' (add_parsed_list@tl) added_files_ref)
	  
  |Include(_,_::_)::tl ->  	  
       failwith "fromula selection in include is not supported yet"
  |h::tl-> h::(unfold_includes' tl  added_files_ref)
  |[]->[]
	
let unfold_includes parsed_list = 
  let added_files_ref = ref [] in
  unfold_includes' parsed_list added_files_ref

let parsed_all = unfold_includes parsed_input_files

(*
let all_in_str = parsing_type_to_string  parsed_all
let () = 
  out_str_debug ("Parsed formulas: \n"^all_in_str^"end of parsed formulas \n") 
*)
	

let symbol_db_ref = Parsed_input_to_db.symbol_db_ref
let term_db_ref   = Parsed_input_to_db.term_db_ref
(* let clause_db_ref = Parsed_input_to_db.clause_db_ref *)


let input_clauses = 
 Parsed_input_to_db.parsed_input_to_db parsed_all

(*
let () = out_str_debug (SymbolDB.to_string !symbol_db_ref)
let () = out_str_debug (TermDB.to_string !term_db_ref)
*)
(* let () = out_str (ClauseAssignDB.to_string !clause_db_ref) *)

(* uncomment this for discount *)
let () = Discount.start_discount ()




(*various tests*)
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
