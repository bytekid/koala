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






(* parse_files from file_names list  *)
(* unfolds includes *)
(* output can be used as follows: *)
(*let _ = Parsed_input_to_db.parsed_input_to_db (parse_files file_names) *)
(* this will fill all db in *)
(*  Parsed_input_to_db.symbol_db_ref    *) 
(*  Parsed_input_to_db.term_db_ref      *)
(*  Parsed_input_to_db.clause_list_ref  *)
(* see discount.ml for example of such usage *)

(* clausify_parse file_name_list *)

(*
(*val clausify_parse :  string list -> Parser_types.parsing_type*)
val clausify_parse :  string list -> unit

(* parse_files  include_path file_name_list *)
(*val parse_files : string -> string list -> Parser_types.parsing_type*)
val parse_files : string -> string list -> unit
*)

(*
type input_problem_type = FOF | CNF | TFF | THF | AIG | QBF

val input_problem_type : ((input_problem_type option) ref)
*)

val clausifier_cmd_options : pure_cnf_flag:bool -> string * string

val parse : unit -> unit
