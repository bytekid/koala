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






type clause = Clause.clause

val symbol_db_ref : SymbolDB.symbolDB ref 
(*
val neg_symb      : Symbol.symbol 
val equality_symb : Symbol.symbol 
val bot_symb      : Symbol.symbol
*)
val bot_term      : Term.term
val top_term      : Term.term

val term_db_ref   : TermDB.termDB ref 

(* input clauses include neg_conjectures*)
val input_clauses_ref : (clause list) ref
val input_neg_conjectures_ref : (clause list) ref

(*val clause_db_ref : ClauseAssignDB.clauseDB ref*)
val e_prover_parsing_success : bool ref

(* fill all db's above and returns clause list*)
(*val parsed_input_to_db : Parser_types.parsing_type -> Clause.clause list*)
val parsed_input_to_db : Parser_types.parsing_type -> unit 

val parsed_input_to_db_debug : Parser_types.parsing_type -> unit 
