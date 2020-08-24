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


open Logic_interface

type lm_input = 
  {
   lm_input_clauses : clause list; (* a ground set of clauses *)
   lm_is_ignore_pred : (symbol-> bool); (* ignore literals with preds in this set *)
  
   lm_is_ignore_type : (symbol -> bool);
 (* do not lift constants  with this type; should include bot_type as lifting to X_bot can cause type_checking problems during unification
   (via bot_type can wrongly equate two different non_bot types ) *)
}

type lm_state

val create_lm_state : lm_input -> lm_state

val get_ground_lemmas : lm_state -> clause list

val get_lifted_lemmas : lm_state -> clause list
