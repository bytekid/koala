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


(*
  
  Created: 2011-12-07 Christoph Sticksel

*)

(** {1 Types and exceptions} *)

(** An abstract solver instance *)
type solver

(** An abstract literal in a solver instance *)
type literal


(* exception Unsatisfiable_prop  *)   (* unsatisfiable ground without assumtions *)
exception Unsatisfiable_prop_na (* unsatisfiable ground possibly with assumtions *)



(** {1 Interaction with the solver} *)

(** [create_solver s] creates and returns a new solver instance

    The solver is a simplification solver if [s] is [true]. *)
val create_solver : bool -> solver 

(** [add_var s v] adds the propositional variable [v] to the solver

    Each variable has to be allocated in the solver although
    {!create_lit} does this for each variable that has not been
    allocated.

    Variables are integers, the first variable is 0.
*)
val add_var : solver -> int -> unit

(** [create_lit s n v] creates and returns a literal of the propositional
    variable [v] with sign [n] in the solver instance [s]

    Variables are integers, the first variable is 0. Use [true] for a
    positive and [false] for a negative literal. Variables not
    allocated in the solver will be allocated by this function, hence
    it is not necessary to call {!add_var} separately.
*)
val create_lit:  solver -> bool -> int -> literal

(** [add_clause s c] asserts the clause [c] given as a list of literals
    in the solver instance [s]

    May raise {!Unsatisfiable;!Unsatisfiable_NA} if the clause set becomes immediately
    unsatisfiable. *)

val add_clause: solver -> literal list -> unit

(** [add_clause s c] asserts the clause [c] given as a list of literals
    as an interesting constraint in the solver instance [s]

    May raise  {!Unsatisfiable;!Unsatisfiable_NA} if the clause set becomes immediately
    unsatisfiable, otherwise return a unique identifier for the
    clause. *)

val add_clause_with_id : solver -> int option -> literal list -> int option

(** Test the given clause set for satisfiability 

    Return [true] if satisfiable and [false] if unsatisfiable *)

(* TODO: implement reset*)
val solve : ?reset:bool -> solver -> bool
val solve_upto_id : solver -> int -> bool

(** Test the given clause set for satisfiability when the given
    literals are to be made true. 

    Return [true] if satisfiable with assumptions, [false] if
    unsatisfiable with assumptions and raise exception
    {!Unsatisfiable;!Unsatisfiable_NA} if immediately unsatisfiable without
    assumptions. *)

(* TODO implement reset *)
val solve_assumptions : ?reset:bool -> solver -> literal list -> bool
val solve_assumptions_upto_id : solver -> literal list -> int -> bool

(** Test the given clause set for satisfiability when the given
    literals are to be made true. 

    Return [true] if satisfiable with assumptions, [false] if
    unsatisfiable with assumptions and raise exception
    {!Unsatisfiable;!Unsatisfiable_NA} if immediately unsatisfiable without
    assumptions. *)
val fast_solve : solver -> literal list -> bool option
val fast_solve_upto_id : solver -> literal list -> int -> bool option

(** {1 Inspection} *)

(** Return the truth value of the literal in the current model 

    [Some true] if the literal is true, [Some false] if the literal is
    false and [None] if the literal value is undefined *)
val model_value : solver -> literal -> bool option

(** Return the model after a satisfiable solve call 

    The n-th element of the array is the truth value of the n-th
    variable. [None] if the truth value is undefined, [Some true] for
    a variable that is assigned [true] and [Some false] for a variable
    that is assigned false.
*)
val get_model : solver -> bool option array

(** Return the final conflict clause after an unsatisfiable solve call 

    Each signed integer in the list is a literal, the sign
    representing the sign of the literal and the absolute value the
    variable.
*)
val get_conflicts : solver -> int list 

val minimise_core : solver -> int list -> int list  

(** Return an unsatisfiable core *)
val unsat_core : solver -> int list 

(** Return the propositional variable in the literal *)
val lit_var : solver -> literal -> int

(** Return the sign of the literal, [true] for a positive and [false]
    for a negative literal *)
val lit_sign : solver -> literal -> bool

val get_lit_id : literal -> int


(** Return the number of clauses containing a unique tracking literal *)
val clauses_with_id : solver -> int

(** {1 Statistics} *)

(** Return the number of calls to {!solve} of the solver instance *)
val num_of_solver_calls : solver -> int

(** Return the number of calls to {!fast_solve} of the solver instance *)
val num_of_fast_solver_calls : solver -> int

(** Return the number of propositional variables in the solver instance *)
val num_of_vars : solver -> int

(** Return the number of clauses in the solver instance *)
val num_of_clauses : solver -> int

(** Return [true] if the solver was created as a simplification
    solver in {!create_solver} *)
val is_simplification : solver -> bool

val reset_solver : solver -> unit

val delete_solver : solver -> unit

(* TODO: implement set_important_lit *)
val set_important_lit : solver -> literal -> unit

(* set variable to a decision/non-decision var (by default all vars are decision vars); *)
(* if set false then semantics of SAT can change  *)
val set_decision_var : solver ->  bool -> literal -> unit 

(** {1 Output and string representations} *)

(** Pretty-print the literal into the formatter *)
val pp_literal : solver -> Format.formatter -> literal -> unit 

(** Pretty-print the list of literals into the formatter *)
val pp_literal_list : solver -> Format.formatter -> literal list -> unit 

(** Return a string representation of the literal *)
val literal_to_string : solver -> literal -> string

(** Return a string representation of the list of literals *)
val literal_list_to_string : solver -> literal list -> string


(** Returns next implied unit clause at the 0 decision level; raises Not_found if no new implied units *)
val get_next_implied_unit: solver -> literal

(** Returns next implied unit clause at the assumption decision level; raises Not_found if no new implied untis *)
(**  here fist implied unit starts from first decision literal *)
(**  resets with each solve; solve_assumptions; fast_solve *)
val get_next_ass_implied_unit: solver -> literal
