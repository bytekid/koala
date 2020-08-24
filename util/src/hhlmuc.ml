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


(********** Types definitions and helper functions **********)


(* An abstract solver instance *)
type hhlmuc_solver

(* An abstract literal in the solver *)
type hhlmuc_literal

(* A solver instance with flags and counters for number of calls *)
type solver = 
    { solver : hhlmuc_solver;
      mutable num_of_solver_calls : int;
      mutable num_of_fast_solver_calls : int;
      mutable is_simplification : bool }


(* A literal in the solver *)
type literal = hhlmuc_literal


(* A lifted Boolean value *)
type lbool = 
  | L_true
  | L_false
  | L_undef


(* Convert an integer to a lifted Boolean

   See SolverTypes.h in MiniSat sources for #define statements:
   L_true = 0, L_false = 1, L_undef = 2 *)
let int_to_lbool = function 
  | 0 -> L_true
  | 1 -> L_false
  | 2 -> L_undef
  | c -> invalid_arg (Format.sprintf "int_to_lbool %d" c)


(* The clause set is immediately unsatisfiable *)
exception Unsatisfiable


(********** Declarations of external functions **********)


(* Create a new instance *)
external hhlmuc_create_solver : unit -> hhlmuc_solver = "hhlmuc_create_solver" 

(* Add the given variable, allocating space for it and all preceding
   variables *)
external hhlmuc_add_var : hhlmuc_solver -> int -> unit = "hhlmuc_add_var"


(* Create and return a literal

   The variable is allocated if it was no allocated before, hence
   calling hhlmuc_add_var separately is not necessary *)
external hhlmuc_create_lit : hhlmuc_solver -> bool -> int -> hhlmuc_literal = "hhlmuc_create_lit"

(* Assert the clause  

   Return [false] if the clause set is immediately unsatisfiable *)
external hhlmuc_add_clause : hhlmuc_solver -> hhlmuc_literal list -> bool = "hhlmuc_add_clause"

(* Assert the clause as interesting and return a unique id 
   
   Return [(true, Some uid)] if the clause was added as [uid] to the
   solver, [(true, None)] if the clause was discarded by the solver
   and [(false, None)] if the clause set is immediately unsatisfiable 
*)
external hhlmuc_add_clause_with_id : hhlmuc_solver -> hhlmuc_literal list -> bool *  int option = "hhlmuc_add_clause_with_id" 

(* Test the given clause set for satisfiability *)
external hhlmuc_solve : hhlmuc_solver ->  bool = "hhlmuc_solve"

(* Test the given clause set for satisfiability when the given
   literals are to be made true *)
external hhlmuc_solve_assumptions : hhlmuc_solver -> hhlmuc_literal list -> int = "hhlmuc_solve_assumptions"


(* Test the given clause set for satisfiability when the given
   literals are to be made true. Limit the search to a number of
   conflicts, which is a multiple of the number of literal
   assumptions *)
external hhlmuc_fast_solve : hhlmuc_solver -> hhlmuc_literal list -> int -> int option = "hhlmuc_fast_solve"


(* Return the variable of the literal *)
external hhlmuc_lit_var : hhlmuc_solver -> hhlmuc_literal -> int = "hhlmuc_lit_var"


(* Return the sign of the literal *)
external hhlmuc_lit_sign : hhlmuc_solver -> hhlmuc_literal -> bool = "hhlmuc_lit_sign"


(* Return the truth value of the literal in the current model *)
external hhlmuc_model_value : hhlmuc_solver -> hhlmuc_literal -> int = "hhlmuc_model_value"


(* Return an unsatisfiable core as a list of clause ids *)
external hhlmuc_unsat_core : hhlmuc_solver -> int list = "hhlmuc_unsat_core"


(* Return the number of variables allocated *)
external hhlmuc_stat_vars : hhlmuc_solver -> int = "hhlmuc_stat_vars" 


(* Return the number of clauses *)
external hhlmuc_stat_clauses : hhlmuc_solver -> int = "hhlmuc_stat_clauses" 


(********** Top-level functions **********)


(* Create a new solver instance *)
let create_solver is_simplification =

  (* Create a new instance *)
  let solver = hhlmuc_create_solver () in

  (* Return record of solver instance *)
  { solver = solver;
    num_of_solver_calls = 0;
    num_of_fast_solver_calls = 0;
    is_simplification = is_simplification }
    
  
(* Allocate the variable in the solver *)
let add_var { solver = solver } var = hhlmuc_add_var solver var


(* Create and return a literal of the given variable and sign in the
   solver *)
let create_lit { solver = solver } sign var = 
  hhlmuc_create_lit solver sign var 
    
    
(* Assert a clause given as a list of literals in the solver. Raise
   {!Unsatisfiable} if the clause set becomes immediately
   unsatisfiable. *)
let add_clause { solver = solver } = function

  (* The empty clause is immediately unsatisfiable *)
  | [] -> raise Unsatisfiable 

  | clause -> 

    (* Add clause and check if immediately unsatisfiable *)
    if not (hhlmuc_add_clause solver clause) then

      (* Raise exception if immediately unsatisfiable *)
      raise Unsatisfiable

    
(* Assert a clause given as a list of literals in the solver. Raise
   {!Unsatisfiable} if the clause set becomes immediately
   unsatisfiable. *)
let add_clause_with_id { solver = solver } = function

  (* The empty clause is immediately unsatisfiable *)
  | [] -> raise Unsatisfiable 

  | clause -> 

    (

      (* Add clause and check if immediately unsatisfiable *)
      match hhlmuc_add_clause_with_id solver clause with
	  
	(* Raise exception if immediately unsatisfiable *)
	| false, _ -> raise Unsatisfiable

	(* Pass on any other result *)
	| true, uid -> uid
    
    )

(* Test the given clause set for satisfiability *)
let solve ({ solver = solver } as s) = 

  (* Increment counter *)
  s.num_of_solver_calls <- succ s.num_of_solver_calls;
  
  hhlmuc_solve solver 
  

(** Test the given clause set for satisfiability when the given
    literals are to be made true *)
let solve_assumptions ({ solver = solver } as s) assumptions =

  (* Increment counter *)
  s.num_of_solver_calls <- succ s.num_of_solver_calls;

  (* Solve with literal assumptions *)
  match int_to_lbool (hhlmuc_solve_assumptions solver assumptions) with 

    (* Satisfiable with assumptions *)
    | L_true -> true

    (* Unsatisfiable with assumptions *)
    | L_false -> false 

    (* Unsatisfiable without assumptions *)
    | L_undef -> raise Unsatisfiable 


(* Test the given clause set for satisfiability when the given
   literals are to be made true. Limit the search to a number of
   conflicts, which is a multiple of the number of literal
   assumptions *)
let fast_solve ({ solver = solver } as s) assumptions = 

  (* Increment counter *)
  s.num_of_fast_solver_calls <- succ s.num_of_fast_solver_calls;

  (* Solve with literal assumptions *)
  match hhlmuc_fast_solve solver assumptions 1 with 

    (* Satisfiable with assumptions *)
    | Some l when int_to_lbool (l) = L_true -> Some true

    (* Unsatisfiable with assumptions *)
    | Some l when int_to_lbool (l) = L_false -> Some false 

    (* Unsatisfiable without assumptions *)
    | Some l when int_to_lbool (l) = L_undef -> raise Unsatisfiable 

    (* Unknown *)
    | None -> None

    (* Catch integers that are not mapped to a lifter Boolean, but the
       exception would already be raised in when guards above *)
    | Some _ -> invalid_arg "int_to_lbool"


(* Return the propositional variable in the literal *)
let lit_var { solver = solver } literal = 
  hhlmuc_lit_var solver literal


(* Return the sign of the literal *)
let lit_sign { solver = solver } literal = 
  hhlmuc_lit_sign solver literal


(* Return the truth value of the literal in the current model *)
let model_value { solver = solver } literal = 

  (* Get model value of literal in solver *)
  match int_to_lbool (hhlmuc_model_value solver literal) with 

    (* Literal is true *)
    | L_true -> Some true 

    (* Literal is false *)
    | L_false -> Some false

    (* Literal is undefined *)
    | L_undef -> None


(* Return an unsatisfiable core *)
let unsat_core { solver = solver } =
  hhlmuc_unsat_core solver


(* Return the number of calls to {!solve} of the solver instance *)
let num_of_solver_calls { num_of_solver_calls = n } = n


(** Return the number of calls to {!fast_solve} of the solver instance *)
let num_of_fast_solver_calls { num_of_fast_solver_calls = n } = n


(* Return the number of propositional variables in the solver instance *)
let num_of_vars { solver = solver } = hhlmuc_stat_vars solver


(* Return the number of propositional variables in the solver instance *)
let num_of_clauses { solver = solver } = hhlmuc_stat_clauses solver


(* Return true if the solver was created as a simplification solver *)
let is_simplification { is_simplification = b } = b


(********** Output functions **********)


(* Pretty-print a lifted Boolean value *)
let pp_lbool ppf = function 
  | L_true -> Format.fprintf ppf "L_true"
  | L_false -> Format.fprintf ppf "L_false"
  | L_undef -> Format.fprintf ppf "L_undef"


(* Pretty-print a lifted Boolean value *)
let pp_bool_option ppf = function 
  | Some true -> Format.fprintf ppf "true"
  | Some false -> Format.fprintf ppf "false"
  | None -> Format.fprintf ppf "undef"


(* Pretty-print a literal *)
let pp_literal solver ppf literal = 
  
  (* Open horizontal box *)
  Format.fprintf ppf "@[<h>";

  (* Print sign of literal *)
  (match lit_sign solver literal with 
    | true -> ()
    | false -> Format.fprintf ppf "-");

  (* Print variable of literal and close box *)
  Format.fprintf ppf "%d@]" (lit_var solver literal)


(* Pretty-print a list of literals *)
let rec pp_literal_list solver ppf = function 
  | [] -> ()
  | [l] -> Format.fprintf ppf "%a" (pp_literal solver) l
  | l::tl -> 
    Format.fprintf ppf "%a@ " (pp_literal solver) l; 
    pp_literal_list solver ppf tl


(* Return a string representation of the literal *)
let literal_to_string solver literal = 
  Format.fprintf Format.str_formatter "%a" (pp_literal solver) literal;
  Format.flush_str_formatter ()


(* Return a string representation of the list of literals *)
let literal_list_to_string solver literals = 
  Format.fprintf 
    Format.str_formatter 
    "@[<hv>%a@]" 
    (pp_literal_list solver) 
    literals;
  Format.flush_str_formatter ()
  
