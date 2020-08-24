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

(* KK: minisat here should be renamed to a generic unsat core solver *)

(* Unsatisfiable_gr_uc;  Unsatisfiable_gr_na_uc repeat exeptions as in iprover/src/lib.ml for unsat core solver *)



(* exception Unsatisfiable_prop *)    (* unsatisfiable ground possibly with assumtions *)
exception Unsatisfiable_prop_na  (* unsatisfiable ground without assumtions *)


(*----- Types definitions and helper functions -------*)


(* An abstract solver instance *)
type minisat_solver

(* An abstract literal in the solver *)
type minisat_literal

(* A solver instance with flags and counters for number of calls *)
type solver = 
    { solver : minisat_solver;
      mutable num_of_solver_calls : int;
      mutable num_of_fast_solver_calls : int;
      mutable is_simplification : bool 
    }


(* A literal in the solver *)
type literal = minisat_literal


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


let lit_None = -2

(********** Declarations of external functions **********)


(* Create a new MiniSat instance *)
external minisat_create_solver : unit -> minisat_solver = "minisat_create_solver" 

(* Add the given variable to MiniSat, allocating space for it and all
   preceding variables *)
external minisat_add_var : minisat_solver -> int -> unit = "minisat_add_var"


(* Create and return a literal in MiniSat

   The variable is allocated if it was no allocated before, hence
   calling minisat_add_var separately is not necessary *)
external minisat_create_lit : minisat_solver -> bool -> int -> minisat_literal = "minisat_create_lit"

(* set variable to a decision/non-decision var (by default all vars are decision vars); *)
(* if set false then semantics of SAT can change  *)
external minisat_set_decision_var : minisat_solver -> bool -> minisat_literal -> unit = "minisat_set_decision_var"

(* Assert the clause in MiniSat. 

   Return [false] if the clause set is immediately unsatisfiable *)
external minisat_add_clause : minisat_solver -> minisat_literal list -> bool = "minisat_add_clause"


(* Assert a clause, given as a list of literals, as an interesting
   constraint clause. Return both a flag if the clause is immediately
   unsatisfiable and a possibly undefined unique id for the clause.
   
   The unique id is [None] if the clause was simplified or if it is
   unsatisfiable. A return value of [(false, None)] means the clause
   is immediately unsatisfiable, if [(true, None)] is returned, the
   clause is already satisfied, otherwise the return value is [(true,
   Some id)].

   The clause is added with a tracking literal appended that is the
   unique ID of the clause. A new tracking variable is created if the
   parameter is None, otherwise the variable given is used to track
   the clause. *)
external minisat_add_clause_with_id : minisat_solver -> int option -> minisat_literal list -> bool * int option = "minisat_add_clause_with_id" 

(* Test the given clause set for satisfiability *)
external minisat_solve : minisat_solver -> int option ->  bool = "minisat_solve"

(* Test the given clause set for satisfiability when the given
   literals are to be made true *)
external minisat_solve_assumptions : minisat_solver -> minisat_literal list -> int option -> int = "minisat_solve_assumptions"


(* Test the given clause set for satisfiability when the given
   literals are to be made true. Limit the search to a number of
   conflicts, which is a multiple of the number of literal
   assumptions *)
external minisat_fast_solve : minisat_solver -> minisat_literal list -> int -> int option -> int option = "minisat_fast_solve"


(* Return the variable of the literal *)
external minisat_lit_var : minisat_solver -> minisat_literal -> int = "minisat_lit_var"


(* Return the sign of the literal *)
external minisat_lit_sign : minisat_solver -> minisat_literal -> bool = "minisat_lit_sign"


(* Return the number of clauses containing a unique tracking literal *)
external minisat_clauses_with_id : minisat_solver -> int = "minisat_clauses_with_id"
    
(* Return the truth value of the literal in the current model *)
external minisat_model_value : minisat_solver -> minisat_literal -> int = "minisat_model_value"

(* Return the model after a satisfiable solve call *)
external minisat_get_model : minisat_solver -> bool option array = "minisat_get_model"

(* Return the final conflict clause after an unsatisfiable solve call *)
external minisat_get_conflicts : minisat_solver -> int list = "minisat_get_conflicts"

(* Minimise an unsatisfiable core *)
external minisat_minimise_core : minisat_solver -> int list -> int list = "minisat_minimise_core"

(* Return the number of variables allocated in MiniSat *)
external minisat_stat_vars : minisat_solver -> int = "minisat_stat_vars" 


(* Return the number of clauses in MiniSat *)
external minisat_stat_clauses : minisat_solver -> int = "minisat_stat_clauses" 

external minisat_reset_solver : minisat_solver -> unit = "minisat_reset_solver"

external minisat_delete_solver : minisat_solver -> unit = "minisat_delete_solver"

(* can raise Not_found *)
external minisat_next_impl_unit : minisat_solver -> minisat_literal = "minisat_next_impl_unit"
external minisat_next_ass_impl_unit : minisat_solver -> minisat_literal = "minisat_next_ass_impl_unit"

external minisat_get_lit_id : minisat_literal -> int = "minisat_get_lit_id"


(********** Top-level functions **********)

(* Return the propositional variable in the literal *)
let lit_var { solver = solver } literal = 
  minisat_lit_var solver literal


(* Return the sign of the literal *)
let lit_sign { solver = solver } literal = 
  minisat_lit_sign solver literal


(* Return the number of clauses containing a unique tracking literal *)
let clauses_with_id { solver = solver } = 
  minisat_clauses_with_id solver 


(* Return the truth value of the literal in the current model *)
let model_value { solver = solver } literal = 

  (* Get model value of literal in solver *)
  match int_to_lbool (minisat_model_value solver literal) with 

    (* Literal is true *)
    | L_true -> Some true 

    (* Literal is false *)
    | L_false -> Some false

    (* Literal is undefined *)
    | L_undef -> None


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
  
(*-----------------------------------------*)

(* Create a new solver instance *)
let create_solver is_simplification =

  (* Create a new MiniSat instance *)
  let solver = minisat_create_solver () in

  (* Return record of solver instance *)
  { solver = solver;
    num_of_solver_calls = 0;
    num_of_fast_solver_calls = 0;
    is_simplification = is_simplification }
    
  
(* Allocate the variable in the solver *)
let add_var { solver = solver } var = minisat_add_var solver var


(* Create and return a literal of the given variable and sign in the
   solver *)
let create_lit { solver = solver } sign var = 
  minisat_create_lit solver sign var 
    


(* Assert a clause given as a list of literals in the solver. Raise
   {!Unsatisfiable_prop_na} if the clause set becomes immediately
   unsatisfiable. *)
let add_clause { solver = solver } = function

  (* The empty clause is immediately unsatisfiable *)
  | [] -> raise Unsatisfiable_prop_na

  | clause -> 

    (* Add clause to MiniSat and check if immediately unsatisfiable *)
    if not (minisat_add_clause solver clause) then

      (* Raise exception if immediately unsatisfiable *)
      raise Unsatisfiable_prop_na

    
(* Assert a clause given as a list of literals in the solver. Raise
   {!Unsatisfiable_prop_na} if the clause set becomes immediately
   unsatisfiable. *)
let add_clause_with_id { solver = solver } id = function

  (* The empty clause is immediately unsatisfiable, but do not catch
     this, since we might want to get an unsat core containing the empty
     clause *)
  (* | [] -> raise Unsatisfiable *)

  | clause -> 

    (

      (* Add clause and check if immediately unsatisfiable *)
      match minisat_add_clause_with_id solver id clause with
	  

	(* Raise exception if immediately unsatisfiable; *)
       (* Solver should not be used after this in particular clause id's will be shifted due to the clause not beeing 
          added clause but tracking variable was created *)

	| false, _ -> raise Unsatisfiable_prop_na 

	(* Pass on any other result *)
	| true, uid -> uid
    
    )


(* Test the given clause set for satisfiability *)
let solve ?(reset=false) ({ solver = solver } as s) = 

(* TODO implement reset; at the moment ignored *)

  (* Increment counter *)
  s.num_of_solver_calls <- succ s.num_of_solver_calls;
  
  minisat_solve solver None


(* Test the given clause set for satisfiability *)
let solve_upto_id ({ solver = solver } as s) max_id = 

  (* Increment counter *)
  s.num_of_solver_calls <- succ s.num_of_solver_calls;
  
  minisat_solve solver (Some max_id)
  

(** Test the given clause set for satisfiability when the given
    literals are to be made true *)
let solve_assumptions ?(reset = false) ({ solver = solver } as s) assumptions =

  (* Increment counter *)
  s.num_of_solver_calls <- succ s.num_of_solver_calls;

  (* Solve with literal assumptions *)
  match 
    int_to_lbool (minisat_solve_assumptions solver assumptions None) 
  with 

    (* Satisfiable with assumptions *)
    | L_true -> true

    (* Unsatisfiable with assumptions *)
    | L_false -> false 

    (* Unsatisfiable without assumptions *)
    | L_undef -> raise Unsatisfiable_prop_na

let solve_assumptions_upto_id ({ solver = solver } as s) assumptions max_id =

  (* Increment counter *)
  s.num_of_solver_calls <- succ s.num_of_solver_calls;

  (* Solve with literal assumptions *)
  match 
    int_to_lbool (minisat_solve_assumptions solver assumptions (Some max_id )) 
  with 

    (* Satisfiable with assumptions *)
    | L_true -> true

    (* Unsatisfiable with assumptions *)
    | L_false -> false 

    (* Unsatisfiable without assumptions *)
    | L_undef -> raise Unsatisfiable_prop_na




(* Test the given clause set for satisfiability when the given
   literals are to be made true. Limit the search to a number of
   conflicts, which is a multiple of the number of literal
   assumptions *)
let fast_solve ({ solver = solver } as s) assumptions = 

 (* print_endline (literal_list_to_string s assumptions); *)

  (* Increment counter *)
  s.num_of_fast_solver_calls <- succ s.num_of_fast_solver_calls;


  (* Solve with literal assumptions *)
  match minisat_fast_solve solver assumptions 1 None with 

    (* Satisfiable with assumptions *)
    | Some l when int_to_lbool (l) = L_true -> 
(*        print_endline ("minisat.ml: dbg: fast_solve: true"); *)
        Some true

    (* Unsatisfiable with assumptions *)
    | Some l when int_to_lbool (l) = L_false -> 
(*        print_endline ("minisat.ml: dbg: fast_solve: false"); *)
        Some false 

          (* Unsatisfiable without assumptions *)
    | Some l when int_to_lbool (l) = L_undef -> 
(*        failwith (" dbg: minisat.ml: fast_solve: Unsatisfiable_prop_na"); *)
        raise Unsatisfiable_prop_na 
          
    (* Unknown *)
    | None -> 
(*        print_endline ("minisat.ml: dbg: fast_solve: None"); *)
        None

    (* Catch integers that are not mapped to a lifter Boolean, but the
       exception would already be raised in when guards above *)
    | Some _ -> invalid_arg "int_to_lbool"


let fast_solve_upto_id ({ solver = solver } as s) assumptions max_id = 

  (* Increment counter *)
  s.num_of_fast_solver_calls <- succ s.num_of_fast_solver_calls;

  (* Solve with literal assumptions *)
  match minisat_fast_solve solver assumptions 1 (Some max_id) with 

    (* Satisfiable with assumptions *)
    | Some l when int_to_lbool (l) = L_true -> Some true

    (* Unsatisfiable with assumptions *)
    | Some l when int_to_lbool (l) = L_false -> Some false 

    (* Unsatisfiable without assumptions *)
    | Some l when int_to_lbool (l) = L_undef -> raise Unsatisfiable_prop_na

    (* Unknown *)
    | None -> None

    (* Catch integers that are not mapped to a lifter Boolean, but the
       exception would already be raised in when guards above *)
    | Some _ -> invalid_arg "int_to_lbool"


(* Return the final conflicts clause after an unsatisfiable solve *)
let get_model { solver = solver } =
  minisat_get_model solver


(* Return the model after a satisfiable solve *)
let get_model { solver = solver } =
  minisat_get_model solver


(* Return the final conflicts clause after an unsatisfiable solve *)
let get_conflicts { solver = solver } =
  minisat_get_conflicts solver


(* Return the final conflicts clause after an unsatisfiable solve *)
let minimise_core { solver = solver } core =
  minisat_minimise_core solver core


(* No support for unsatisfiable cores in MiniSat *)
let unsat_core _ = 
  invalid_arg "Unsatisfiable cores not supported"
 

(* Return the number of calls to {!solve} of the solver instance *)
let num_of_solver_calls { num_of_solver_calls = n } = n


(* Return the number of calls to {!fast_solve} of the solver instance *)
let num_of_fast_solver_calls { num_of_fast_solver_calls = n } = n


(* Return the number of propositional variables in the solver instance *)
let num_of_vars { solver = solver } = minisat_stat_vars solver


(* Return the number of propositional variables in the solver instance *)
let num_of_clauses { solver = solver } = minisat_stat_clauses solver


(* Return true if the solver was created as a simplification solver *)
let is_simplification { is_simplification = b } = b


let reset_solver solver = 
  minisat_reset_solver solver.solver

let delete_solver solver =
  minisat_delete_solver solver.solver

(* TODO: implement set_important_lit *)
let set_important_lit solver lit = ()

let set_decision_var { solver = solver } is_decision lit =
 minisat_set_decision_var solver is_decision lit


(*   minisat_next_impl_unit can raise Not_found *)
let get_next_implied_unit solver = 
(*   print_endline ("dbg minisat.ml: get_next_implied_unit: start"); *)
  let lit_minisat = minisat_next_impl_unit solver.solver in
(*  print_endline ("dbg minisat.ml: get_next_implied_unit" ^(literal_to_string solver lit_minisat)); *)
  lit_minisat



let get_next_ass_implied_unit solver = 
(*   print_endline ("dbg minisat.ml: get_next_implied_unit: start"); *)
  let lit_minisat = minisat_next_ass_impl_unit solver.solver in
(*  print_endline ("dbg minisat.ml: get_next_implied_unit" ^(literal_to_string solver lit_minisat)); *)
  lit_minisat


let get_lit_id lit = minisat_get_lit_id lit
