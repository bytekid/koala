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

open Minisat

(* Print an array of any type with separator from an index on *)
let rec pp_any_array' pp_a sep ppf array = function
  | i when i > Array.length array -> ()
  | i when i < 0 -> ()
  | i when i = Array.length array - 1 -> 
      Format.fprintf ppf "%a" pp_a array.(i)
  | i -> 
    Format.fprintf ppf "%a%s" pp_a array.(i) sep; 
    pp_any_array' pp_a sep ppf array (succ i)

(* Print an array of any type with separator *)
let pp_any_array pp_a sep ppf array = 
  pp_any_array' pp_a sep ppf array 0

(* Print a list of any type with separator *)
let rec pp_any_list pp_a sep ppf = function
  | [] -> 
      ()
  | [a] -> 
      Format.fprintf ppf "%a" pp_a a
  | a::tl -> 
      Format.fprintf ppf "%a%s" pp_a a sep; pp_any_list pp_a sep ppf tl

(* Print a list of strings with separator *)
let pp_string_list = pp_any_list Format.pp_print_string

(* Print a list of strings with separator *)
let pp_string_array sep array = pp_any_array Format.pp_print_string sep array

(* Print a list of strings with separator *)
let pp_int_list = pp_any_list Format.pp_print_int

(* Print an array of strings with separator *)
let pp_int_array sep array = pp_any_array Format.pp_print_int sep array

(* Print a bool option value as l_True, l_False or l_Undef *)
let pp_bool_option ppf = function
  | Some true -> Format.fprintf ppf "l_True"
  | Some false -> Format.fprintf ppf "l_False"
  | None -> Format.fprintf ppf "l_Undef"

(* Print a list of bool option values *)
let pp_bool_option_list = pp_any_list pp_bool_option

(* Print an array of bool option values *)
let pp_bool_option_array sep array = pp_any_array pp_bool_option sep array

(* Print a list of floats with separator *)
let pp_float_list = pp_any_list Format.pp_print_float

(* Print an array of floats with separator *)
let pp_float_array sep array = pp_any_array Format.pp_print_float sep array

let main () =

  let solver = create_solver false in

  let p = create_lit solver true 0 in
  let p' = create_lit solver false 0 in

  let q = create_lit solver true 1 in
  let q' = create_lit solver false 1 in

  let r = create_lit solver true 2 in
  let r' = create_lit solver false 2 in

  let p2 = create_lit solver true 0 in

(*
  let c0_lits = [p] in
  let c0 = add_clause_with_id solver c0_lits in

  Format.printf 
    "Added clause {%a} as %d@." 
    (pp_any_list (pp_literal solver) " ") 
    c0_lits
    (match c0 with Some i -> i | None -> -1);
*)
  let c1_lits = [p; q] in
  let c1 = add_clause_with_id solver c1_lits in

  Format.printf 
    "Added clause {%a} as %d@." 
    (pp_any_list (pp_literal solver) " ") 
    c1_lits
    (match c1 with Some i -> i | None -> -1);

  let c11_lits = [p'] in
  let c11 = add_clause_with_id solver c11_lits in

  Format.printf 
    "Added clause {%a} as %d@." 
    (pp_any_list (pp_literal solver) " ") 
    c11_lits
    (match c11 with Some i -> i | None -> -1);

(*
  let c12_lits = [q'] in
  let c12 = add_clause_with_id solver c12_lits in

  Format.printf 
    "Added clause {%a} as %d@." 
    (pp_any_list (pp_literal solver) " ") 
    c12_lits
    (match c12 with Some i -> i | None -> -1);
*)

(*
  let c2_lits = [p; q; r] in
  let c2 = add_clause_with_id solver c2_lits in

  Format.printf 
    "Added clause {%a} as %d@." 
    (pp_any_list (pp_literal solver) " ") 
    c2_lits
    (match c2 with Some i -> i | None -> -1);
*)

(*  match solve_assumptions solver [p'; q'; r'] with *)
  match solve_assumptions solver [q'] with  
(*  match solve solver with *)

    | false -> 
      
      Format.printf "Unsatisfiable@.";

      let uc = get_conflicts solver in

      Format.printf "Conflict clause is {%a}@." (pp_int_list " ") uc

    | true -> 

      Format.printf "Satisfiable@.";
      
      let m = get_model solver in 

      Format.printf "Model is {%a}@." (pp_bool_option_array " ") m;
	
;;

main ()

;;
