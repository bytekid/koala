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


open AigCommon
open Lib
open Bmc1Common (* for helpers for creating theory *)
open Logic_interface
open Statistics

(**)
(* print AIG problem *)
(**)

let print_var symbol = out_str (string_of_int symbol.lit)

let print_latch symbol =
  let l = (string_of_int symbol.lit) in
  let n = (string_of_int symbol.next) in
  let str =
    if 0 = symbol.reset
    then l^" "^n
    else l^" "^n^(string_of_int symbol.reset)
  in
  if symbol.used
  then out_str str

let print_and conj =
  (* all simplified ands should not be kept *)
  assert (not (conj.in_use && conj.simplified));
  if conj.in_use
  then
    out_str ((string_of_int conj.lhs)^" "^(string_of_int conj.rhs0)^" "^(string_of_int conj.rhs1))

let print_aig problem =
  (* print header *)
  let m = (string_of_int problem.max_var) in
  let i = (string_of_int (List.length problem.inputs)) in
  let l = (string_of_int (List.length problem.latches)) in
  let o = (string_of_int (List.length problem.outputs)) in
  let a = (string_of_int (List.length problem.ands)) in
  let b = (string_of_int (List.length problem.bad)) in
  let c = (string_of_int (List.length problem.constraints)) in
  (* let j = (string_of_int (List.length problem.justice)) in  *)
  (* let f = (string_of_int (List.length problem.fairness)) in *)
  out_str ("aag "^m^" "^i^" "^l^" "^o^" "^a^" "^b^" "^c);

  (* print inputs *)
  List.iter print_var problem.inputs;
  (* print latches *)
  List.iter print_latch problem.latches;
  (* print outputs *)
  List.iter print_var problem.outputs;
  (* print bads *)
  List.iter print_var problem.bad;
  (* print constraints *)
  List.iter print_var problem.constraints;
  (* print ANDs *)
  List.iter print_and problem.ands
