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


(* to generate mli use "ocamlc -I obj/ -i src/aigCommon.ml > src/aigCommon.mli" *)

(* AND structure *)
type aig_and =
  {
    lhs : int;
    mutable rhs0: int;
    mutable rhs1: int;
    mutable in_use: bool;
    mutable simplified: bool;
  }

let and_as_string conj =
  "aig_and("^(string_of_int conj.lhs)^","^(string_of_int conj.rhs0)^","^(string_of_int conj.rhs1)^")"

(* symbol structure *)
type aig_symbol =
  {
    mutable lit      : int;
    mutable next     : int;
    reset    : int;
    size     : int;
    lits     : int list;
    name     : string;
    mutable used: bool;
    mutable removed: bool
  }

let latch_as_string latch =
  "latch("^(string_of_int latch.lit)^"->"^(string_of_int latch.next)^":"^(string_of_int latch.reset)^")"

(* list of symbol *)
type aig_symbol_list = aig_symbol list

(* aig representation itself *)
type aiger =
  {
    max_var : int;

    inputs : aig_symbol_list;
    latches : aig_symbol_list;
    outputs : aig_symbol_list;
    bad : aig_symbol_list;
    constraints : aig_symbol_list;
    justice : aig_symbol_list;
    fairness : aig_symbol_list;

    ands: aig_and list;

    comments: string list;
  }

let aiger_stat aiger =
  let pref = "\nAIG input: " in
  pref^(string_of_int aiger.max_var)^" vars"^
  pref^(string_of_int (List.length aiger.inputs))^" inputs\n"^
  pref^(string_of_int (List.length aiger.outputs))^" outputs"^
  pref^(string_of_int (List.length aiger.bad))^" bads\n"^
  pref^(string_of_int (List.length aiger.ands))^" ands"^
  pref^(string_of_int (List.length aiger.latches))^" latches\n"^
  pref^(string_of_int (List.length aiger.constraints))^" constraints"^
  pref^(string_of_int (List.length aiger.justice))^" justice"^
  pref^(string_of_int (List.length aiger.fairness))^" fairness\n"

let aig_pref = "AIG_OUT "

(**)
(* helpers to work with AIG literals *)
(**)

(* move from literals to vars *)
let lit2var n = (n/2)
(* create negation of a literal *)
let neg n =
  if n mod 2 = 0
  then (succ n)
  else (pred n)
