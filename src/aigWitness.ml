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


open Lib
open Logic_interface
open AigCommon

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_latch
  | D_latch_var
  | D_input
  | D_input_var

let dbg_gr_to_str = function
  | D_latch -> "latch"
  | D_latch_var -> "latch_var"
  | D_input -> "input"
  | D_input_var -> "input_var"

let dbg_groups =
  [
    (* D_latch; *)
    D_input;
 ]

let module_name = "aig_witness"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(*----------- initial state: data --------------*)

(* array corresponding to the initial state *)
let initial_state_value = ref (Bytes.make 1 'x')

(* set of latches corresponding to values to be filled *)
let latches_to_fill = ref SMap.empty

(*----------- initial state: setup code --------------*)

(* set a value of a given latch *)
let set_state_size n =
  initial_state_value := Bytes.make n '.'

let set_latch_value i value =
  let value_ = (string_of_int value).[0] in
  dbg D_latch (lazy ("Set latch "^(string_of_int i)^
    " (of "^(string_of_int (Bytes.length !initial_state_value))^
    ") to "^(string_of_char value_)));
  Bytes.set !initial_state_value i value_

let set_latch_index i symb =
  Bytes.set !initial_state_value i 'x';
  dbg D_latch_var (lazy ("Latch var "^(string_of_int i)^
    " corresponds to var "^(Symbol.to_string symb)));
  latches_to_fill := SMap.add symb i !latches_to_fill

(*----------- initial state: usage code --------------*)

(* set the position corresponding to SYMB of the initial state to VALUE *)
let add_latch_value symb value =
  try (* find the symbol's place in the line *)
    let i = SMap.find symb !latches_to_fill in
    (* set the value *)
    Bytes.set !initial_state_value i value
  with (* not a variable -- nothing to do *)
  | Not_found -> ()

(* print the state array as a string *)
let print_initial_state () =
  out_str (aig_pref^(Bytes.to_string !initial_state_value))

(*----------- input vector: data --------------*)

(* sample array with fixed values for constants *)
let sample_input_values = ref (Bytes.make 1 'x')

(* current array with values for input variables *)
let current_input = ref (Array.make 1 (Bytes.make 1 'x'))

(* set of input variables corresponding values to be filled *)
let input_vars_to_fill = ref SMap.empty

(*----------- input vector: setup code --------------*)

(* set a value of a given input *)
let set_input_size n =
  sample_input_values := Bytes.make n '.'

let set_input_value i value =
  Bytes.set !sample_input_values i (string_of_int value).[0]

let set_input_index i symb =
  Bytes.set !sample_input_values i 'x';
  dbg D_input_var (lazy ("Input "^(string_of_int i)^
    " corresponds to var "^(Symbol.to_string symb)));
  input_vars_to_fill := SMap.add symb i !input_vars_to_fill

(*----------- input vector: usage code --------------*)

(* setup bounds for the input *)
let set_input_max_bound bound =
  let pattern = !sample_input_values in
  current_input := Array.make (succ bound) pattern;
  (* unhare vectors *)
  for i = 0 to bound do
    Array.set !current_input i (Bytes.copy pattern)
  done

(* set the position corresponding to SYMB of the INDEX input to VALUE *)
let add_input_value index symb value =
  try (* find the symbol's place in the line *)
    let i = SMap.find symb !input_vars_to_fill in
    (* find the input vector *)
    let input = Array.get !current_input index in
    dbg D_input (lazy ("Set input "^(string_of_int i)^
      " (of "^(string_of_int (Bytes.length input))^
      ") at bound "^(string_of_int index)^" to "^(string_of_char value)));
    (* set the value *)
    Bytes.set input i value
  with (* not a variable -- nothing to do *)
  | Not_found -> ()

(* print the input vector as a string *)
let print_input_vectors () =
  for i = 0 to pred (Array.length !current_input) do
    out_str (aig_pref^(Bytes.to_string (Array.get !current_input i)))
  done
