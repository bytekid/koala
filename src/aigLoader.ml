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

external init_aiger : string -> bool = "C_init_aiger"
external clear_aiger : unit -> unit = "C_clear_aiger"

external get_and_lhs : unit -> int = "C_get_and_lhs"
external get_and_rhs0 : unit -> int = "C_get_and_rhs0"
external get_and_rhs1 : unit -> int = "C_get_and_rhs1"

external get_symbol_lit : unit -> int = "C_get_symbol_lit"
external get_symbol_next : unit -> int = "C_get_symbol_next"
external get_symbol_reset : unit -> int = "C_get_symbol_reset"
external get_symbol_size : unit -> int = "C_get_symbol_size"
external get_symbol_just : int -> int = "C_get_symbol_just"
external get_symbol_name : unit -> string = "C_get_symbol_name"

external n_vars : unit -> int = "C_n_vars"
external num_ands : unit -> int = "C_num_ands"
external num_ins : unit -> int = "C_num_ins"
external num_outs : unit -> int = "C_num_outs"
external num_bads : unit -> int = "C_num_bads"
external num_latches : unit -> int = "C_num_latches"
external num_constraints : unit -> int = "C_num_constraints"
external num_fairness : unit -> int = "C_num_fairness"
external num_justice : unit -> int = "C_num_justice"


external set_cur_and : int -> unit = "C_set_cur_and"
external set_cur_in : int -> unit = "C_set_cur_in"
external set_cur_out : int -> unit = "C_set_cur_out"
external set_cur_bad : int -> unit = "C_set_cur_bad"
external set_cur_latch : int -> unit = "C_set_cur_latch"
external set_cur_constraint : int -> unit = "C_set_cur_constraint"
external set_cur_fairness : int -> unit = "C_set_cur_fairness"
external set_cur_justice : int -> unit = "C_set_cur_justice"

exception AigLoadError

(* load current AND from AIGER description *)
let get_and () =
  {
    lhs  = get_and_lhs ();
    rhs0 = get_and_rhs0 ();
    rhs1 = get_and_rhs1 ();
    in_use = true;
    simplified = false;
  }

let get_symbol_lits () =
  (* folder *)
  let rec get_lit n accum =
    if n = 0
    then accum
    else get_lit (pred n) ((get_symbol_just n)::accum)
  in
  (* get all vars from justice *)
  get_lit (get_symbol_size ()) []

(* load current SYMBOL from AIGER description *)
let get_symbol () =
  {
    lit   = get_symbol_lit ();
    next  = get_symbol_next ();
    reset = get_symbol_reset ();
    size  = get_symbol_size ();
    lits  = get_symbol_lits ();
    name  = "";(*get_symbol_name ();*)
    used  = true;
    removed = false;
  }


(* load all ANDS *)
let load_ands () =
  (* folder *)
  let rec load_and n accum =
    if n = 0
    then accum
    else
      begin
        set_cur_and (pred n);
        load_and (pred n) (get_and ()::accum)
      end
  in
  load_and (num_ands ()) []
  
(* load symbols from an array accessed by SET_CUR_SYMBOL of size N *)
let load_symbols set_cur_symbol num =
  (* folder *)
  let rec load_symbol n accum =
    if n = 0
    then accum
    else
      begin
        set_cur_symbol (pred n);
        load_symbol (pred n) (get_symbol ()::accum)
      end
  in
  load_symbol num []

(* load AIGER from file. TODO: add STDIN support *)
let load_aig filename =
  (* try to load AIG into file *)
  if init_aiger filename
  then raise AigLoadError;
  
  (* read the format *)
  let problem =
    {
      max_var = n_vars();

      inputs = load_symbols set_cur_in (num_ins ());
      latches = load_symbols set_cur_latch (num_latches ());
      outputs = load_symbols set_cur_out (num_outs ());
      bad = load_symbols set_cur_bad (num_bads ());
      constraints = load_symbols set_cur_constraint (num_constraints ());
      justice = load_symbols set_cur_justice (num_justice ());
      fairness = load_symbols set_cur_fairness (num_fairness ());

      ands = (load_ands ());

      comments = [];
    }
  in
  (* close the reader *)
  clear_aiger();
  (* print stat *)
  Lib.out_str (aiger_stat problem);
  (* return read problem *)
  problem
