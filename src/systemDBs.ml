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



(* ----------------Parser Out------------------------------- *)
open Lib

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

let dbg_groups =
  [
   D_trace;
 ]
    
let module_name = "systemDBs"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


module SSet = Symbol.Set
module TSet = Term.Set
module SMap = Symbol.Map

type symbol = Symbol.symbol

let symbol_db_ref = ref (SymbolDB.create_name "Symbols_DB")
let term_db_ref   = ref (TermDB.create_name "Terms_DB")

(*----- special terms ------- *)
let add_term symb args =  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let bot_term = add_term Symbol.symb_bot []
let top_term = add_term Symbol.symb_top []

let true_term = add_term Symbol.symb_true []

let false_term = add_term Symbol.symb_false []


let true_fun_term = add_term Symbol.symb_true_fun [] 

let false_fun_term = add_term Symbol.symb_false_fun []

(*---- special domains ---*)

let bool_fun_dom = TSet.add true_fun_term (TSet.add false_fun_term TSet.empty)

(* map from types to domains *)

type type_to_domain = TSet.t SMap.t

let type_to_domain = SMap.add Symbol.symb_bool_fun_type bool_fun_dom SMap.empty

let type_to_domain_to_string_list () = 
  let f type_symb dom_set str_list = 
    let type_str     = Symbol.to_string type_symb in 
    let dom_str      = Term.term_list_to_string (TSet.elements dom_set) in 
    let type_dom_str = type_str^": "^dom_str in 
    type_dom_str::str_list
  in
  SMap.fold f type_to_domain [] 

let type_to_domain_to_string () = 
  let type_dom_str_list = type_to_domain_to_string_list () in
  String.concat "\n" type_dom_str_list

let _ =
  dbg_env D_trace 
    (fun () ->
      dbg D_trace (lazy ("\n"));
      out_str ("true_term: "^(Term.to_string true_term));
      out_str ("true_fun_term: "^(Term.to_string true_fun_term));
      out_str "------- Type domain "; 
      out_str (type_to_domain_to_string ())
    )
(* should not be used since special symbols can change
let special_symbols_set = SSet.of_list Symbol.special_symbols_list
let is_special_symbol s = SSet.mem s special_symbols_set
*)
