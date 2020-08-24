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







open Printf 
open Lib
type term = Term.term

let c1=Symbol.create_from_str "c1" Symbol.Func 
let c2=Symbol.create_from_str "c2" Symbol.Func 

let f2=Symbol.create_from_str "f2" Symbol.Func 
let f3=Symbol.create_from_str "f3" Symbol.Func 

let symdb0 = SymbolDB.create ()
let symdb1= SymbolDB.add c1 symdb0
let symdb2= SymbolDB.add c2 symdb1
let symdb3= SymbolDB.add f2 symdb2
let symdb4= SymbolDB.add f3 symdb3


let symdb = symdb4

let v1= Var.get_first_var ()
let v2= Var.get_next_var v1


let tc1 = Term.create_fun_term c1 []
let tc2 = Term.create_fun_term c2 []
let tv1 = Term.create_var_term v1
let tv2 = Term.create_var_term v2
let t1  = Term.create_fun_term f2 [tc1;tv2]
let t2  = Term.create_fun_term f2 [t1;t1]


let termdb0 = TermDB.create ()
let termdb1 = TermDB.add tc1 termdb0
let termdb2 = TermDB.add tv1 termdb1
let termdb3 = TermDB.add tv2 termdb2
let termdb4 = TermDB.add t1 termdb3
let termdb5 = TermDB.add t2 termdb4
let termdb  = termdb5


module Param = 
  struct
    let num_of_symb = SymbolDB.size symdb
  end

module DT =DiscrTree.Make (Param)

let dt = ref (DT.create () : (term DT.index))
let x = DT.add_term_path (TermDB.find t1 termdb) dt;;
x := Elem (t1)
let y= DT.add_term_path (TermDB.find t2 termdb) dt;;
y := Elem (t2)


(* let dt1 = DT.add_term_path 
*)
(* old
let keylist = DiscrTree.get_key_list t2

let rec out_s_v list = 
  match list with 
  | DiscrTree.Sym(h)::tl -> 
      let ()=fprintf stdout " %s "(Symbol.to_string h)
      in out_s_v tl
  | DiscrTree.Var(h)::tl -> 
      let ()=fprintf stdout " %s "(Var.to_string h)
      in out_s_v tl
  | [] -> ()
 
let () = out_s_v keylist
*)
