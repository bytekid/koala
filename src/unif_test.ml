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

let v0= Var.get_first_var ()
let v1= Var.get_next_var v0
let v2= Var.get_next_var v1
let v3= Var.get_next_var v2


let tc1 = Term.create_fun_term c1 []
let tc2 = Term.create_fun_term c2 []
let tv0 = Term.create_var_term v0
let tv1 = Term.create_var_term v1
let tv2 = Term.create_var_term v2
let tv3 = Term.create_var_term v3

let t1  = Term.create_fun_term f3 [tv2;tv2]
let t2  = Term.create_fun_term f2 [t1;tv1;tv3;t1]
let t3  = Term.create_fun_term f3 [tv2;tv1;tv2;tv2]


let t = t2
let s = t3


let termdb0 = TermDB.create ()
let termdb1 = TermDB.add tc1 termdb0
let termdb2 = TermDB.add tv0 termdb1
let termdb3 = TermDB.add tv1 termdb2
let termdb4 = TermDB.add tv2 termdb3
let termdb5 = TermDB.add tv3 termdb4

let termdb6 = TermDB.add t1 termdb5
let termdb7 = TermDB.add t2 termdb6
let termdb8 = TermDB.add t3 termdb7
let termdb  = termdb8

let clause1 = Clause.create [t1;t2;t1] 
let bclause1 = (1,clause1)
let bclause2 = (2,clause1)

let empty_bsubst = SubstBound.create ()

let bsubst1 = SubstBound.add (1,v1) (1,t1) empty_bsubst 
let bsubst2 = SubstBound.add (1,v2) (1,tv3) bsubst1 
let bsubst = bsubst2

let termdb_ref = ref termdb

let norm_clause = Clause.normalise clause1 termdb_ref
let norm_bclause = Clause.normalise_bclause_list [bclause1;bclause2] bsubst termdb_ref

let () = fprintf stdout " %s \n" (Clause.to_string clause1)
let () = fprintf stdout " %s \n" (Clause.to_string norm_clause)
let () = fprintf stdout " %s \n" (Clause.to_string norm_bclause)


let unif_test = 
  try 
    let env = Unif.unify_bterms (1,(TermDB.find t termdb)) (2,(TermDB.find s termdb)) in
    ()=fprintf stdout " %s \n" (SubstBound.to_string env)
  with 
    Unif.Unif_non_unifable -> ()=fprintf stdout "Non-unifiable \n"
