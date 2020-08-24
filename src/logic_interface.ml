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


(* to generate interface *)
(* ocamlc -I obj/ -i src/logic_interface.ml > src/logic_interface.mli *)
open Lib
open Options

module SSet = Symbol.Set
module SMap = Symbol.Map
module SHtbl = Symbol.Hashtbl

module VSet = Var.VSet
module VMap = Var.VMap
module VHtbl = Var.VHashtbl

module BVSet = Var.BSet
module BVMap = Var.BMap
module BVHtbl = Var.BHashtbl

module TSet = Term.Set
module TMap = Term.Map
module THtbl = Term.Hashtbl

module CSet = Clause.CSet
module CMap = Clause.CMap
module CHtbl = Clause.CHashtbl

(* basic clause as key *)
module BCSet = Clause.BCSet  
module BCMap = Clause.BCMap 
module BCHtbl = Clause.BCHashtbl


type var    = Var.var
type symbol = Symbol.symbol
type stype = Symbol.stype
type term = Term.term
type args = Term.args
type lit = term
type lits = lit list
type literal = lit
type clause = Clause.clause
type tstp_source = Clause.tstp_source
type context = Clause.context
(* type proof_search_param = Clause.proof_search_param *)
type symbol_db_ref = SymbolDB.symbolDB ref

type term_db_ref = TermDB.termDB ref

let symbol_db_ref = SystemDBs.symbol_db_ref
let term_db_ref = SystemDBs.term_db_ref

exception Empty_clause = Clause.Empty_clause 


(* let context = Parser_types.context *)
(* first when term_db_ref is a parameter *)

(*----------------- symbols ---------------------------------*)

(*let creat_const_symb symb_name ~symb_type =*)

let create_stype = Symbol.create_stype

let create_symbol ?(is_special=false) symbol_name symbol_stype =
  let symb =  
    SymbolDB.add_ref
      (Symbol.create_from_str_type symbol_name symbol_stype)
      symbol_db_ref
  in
  Symbol.set_is_special_symb is_special symb;
  symb

let find_symbol symb_name = 
  SymbolDB.find
    (Symbol.create_template_key_symb symb_name) !symbol_db_ref 


(*
let special_symbols_set = SystemDBs.special_symbols_set
let is_special_symbol = SystemDBs.is_special_symbol
*)
let is_special_symb = Symbol.is_special_symb

(*---------------terms/lits----------------------------------*)
let add_fun_term symb args = 
  TermDB.add_ref (Term.create_fun_term symb args) term_db_ref

let add_fun_term_args symb args = 
  TermDB.add_ref (Term.create_fun_term_args symb args) term_db_ref

let add_var_term var = 
  TermDB.add_ref (Term.create_var_term var) term_db_ref

let add_term_db term = 
  TermDB.add_ref term term_db_ref

let add_pred_0 ?(is_special=false) pred_name = 
  let pred_type = Symbol.create_stype [] Symbol.symb_bool_type in
  let pred_symb = create_symbol ~is_special pred_name pred_type in 
  add_fun_term pred_symb []


let add_typed_equality_term stype_term t s =
  let args = [stype_term; t; s] in
  add_fun_term Symbol.symb_typed_equality args

let add_typed_equality_sym eq_type_sym t s =
  let eq_type_term = (add_fun_term eq_type_sym []) in
  add_typed_equality_term eq_type_term t s


let add_typed_disequality_term eq_type t s =
  add_fun_term Symbol.symb_neg [(add_typed_equality_term eq_type t s)]

let add_typed_disequality_sym eq_type_sym t s =
  add_fun_term Symbol.symb_neg [(add_typed_equality_sym eq_type_sym t s)]

let add_neg_atom atom =
  let args = [atom] in
  add_fun_term Symbol.symb_neg args

let add_neg_atom_symb symb args = 
  add_neg_atom	(add_fun_term symb args)

let add_lit_symb sign symb args = 
  if sign 
  then 
    add_fun_term symb args 
  else 
    add_neg_atom_symb symb args

let add_compl_lit lit = 
  TermDB.add_ref (Term.compl_lit lit) term_db_ref 

let term_true () = add_fun_term Symbol.symb_true []

let term_false () = add_fun_term Symbol.symb_false []



(*-----------term views----------*)	
type eq_view_type_term = 
    Eq_type_term of term * term * term

type eq_view_type_symb = 
  | Eq_type_symb of symbol * term * term 

	
let term_eq_view_type_term t = 
  match t with
  |Term.Fun (sym, args, _info) ->
      if (sym == Symbol.symb_typed_equality)
      then 
	let (type_term_eq, t, s) = get_triple_from_list (Term.arg_to_list args) in
	Def(Eq_type_term (type_term_eq, t, s))
      else
	Undef
  |_-> Undef
	
(* should be used with care since assume that eq type is not a variable here *)	
let term_eq_view_type_symb t = 
  match t with
  |Term.Fun (sym, args, _info) ->
      if (sym == Symbol.symb_typed_equality)
      then 
	let (type_term_eq, t, s) = get_triple_from_list (Term.arg_to_list args) in
	let eq_type_symb = 
	  try
	    Term.get_top_symb type_term_eq
	  with 
	    Term.Var_term ->
	      failwith
		("term_eq_view_type_symb: equality type is a variable in"^(Term.to_string t))
	in				
	Def(Eq_type_symb (eq_type_symb, t, s))
      else
	Undef
  |_-> Undef
	
	
(*
  let dis_equality t s =
  neg_atom (equality_term t s)
 *)

(*
  let add_typed_dis_equality stype t s =
  add_neg_atom (add_typed_equality_term stype t s)
 *)
(* used for model output *)
let add_term_algebra_eq_term args = 
  let ta_eq_type_term = (add_fun_term Symbol.symb_term_algebra_type []) in
  add_fun_term Symbol.symb_typed_equality  (ta_eq_type_term::args)

(*--------clause---------------*)	
(*-----------empty clause check ------------*)
let check_empty_clause clause =
  if (Clause.is_empty_clause clause)
  then
    raise (Empty_clause clause)
  else 
    ()

(*----------------*)
let create_clause ?(is_negated_conjecture=false)  ?(bc_imp_inh=bc_imp_inh_default_val) tstp_source lits = 
(* Normalisation is done in Clause.create_clause *)
(*  let norm_lits = Clause.normalise_lit_list term_db_ref lits in *) 
  let clause = Clause.create_clause term_db_ref ~is_negated_conjecture ~bc_imp_inh tstp_source (* norm_lits *) lits in 
  (if (Clause.is_empty_clause clause) 
  then 
    raise (Empty_clause (clause))
  );
  clause

let create_clause_context context ?(is_negated_conjecture=false) ?(bc_imp_inh=bc_imp_inh_default_val) tstp_source lits =
  let clause = create_clause ~is_negated_conjecture ~bc_imp_inh tstp_source lits in
  Clause.context_add context clause

let normalise_blitlist_list blitlist_list = 
  Clause.normalise_blitlist_list term_db_ref blitlist_list 		

let get_lits c = Clause.get_lits c

let clause_register_subsumed_by context ~by c = 
  (if  (not (by == c)) 
  then Clause.assign_is_dead context true c);
  if (Clause.equal_bc by c)
  then ()
  else
    ( 
(*      Clause.set_ps_simplifying true by; *)
(*      Clause.assign_replaced_by context (Def(Clause.RB_subsumption by)) c; *) (* TODO *)
      Clause.inherit_conjecture c by
     )

let pp_clause_with_source = Clause.pp_clause_with_source
    
let pp_clause_list_with_source = Clause.pp_clause_list_with_source
    

(*---------- context ----------------*)				
let context_create = Clause.context_create
let context_add  = Clause.context_add
let context_remove = Clause.context_remove  
let context_mem = Clause.context_mem 
(* let context_mem_lits = Clause.context_mem_lits *)
(* let context_reset = Clause.context_reset *)
let context_find = Clause.context_find
(* let context_find_lits = Clause.context_find_lits *)
let context_iter = Clause.context_iter 
let context_fold = Clause.context_fold 
let context_size = Clause.context_size

(* context_add_context from_cxt to_cxt *)
(* let context_add_context = Clause.context_add_context *)
    
(** replaces dead with simplified_by *)
(* let context_replace_by_clist = Clause.context_replace_by_clist *)


(*---- for aguments which are either context or list we can use --------*)

type context_list = Clause.context_list

let cl_iter = Clause.cl_iter
let cl_fold = Clause.cl_fold
let cl_size = Clause.cl_size

(*-------------------------*)
let is_ver_epr () = 
  (!current_options.aig_mode || (val_of_override  !current_options.bmc1_incremental)) 
 

(*------ debug output (outdated) ----------*)

let out_symbs () =   
  let out_symb symb =
    out_str ("Symb: "
	     ^(Symbol.to_string symb)
	     ^" is conj symb: "
	     ^ (string_of_bool (Symbol.get_bool_param Symbol.is_conj_symb symb ))^"\n"
	     ^"has bound constant: "
	     ^(string_of_bool (Symbol.get_bool_param Symbol.is_bound_constant symb ))^"\n" );
  in
  out_str ("\n\n ------------------------------\n\n");
  SymbolDB.iter out_symb !symbol_db_ref;
  out_str ("\n\n ------------------------------\n\n")

let out_terms () =
  let out_term t =
    if (not (Term.is_var t))
    then
      (    out_str ("Term: "
	     ^(Term.to_string t)
	     ^" has conj symb: "
	     ^ (string_of_bool (Term.get_fun_bool_param Term.has_conj_symb t ))^" "
	     ^"has bound constant: "
	     ^(string_of_bool (Term.get_fun_bool_param Term.has_bound_constant t ))^"\n" )
          )
    else
      (    out_str ("Var Term: "
	            ^(Term.to_string t)
                   )
          )
  in       
  out_str ("\n\n ------------------------------\n\n");
  TermDB.iter out_term !term_db_ref;
  out_str ("\n\n ------------------------------\n\n")


let out_basic_mem () = 
  print_objsize "term_db" term_db_ref;
  print_objsize "symbol_db_ref" symbol_db_ref;
  Clause.out_mem ()
