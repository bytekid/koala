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
open Options
open Logic_interface

exception Unsatisfiable_fm_na 


let get_sym_types sym = Symbol.get_stype_args_val_def sym


(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_range_axs
  | D_assumptions
  | D_incr_range_unsat_core
  | D_const_range 
  | D_dis_eq
  | D_lemmas 
  | D_assign_fp_range
  | D_flattening
  | D_cyclic

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_range_axs -> "range_axs"
  | D_assumptions -> "assumptions"
  | D_incr_range_unsat_core -> "incr_range_unsat_core"
  | D_const_range -> "const_range"
  | D_dis_eq -> "dis_eq"
  | D_lemmas -> "lemmas"
  | D_assign_fp_range -> "assign_fp_range"
  | D_flattening -> "flattening"
  | D_cyclic -> "cyclic"

let dbg_groups =
  [
(*   D_trace; 
     D_range_axs;  
     D_assumptions;  
     D_incr_range_unsat_core;  
     D_const_range;    
     D_dis_eq; 
 *)
   D_lemmas;
(*
  D_assign_fp_range;

  D_flattening;
  D_cyclic
 *)

 ]
    
let module_name = "finite_models"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)



(* The flattening transformation is based on                          *)
(* Computing Finite Models by Reduction to Function-free clause logic *)
(* by Baumgartner, Fuchs, de Nivelle, Tinelli *)
(* which are extensions of ideas from Paradox *)
(* after flattening each clause is of the form *)
(* ~P_f(y,x)\/~P(x)\/Q(x)\/ x=z *)
(* 1. all P_f are neg., 2. no x \not = y *)

(*-----------Add terms, clauses--------------*)

(* change later !!!*)
(*
  let equality_term t s =
  let default_type_term = (add_fun_term Symbol.symb_default_type []) in
  let args = [default_type_term; t; s] in
  add_fun_term Symbol.symb_typed_equality args
 *)

let create_symbol symb_name stype sproperty =
  let symb =
    Symbol.create_from_str_type_property
      symb_name stype  sproperty in
  let added_symb = SymbolDB.add_ref symb symbol_db_ref in
  Symbol.assign_is_essential_input true added_symb;
  Symbol.assign_is_input true added_symb;
  Symbol.incr_num_input_occur added_symb;
  added_symb
    
(*
  let equality_term eq_type t s =
  let args = [eq_type; t; s] in
  add_fun_term Symbol.symb_typed_equality args

  let add_typed_equality_sym eq_type_sym t s =
  let eq_type = (add_fun_term eq_type_sym []) in
  equality_term eq_type t s

  let add_typed_dis_equality eq_type t s =
  add_fun_term Symbol.symb_neg [(equality_term eq_type t s)]

  let dis_equality_sym eq_type_sym t s =
  add_fun_term Symbol.symb_neg [(add_typed_equality_sym eq_type_sym t s)]

  let add_clause_lits lit_list =
  Clause.normalise term_db_ref (Clause.create lit_list)
 *)

(* aux fun *)
let get_val_type sym = Symbol.get_val_type_def sym

(*----------------*)

(*
  type cyclic_types =
  {
  cyclic_types : SSet.t;
  non_cyclic_types : SSet.t
  }
 *)

(*----------------*)

(*
  let init_sig = ref (Clause.create_clause_sig ())

  let flat_sym_set = ref SSet.empty

  let def_sym_set = ref SSet.empty
(*let eq_type_set  = ref SSet.empty*)

  let epr_type_set = ref SSet.empty

  let epr_const_set = ref SSet.empty

  let cyc_non_cyc_types = ref { cyclic_types = SSet.empty; non_cyclic_types = SSet.empty }
 *)


(* SW
  let _ = out_warning "finite_models commented: preprocess_after_flattening" *)
 
(* (* slow *)
let preprocess_after_flattening clauses = 
  Splitting.splitting Definitions.def_env_glb ~out_progress:true clauses
*)

let preprocess_after_flattening clauses = clauses



type input_sig = 
    {
     mutable basic_input_sig : Clause.clause_signature; 
     mutable epr_type_set  : SSet.t;
     mutable epr_const_set : SSet.t;
     mutable cyclic_types : SSet.t;
     mutable non_cyclic_types : SSet.t;
   }

type flat_sig = 
    {
     mutable flattened_clauses : clause list;
     mutable flat_to_orig : symbol SMap.t;
     mutable flat_sym_set : SSet.t;   
   }

type term_defs = 
    {
     mutable def_sym_set : SSet.t;
     mutable term_def_map : symbol TMap.t; (* term definitions *)   
   }


(* fp -- flattend predicate that represent functions *)

(* value domain of flattend functions as predicates *)

type fp_range = 
    {

     fp_range_axiom : Clause.clause;  

     (* prop. predicates that positively added to range axioms; they are used to switch the axioms on/off*)

     fp_range_switch_atom : term;
   }


type flat_pred_ranges = 
    {
     fp_pred : symbol;   (* the flat predicate of this value domain *)
     fp_pred_type : symbol; (* value type *)
     (* fp_range_max_bound : int param; *) (* if defined, we do not extend value domain beyond this bound.  *)
     (* can be used in triangular symmetry breaking for constants  *)
     mutable fp_current_range : int;  (* current range value, values start with 1; 0 no value is assigned *)
     
(*  mutable fp_range_elements : term IntMap.t;  (* int -> bound_term *)  *)
     mutable fp_range_map : fp_range IntMap.t;
   }


type type_domain = 
    {
     mutable dom_type : symbol;
     mutable is_eq_domain : bool; (* there is equality of this type; so the type is eq type *)
     mutable dom_current_bound : int; (* elements of the domain {1,..,dom_current_bound} *)
     mutable dom_elements_map : term IntMap.t;  (* current domain elements *)  

     mutable dom_flat_const_bounds : int SMap.t; (* trianglular rep. int is max range bound for the *)

     (* current list of disequality axioms; if type is not an equality type so we do not need diseq axioms and have [] *)
     mutable dom_dis_eq_axioms : clause list; 
   }

type domain =
    {
(* only types which are value types of flat preds are considered in the domain *)

     mutable type_domain_map : type_domain SMap.t; (* map from type_symbol ->  domain *)
     
(*     mutable eq_domain_types : SSet.t;*) (* the set of all equality types in the domain; moved to type_domain *)  

     (* all flat and defpred symbols with value type of domain_type *)
     mutable dom_flat_preds : SSet.t;

     mutable flat_pred_ranges_map : flat_pred_ranges SMap.t;   (* map from pred ->  flat_pred_range *) 
     
(* map for decomposing switch predicate for fp into fp and range *)
     mutable switch_pred_to_fp_range : (symbol * int) SMap.t;

     mutable all_switch_atoms : TSet.t;
   }
      

(* finite models state *)
type fm_state = 
    {
     mutable input_clauses : clause list; 
     mutable input_sig : input_sig;
     mutable flat_sig : flat_sig;
     mutable term_defs : term_defs;
     mutable domain : domain;
     mutable lemmas : clause list;
   }

let cyclic_types fms = fms.input_sig.cyclic_types

let non_cyclic_types fms = fms.input_sig.non_cyclic_types
(*-------------------------------------*)

(* can be extended later *)
let epr_type_set clause_sig =
  let not_epr_type_set = ref SSet.empty in
  let val_types = ref SSet.empty in
  not_epr_type_set := SSet.add Symbol.symb_bool_type !not_epr_type_set;
  let f symb =
    let (arg_types, val_type) = get_sym_types symb in
    val_types := SSet.add val_type !val_types;
    if not (arg_types = [])
    then
      not_epr_type_set := SSet.add val_type !not_epr_type_set
    else
      ()
  in
  SSet.iter f clause_sig.Clause.sig_fun_preds;
  let epr_type_set = SSet.diff !val_types !not_epr_type_set in
  Statistics.incr_int_stat (SSet.cardinal epr_type_set) Statistics.sat_num_of_epr_types;
  epr_type_set

(* should be called after epr_type_set_init () *)
let epr_const_set clause_sig epr_type_set =
  let f symb  epr_const_set = 
    let (arg_types, val_type) = get_sym_types symb in
    if
      (arg_types = [])
	&&
      (SSet.mem val_type epr_type_set)
    then
      (
       SSet.add symb epr_const_set
      )
    else 
      epr_const_set 
  in
  SSet.fold f SSet.empty clause_sig.Clause.sig_fun_preds

(*-----------------------*)

let not_to_flat_type_test input_sig stype =
  (!current_options.sat_epr_types
     &&
   (SSet.mem stype input_sig.epr_type_set)
  )
||
  (!current_options.sat_non_cyclic_types
     &&
   (SSet.mem stype input_sig.non_cyclic_types)
  )

(* we do not faltten terms that do not sat this test*)
let not_to_flat_symb_test input_sig symb =
  let vt = get_val_type symb in
  not_to_flat_type_test input_sig vt
    
let not_to_flat_atom_test input_sig atom =
  match atom with
  | Term.Var _ -> false
  | Term.Fun (symb, args, _) ->
      (
       if (symb == Symbol.symb_typed_equality)
       then
	 let (eq_type, _t1, _t2) =
	   get_triple_from_list (Term.arg_to_list args) in
	 let eq_type_sym = Term.get_top_symb eq_type in
	 (not_to_flat_type_test input_sig eq_type_sym)
       else
	 true
      )

let not_to_flat_lit_test input_sig lit =
  not_to_flat_atom_test input_sig (Term.get_atom lit)

(*
  let don_not_flat_term_test term =
 *)

(*------------------------------------*)


(*
(* map from flat to original *)
  let flat_to_orig = SHtbl.create 101
 *)

let add_flat_to_orig flat_sig flat orig =
  if (SMap.mem flat flat_sig.flat_to_orig)
  then ()
  else
    flat_sig.flat_to_orig <- SMap.add  flat orig flat_sig.flat_to_orig

(*--------------- Flattening Signature ----------------------------*)
(* for each fun. symbol f in signature which also occrs in the input *)
(* we add P_f of arity ar(f) + 1, the first argument of P_f corresponds *)
(* to the value of f *)
(* one should run flat_signature (once) before flattening *)

(* val pred is first arg *)
let get_val_flat_pred_type sym =
  (* assert ((Symbol.is_flat sym) &&
     ( ( (not (Symbol.is_arity_def sym)) || (Symbol.get_arity sym) >0)
     || (Symbol.is_defpred sym)));
   *)
  let arg_types, _bool_type = Symbol.get_stype_args_val_def sym in
  let (val_type, _rest) = split_list arg_types in
  val_type


let fill_flat_signature input_sig flat_sig =
  let f symb =
    (
     if
       (
	(Symbol.is_fun symb)
	  &&
	(not (not_to_flat_symb_test input_sig symb))
       )
     then
       (
	begin
	  let new_symb_name = ("$$iProver_Flat_"^(Symbol.get_name symb)) in
	  let flat_type =
	    match (Symbol.get_stype_args_val symb) with
	    | Def (old_args, old_val) ->
		(*            Symbol.create_stype (old_args@[old_val]) Symbol.symb_bool_type*)
		Symbol.create_stype (old_val:: old_args) Symbol.symb_bool_type
	    | Undef -> Symbol.create_stype [] Symbol.symb_bool_type
	  in
	  let add_flat_symb = create_symbol new_symb_name flat_type Symbol.Flat in

	  dbg D_flattening (lazy (" new fp: "^(Symbol.to_string add_flat_symb)^" fp val type: "
				  ^(Symbol.to_string (Symbol.get_val_type_def symb))));

	  flat_sig.flat_sym_set <- SSet.add add_flat_symb flat_sig.flat_sym_set;
	  add_flat_to_orig flat_sig add_flat_symb symb;
	  Symbol.assign_flattening symb add_flat_symb;
	end
       )
     else 
       (
	dbg D_flattening (lazy (" not to flat: "^(Symbol.to_string symb)
			        ^" val type "^(Symbol.to_string (Symbol.get_val_type_def symb))));
       )
    )
  in
  SSet.iter f input_sig.basic_input_sig.Clause.sig_fun_preds


(*-------Definitions for Ground Terms ------------------------------------*)
(* We introduce defintions for each ground non-variable term              *)
(* this helps to shorten the resulting clauses.                           *)
(* We do not introduce explicitly new constants but use the same term for *)
(* its definition, and introduce R_t as the relation corresponding        *)
(* to this constant                                                       *)
(* term_def_table maps ground terms to symbols which are used to define   *)
(* these terms ex.: for f(g(a))                                           *)
(* the table will contain                                                 *)
(* f(g(a)) -> R_{f(g(a))}; g(a) -> R_{ga}; a -> (Symbol.get_flattening a) *)

let add_term_to_def_test t =
  (Term.is_ground t) && !current_options.sat_gr_def

(*
  let term_def_table = TermHash.create 41
 *)

(* adds definition of a ground term to the table *)
(* fix typed equality! *)
let rec add_term_def_table term_defs  t =
  if (TMap.mem t term_defs.term_def_map)
  then ()
  else
    match t with
    | Term.Fun (symb, args, _) ->
	if (Term.is_constant t)
	then
	  term_defs.term_def_map <- TMap.add  t (Symbol.get_flattening symb) term_defs.term_def_map
	else
	  (Term.arg_iter (add_term_def_table term_defs) args;
	   (* replace to a shorter name: based on a counter *)
	   let def_symb_name = ("$$iProver_Def_"^(Term.to_string t)) in
	   let def_symb_type =
	     (Symbol.create_stype [(get_val_type symb)] Symbol.symb_bool_type) in
	   let add_def_symb =
	     create_symbol def_symb_name def_symb_type Symbol.DefPred in
	   term_defs.def_sym_set <-
	     SSet.add add_def_symb (term_defs.def_sym_set);
	   term_defs.term_def_map <- TMap.add  t add_def_symb term_defs.term_def_map
	  )
    | Term.Var _ -> failwith "add_term_def_table term should be ground"


(* OLD
(*---------Basic flattening------------------------*)
(* Flattening of a clause is done in two stages:                      *)
(* First, we build a hash table (var_env) mapping non-var term into vars. *)
(* Second, we use var_env  to build flat terms.            *)
(* In "term_flattening_env var_env max_var_ref term"       *)
(* max_var is max var used                                 *)
(* the input term itself also added to the the var_env     *)
(* if a function term t statisfies add_term_to_def_test    *)
(* we do not need to go                                    *)
(* to subterms  but add 1. a definition t->x into env and  *)
(* 2. a definition into term_def_table (def. of all subterms of t are also added) *)
(* and later add  \neg R_t(x) to the clause *)

   let b_orig = 0
   let b_fresh = 1 (* bound for making vars fresh *)

   let rec term_flattening_env fresh_vars_env var_env term =
   match term with
   | Term.Var (v, _) -> () (*add_var_term (SubstBound.find_renaming renaming_env (b_orig,v))*)
   | Term.Fun (symb, args, _) ->
   if (TermHash.mem var_env term)
   then ()
   else
   begin
   (if (Symbol.is_fun symb)
   && (add_term_to_def_test term)
   then
   ((* out_str ("Adding to add_term_def_table term: "
       ^(Term.to_string term)^"\n");*)
   add_term_def_table term)
   else
   (
   let relevant_args =
   if (symb == Symbol.symb_typed_equality)
   then
   let (eq_type, t1, t2) =
   get_triple_from_list (Term.arg_to_list args) in
   (* on the way we also fill set of equality types *)
   (* let eq_type_sym = Term.get_top_symb eq_type in
      eq_type_set:= SSet.add eq_type_sym !eq_type_set;*)
   Term.list_to_arg [t1; t2]
   else
   args
   in
   Term.arg_iter (term_flattening_env fresh_vars_env var_env) relevant_args)
   );
   if (Symbol.is_fun symb)
   && (not (not_to_flat_symb_test symb))
   then
   (
   (* max_var_ref:= Var.get_next_var !max_var_ref; *)
   (*let new_var = SubstBound.get_next_unused_var renaming_env (Symbol.get_val_type_def symb) in*)
   let fresh_var = Var.get_next_fresh_var fresh_vars_env (Symbol.get_val_type_def symb) in
   let fresh_var_term = add_var_term fresh_var in
   TermHash.add var_env term fresh_var_term
   )
   else ()
   end

   let flat_term_to_var fresh_vars_env var_env t =
   if (Term.is_var t)
   then t
   else
   (
   try
   term_flattening_env fresh_vars_env var_env t;
   TermHash.find var_env t
   with Not_found -> failwith "flat_term_to_var: Not_found"
   )

   let order_term_var tv1 tv2 =
   if (Var.compare (Term.get_var tv1) (Term.get_var tv2)) > 0
   then (tv1, tv2)
   else (tv2, tv1)


(* We obtain flat def. of terms in var_env and   *)
(* a normalised subst. corresponding to x \not = y *)
(* subst is kept confluent *)
(* later this substitution will be applied to all variables*)
   let flat_lit_env fresh_vars_env var_env neg_var_subst_ref lit =
   if (not_to_flat_lit_test lit)
   then
   ()
   else
   begin
   if (Term.is_neg_lit lit)
   then
   begin
   let atom = Term.get_atom lit in
   match atom with
   | Term.Fun (symb, args, _) ->
   if (symb == Symbol.symb_typed_equality)
   then
   (* flat neg eq: t\=s 1. t->x s->y added to var_env,   *)
   (* then x\not y is normalised and added to subst.     *)
   
   (*	    let (t1,t2) = get_pair_from_list (Term.arg_to_list args) in*)
   let (eq_type, t1, t2) = get_triple_from_list (Term.arg_to_list args) in
   begin
   (*	    let rec fl t1 t2 = *)
   if t1 == t2 then ()
   else
   let var_t1 = flat_term_to_var fresh_vars_env var_env t1 in
   let var_t2 = flat_term_to_var fresh_vars_env var_env t2 in
   let norm_t1 =
   Subst.find_normalised !neg_var_subst_ref var_t1 in
   let norm_t2 =
   Subst.find_normalised !neg_var_subst_ref var_t2 in
   if norm_t1 == norm_t2
   then ()
   else
   begin
   let (big_t, small_t) = order_term_var norm_t1 norm_t2 in
   neg_var_subst_ref:=
   Subst.add (Term.get_var big_t) small_t !neg_var_subst_ref
   end
   end
   (* atom is not equality *)
   else
   term_flattening_env fresh_vars_env var_env atom
   
   | Term.Var _ -> failwith "flat_lit_env: atom cannot be a var"
   end
   (* positive lit*)
   else
   term_flattening_env fresh_vars_env var_env lit
   end

(*
  let rec get_max_var_term current_max_var_ref term =
  match term with
  | Term.Fun (_, args, _) ->
  Term.arg_iter (get_max_var_term current_max_var_ref) args
  | Term.Var (v, _) ->
  if (Var.compare v !current_max_var_ref) > 0
  then
  (current_max_var_ref := v)
  else ()
 *)

(*
  let get_max_var clause =
  let var_ref = ref (Var.get_first_var ()) in
  Clause.iter (get_max_var_term var_ref) clause;
  !var_ref
 *)

 *)


(*-----------------New flattening with cyclic types but without def yet---------------------------------------*)
(* P(t,..); *)
(* get_flat_term t:*)
(* either a var if top(t) is of a to_flatten type  *)
(* or f(get_flattened term) *)
(* vars are normalised wrt neg_var_subst_ref *)
(* during get_flattend save*)
(* 1) ~P_f(var, (flattened_args args)) for to_flatten type in an flat_env*)
(* 2)  mapping from term into flat_term  so it can be used when the same term is processed later *)
(* t=s then (get_flat_term t)=(get_flat_term s) ) *)
(* t != s then if (get_flat_term t) == (get_flat_term s) remove else (get_flat_term t) != (get_flat_term s) *)

(* if one of them is var then return (v,t) if both are vars compare them in by Var.compare otherwise restun as it is *)
let order_terms t1 t2 =
  if (Term.is_var t2)
  then
    if (Term.is_var t1)
    then
      if (Var.compare (Term.get_var t1) (Term.get_var t2)) > 0
      then (t1, t2) (* both vars*)
      else (t2, t1) (* both vars *)
    else (* t2 var; t1 non var*)
      (t2, t1)
  else (*t2 is non-var, t1 var/non-var *)
    (t1, t2)


(* without (ground) term definitions yet !*)
let flat_clause input_sig clause =
  (*	let var_env = TermHash.create 19 in *)
  let term_to_flat_term_env = ref TMap.empty in
  let clause_lits = Clause.get_literals clause in
  
  dbg D_flattening (lazy  (" clause: "^(Clause.to_string clause)^"\n"));

  let clause_vars = Clause.get_var_list clause in
  let fresh_vars_env = Var.init_fresh_vars_env_away clause_vars in
  
  let neg_var_subst_ref = ref (Subst.create ()) in
  (* lits of the form ~P_f(flat_args) *)
  let fun_def_lits = ref [] in
  
  (*Clause.iter (flat_lit_env fresh_vars_env var_env neg_var_subst_ref) clause;*)
  
  let neg_norm_term t = add_term_db (Subst.normalise_term !neg_var_subst_ref t) in

  (* add_to_neg_env checks if one of t1 or t2 is a vriable which does not occur in the other *)  
  (* then adds this pair to the env and return true otherwise return false*)
  let add_to_neg_env t1 t2 =
    (* assume that neither t1 nor t2 are in neg_var_subst_ref due to normalising *)
    let norm_t1 = neg_norm_term t1 in
    let norm_t2 = neg_norm_term t2 in
    if (norm_t1 == norm_t2)
    then
      true (* ignore if they norm terms are equal *)
    else
      let (ot1, ot2) = order_terms norm_t1 norm_t2 in
      if (Term.is_var ot1) && (not (Term.is_subterm ot1 ot2))
      then
	(
	 try 
	   neg_var_subst_ref := Subst.add (Term.get_var ot1) ot2 !neg_var_subst_ref;
	   true
	 with 
	   Subst.Subst_var_already_def ->
	     failwith ("flat_clause: ot1 var:"^(Var.to_string (Term.get_var ot1))^" has already def: "
		       ^(Term.to_string (Subst.find (Term.get_var ot1) !neg_var_subst_ref))
		       ^" ot2: "^(Term.to_string ot2)
		       ^" t1: "^(Term.to_string t1)
		       ^" norm_t1: "^(Term.to_string norm_t1)
		       ^" t2: "^(Term.to_string t2)
		       ^" norm_t2: "^(Term.to_string norm_t2)
		      )
	       
	)
      else
	false
  in
  (* a fun/var term not lit *)
  let rec get_flat_term term =
    try
      TMap.find term !term_to_flat_term_env
    with
    | Not_found ->
	begin
	  match term with
	  | Term.Fun (symb, args, _) ->
	      let arg_list = Term.arg_to_list args in
	      let new_args = List.map get_flat_term arg_list in
	      if (not_to_flat_symb_test input_sig symb)
	      then
		(
		 let flat_term =	add_fun_term symb new_args in
		 (* add t-> flat_term *)
		 term_to_flat_term_env := TMap.add term flat_term !term_to_flat_term_env;
		 flat_term
		)
	      else
		(
		 (* create ~P_f(new_args) *)
		 let pred_f_symb = Symbol.get_flattening symb in
		 (*	    out_str ("new symb: "^(Symbol.to_string new_symb)^"\n");*)
		 (* the value of the function is the first argument of the relation*)
		 let fresh_var = Var.get_next_fresh_var fresh_vars_env (Symbol.get_val_type_def symb) in
		 let fresh_var_term = add_var_term fresh_var in
		 let pred_f_args = fresh_var_term:: new_args in
		 let fun_def_lit = add_neg_atom_symb pred_f_symb pred_f_args in
		 (* add ~P_f(flat_args) to list *)
		 fun_def_lits:= fun_def_lit::!fun_def_lits;
		 (* add t -> flat_term == fresh_var *)
		 term_to_flat_term_env := TMap.add term fresh_var_term !term_to_flat_term_env;
		 fresh_var_term
		)
		  
	  | Term.Var (v, _) -> term
		(* Subst.find_normalised !neg_var_subst_ref term; normalise later after flattening *)
	end
  in
  
  let get_flat_lit rest lit =
    let atom = Term.get_atom lit in
    match atom with
    | Term.Fun (symb, args, _) ->
	if (symb == Symbol.symb_typed_equality)
	then
	  let (eq_type, t1, t2) = get_triple_from_list (Term.arg_to_list args) in
	  let flat_t1 = (get_flat_term t1) in
	  let flat_t2 = (get_flat_term t2) in
	  if (Term.is_neg_lit lit)
	  then
	    if (add_to_neg_env flat_t1 flat_t2)
	    then
	      rest
	    else
	      (add_typed_disequality_term eq_type flat_t1 flat_t2):: rest
	  else (* pos eq *)
	    (add_typed_equality_term eq_type flat_t1 flat_t2):: rest
	else (* non eq pred *)
	  let flat_atom_args = List.map get_flat_term (Term.arg_to_list args) in
	  let new_lit =
	    if (Term.is_neg_lit lit)
	    then
	      add_neg_atom_symb symb flat_atom_args
	    else
	      add_fun_term symb flat_atom_args
	  in
	  new_lit:: rest
    | Term.Var _ -> failwith "flat_lit: atom cannot be var"
  in
  let flat_lits = List.fold_left get_flat_lit [] clause_lits in
  let new_lits = flat_lits@(!fun_def_lits) in
  let new_neg_norm_lits = List.map neg_norm_term new_lits in
  
  let tstp_source = Clause.tstp_source_flattening clause in
  let new_clause = create_clause tstp_source new_neg_norm_lits in
(*
  Format.printf "Flat clause: \n @[%a @]@."
  (TstpProof.pp_clause_with_source_gs ~clausify_proof: false ) new_clause;
 *)
  (*	
    out_str ("     Cl: \n"^(Clause.to_string clause)^"\n");
    out_str ("Flat Cl: \n"^(Clause.to_string new_clause)^"\n");
   *)
  new_clause

(*--------------OLD-------------------*)
(*
  let flat_clause clause =
  let var_env = TermHash.create 19 in
  let clause_vars = Clause.get_var_list clause in
  let fresh_vars_env = Var.init_fresh_vars_env_away clause_vars in
(*let max_var_ref = ref (get_max_var clause) in*)
  let neg_var_subst_ref = ref (Subst.create ()) in
  Clause.iter (flat_lit_env fresh_vars_env var_env neg_var_subst_ref) clause;
(* now we have the map of non-var terms  to corresponding vars in var_env *)
(* get var_term corresponding to the term in var_env *)

  let term_to_var_term term =
  try
  (Subst.find_normalised !neg_var_subst_ref
  (TermHash.find var_env term))
  with Not_found ->
  if (Term.is_var term)
  then Subst.find_normalised !neg_var_subst_ref term
  else
  failwith ("term_to_var_term: Not_found term: "
  ^(Term.to_string term))
  in
(* auxilary function to flatten arguments taking into account epr sorts *)
  let flat_args_fun symb old_arg_list =
  let arg_types, _val_type = get_sym_types symb in
  let (_, rev_new_args) =
  let f (arg_types_rest, new_args_rest) old_arg =
  match arg_types_rest with
  | arg_type:: tl ->
  let new_arg =
  if (to_flat_type_test arg_type)
  then
  (
(*
  out_str ("to flat type "^(Symbol.to_string arg_type)
  ^" term "^(Term.to_string old_arg)^"\n");
 *)
  term_to_var_term old_arg
  )
  else
  old_arg
  in
  (tl, new_arg:: new_args_rest)
  |[] -> failwith "flat_lit rest lit should not happen"

  in
  List.fold_left f (arg_types,[]) old_arg_list
  in
  let new_arg_list = List.rev rev_new_args in
  new_arg_list
  in

(* first we flatten top of predicates and pos. eq. *)
(* (neq eq translates to x\=y and was added to subst.), *)
(* then we add all flattenings of terms in var_env *)
  let flat_lit rest lit =
  if (not (to_flat_lit_test lit))
  then
  lit:: rest
  else
  begin
  let atom = Term.get_atom lit in
  match atom with
  | Term.Fun (symb, args, _) ->
  if (symb == Symbol.symb_typed_equality)
  then
  if (Term.is_neg_lit lit)
  then
(* all neg eq are falttend to x\not y which are added to neg_var_subst_ref *)
(* and will be added to the rest later *)
  rest
  else
(*positive eq, terms replaced by definitions *)
(* let (t1,t2) = get_pair_from_list (Term.arg_to_list args) in*)
(* replace *)
  let (eq_type, t1, t2) = get_triple_from_list (Term.arg_to_list args) in
  (add_typed_equality_term eq_type (term_to_var_term t1) (term_to_var_term t2)):: rest
  else
(* non equlaity literal *)
  let new_atom =
  let old_arg_list = Term.arg_to_list args in
  let new_arg_list = flat_args_fun symb old_arg_list in
  add_fun_term symb new_arg_list
  in
  let new_lit =
  if (Term.is_neg_lit lit)
  then
  add_fun_term Symbol.symb_neg [new_atom]
  else
  new_atom
  in
  new_lit:: rest
  | Term.Var _ -> failwith "flat_lit: atom cannot be var"
  end
  in
  let flat_part = Clause.fold flat_lit [] clause in
  let get_env_part term var_term rest =
  let new_var_term =
  (Subst.find_normalised !neg_var_subst_ref var_term) in
  match term with
  | Term.Fun (symb, args, _) ->
  let new_atom =
  if (add_term_to_def_test term)
  then
  (try
  let new_symb = (TermHash.find term_def_table term) in
  add_fun_term new_symb [new_var_term]
  with Not_found ->
  failwith "get_env_part: ground term shoud be in term_def_table "
  )
  else
  (let new_symb = Symbol.get_flattening symb in
(*	    out_str ("new symb: "^(Symbol.to_string new_symb)^"\n");*)
(* the value of the function is the first argument of the relation*)

  let old_arg_list = Term.arg_to_list args in
  let non_flat_new_arg_list = flat_args_fun symb old_arg_list in

  let new_args = new_var_term:: non_flat_new_arg_list
(*	      new_var_term::(Term.arg_to_list (Term.arg_map term_to_var_term args)) *)
  in
  add_fun_term new_symb new_args
  )
  in
  let new_lit = add_fun_term Symbol.symb_neg [new_atom] in
  new_lit:: rest
  | Term.Var _ -> failwith "get_env_part should not be var term"
  in
  let env_part = TermHash.fold get_env_part var_env [] in
  add_clause_lits (env_part@flat_part)
 *)

(*----------------------------------------------------------------*)
(* Gets definitions from the term_def_table                       *)
(* Ex: we need to get f(t1,..,tn) = c_f(t1,..,tn)                 *)
(* which can be defined as                                        *)
(* \neg P_t1(X1)\/..\/ \neg P_tn(Xn) \/ \neg P_f(t1,...,tn)(Z) \/ *)
(* \/ \neg P_f(Val,X1,..,Xn)\/ Z=Val                              *)
(* constants are not redefined *)

(*----------------definitions are wrong and do not work!---------------------*)
(*--------------------fix later --------------------*)


(*let _ = out_str ("\n\n!Fix Definitions in finite_models!\n\n")*)

(*this should work for non-gound definitions but for ground should add a be better translation *)
let get_definitions term_defs =
  let f t def_symb rest =
    match t with
    | Term.Fun (symb, args, _) ->
	if (Term.is_constant t)
	then
	  (* no def. for constants needed *)
	  rest
	else
	  (
	   (*  [\neg P_t1(X1);.. \neg P_tn(Xn)] *)
	   (* let current_var = ref (Var.get_first_var ()) in *)
	   let var_env = Var.init_fresh_vars_env () in
	   let arg_vars = ref [] in
	   let f arg_lits_rest arg_term =
	     try
	       let new_symb = TMap.find arg_term term_defs.term_def_map in
	       let new_var_term = add_var_term (Var.get_next_fresh_var var_env (Term.get_term_type arg_term)) in
	       arg_vars:= new_var_term::!arg_vars;
	       let new_lit = add_neg_atom_symb new_symb [new_var_term] in
	       new_lit:: arg_lits_rest
	     with
	       Not_found ->
		 failwith "get_definitions: term should be in term_def_table "
	   in
	   let arg_lits = Term.arg_fold_left f [] args in
	   arg_vars := List.rev !arg_vars;
	   
	   (* \neg P_f(t1,...,tn)(Z) *)
	   let val_type = Symbol.get_val_type_def symb in
	   let current_var = Var.get_next_fresh_var var_env val_type in
	   let p_f_t_lit_var = add_var_term current_var in
	   let p_f_t_lit = add_neg_atom_symb def_symb [p_f_t_lit_var] in
	   
	   (*\neg P_f(Val,X1,..,Xn) *)
	   let current_var = Var.get_next_fresh_var var_env val_type in
	   let val_var = add_var_term current_var in
	   let p_f_symb = Symbol.get_flattening symb in
	   let p_f_lit = add_neg_atom_symb p_f_symb (val_var:: (!arg_vars)) in
	   (*Z=Val*)
	   let z_val_lit = add_typed_equality_sym
	       val_type p_f_t_lit_var val_var in
	   let tstp_source = Clause.tstp_source_definition in
	   let new_clause =
	     create_clause tstp_source (z_val_lit:: p_f_lit:: p_f_t_lit:: arg_lits) in
	   new_clause:: rest
	  )
	    
    | Term.Var _ -> failwith "get_definitions: term should be ground"
  in
  TMap.fold f term_defs.term_def_map []

(* TODO: definitions should be fixed!!! *)

let flat_clause_list input_sig term_defs clause_list =
  let flat_clauses = List.map (flat_clause input_sig) clause_list in
  
  dbg D_flattening (lazy  (
		    "\n\n --------- Flat Clauses ------- \n\n"
		    ^(Clause.clause_list_to_string flat_clauses)
		   ));
  

(*  let definitions = get_definitions term_defs in *) (* TODO term_defs *)
  
  let definitions = [] in
  definitions@flat_clauses

(*---------------Axioms-------------------------*)

(* bound_pred is added to clauses which are active at the current domain bound i *)
let create_range_switch_atom domain fp i =
  let range_switch_symb_name = ("$$iProver_range_switch_"^(Symbol.to_string fp)^"_"^(string_of_int i)) in

  let add_range_switch_symb =
    create_symbol
      range_switch_symb_name
      (Symbol.create_stype [] Symbol.symb_bool_type)
      Symbol.DomainPred 
  in
  let range_switch_atom =  add_fun_term add_range_switch_symb [] in

  domain.switch_pred_to_fp_range <- 
    SMap.add add_range_switch_symb (fp,i) domain.switch_pred_to_fp_range; 

  domain.all_switch_atoms <- TSet.add range_switch_atom domain.all_switch_atoms;
  range_switch_atom

(*--------*)
let is_switch_pred pred = ((Symbol.get_property pred) = Symbol.DomainPred)

(*-------domains do not include epr/non-cyclic domains----------------*)
(*
  type domain =
  {
  dom_type : symbol;

  (* in increasing order *)
  mutable dom_elements : term list;
  
  (* all flat and defpred symbols with value type of domain_type *)
  mutable dom_flat_preds : symbol list;

  (*     mutable dom_def_preds : symbol list; *)
  }

  let create_domain dom_type =
  {
  dom_type = dom_type;
  dom_elements =[];
  dom_flat_preds = [];
  }

(*
  module DKey =
  struct
  type t = domain
  let equal d1 d2 = Symbol.equal d1.dom_type d2.dom_type
  let hash d = Symbol.hash d.dom_type
  end
 *)

(* TDomainH hash table mapping domain_type -> domain *)
  module TDomainH = Hashtbl.Make(Symbol)

  let domain_table = TDomainH.create 101
 *)


(* init is should be followed by extension of ranges of all falt_preds by 1 *)

(*let _= out_warning "finite_models uncomment in is_fp_constant"*)

    
let is_fp_constant fp = 
  (((Symbol.get_property fp) = Symbol.Flat) &&
   (Symbol.get_arity fp) = 1)
    
    (* triangluar based on number of occurrences *)
let fill_triang_const_bounds domain flat_sig = 
(* occur map and occur based ordering does not depend on types so do it unifomrly *)
  let add_occ_map pred occ_map = 
    let old_num = 
      try 
	SMap.find pred occ_map
      with 
	Not_found -> 0
    in
    let new_num = old_num + 1 in
    SMap.add pred new_num occ_map 
  in
  let f occ_map c  = 
    let g c_occ_map _sign fp =
      if (is_fp_constant fp) 
      then
	add_occ_map fp c_occ_map
      else
	c_occ_map 
    in
    Clause.fold_pred g occ_map c
  in
  let occ_map = List.fold_left f SMap.empty flat_sig.flattened_clauses in 
  let cmp_num_occ num_occur_map p1 p2 = 
    let get_occ_num pred = 
      try
	(SMap.find pred num_occur_map)
      with 
	Not_found -> failwith ("finite_models: pred: "^(Symbol.to_string pred)^" should be in the occurrence map")
    in
    Pervasives.compare (get_occ_num p1)  (get_occ_num p2)
  in       
  
  let const_list = 
    let f fp _ rest = fp ::rest in 
    SMap.fold f occ_map []
  in
  
  (* type_map: type -> fp_const_list *)
  let f curr_type_map fp = 
    let fp_type = get_val_flat_pred_type fp in  
    try 
      let const_list = SMap.find fp_type curr_type_map in
      SMap.add fp_type (fp::const_list) curr_type_map 
    with 
      Not_found -> 
	SMap.add fp_type [fp]  curr_type_map
  in
  let type_map =  List.fold_left f SMap.empty const_list in
  
  let order_list_to_int_map ordered_const_list =
    let f (i,const_bounds_map) fp = 
      dbg D_const_range (lazy (" adding range bound: "^(string_of_int i)^" for "^(Symbol.to_string fp)));
      (i+1,(SMap.add fp i const_bounds_map)) 
    in
    let (_max_occ,dom_flat_const_bounds) = 
      List.fold_left f (1,SMap.empty) ordered_const_list in 
    dom_flat_const_bounds
  in
  
  let fill fp_type const_list = 
    let type_domain = 
      try 
	SMap.find fp_type domain.type_domain_map
      with
	Not_found -> failwith ("fill_triang_const_bounds: fp_type: "^(Symbol.to_string fp_type)
			       ^" is not in domain.type_domain_map "^" const list "
			       ^(list_to_string Symbol.to_string const_list ","))
    in      
    let ordered_const_list =   List.rev  (List.sort (cmp_num_occ occ_map) const_list) in
    let dom_flat_const_bounds = order_list_to_int_map ordered_const_list in
    type_domain.dom_flat_const_bounds <-  dom_flat_const_bounds
  in
  SMap.iter fill type_map
    

(*------domains should be initialised before use!-----*)

(* we assume that the rest of the state is already initialised *)

let init_domain input_sig flat_sig  =   
  let flat_preds = flat_sig.flat_sym_set in (* TODO: add term definitions *)  
  let eq_types = input_sig.basic_input_sig.Clause.sig_eq_types in
  let init_domain = 
    {
     type_domain_map = SMap.empty; 
(*     eq_domain_types = input_sig.basic_input_sig.Clause.sig_eq_types; *)
     dom_flat_preds = flat_preds; (* TODO: add term definitions *)  
     flat_pred_ranges_map =  SMap.empty;   (* map from pred ->  flat_pred_ranges *) 
     switch_pred_to_fp_range = SMap.empty;
     all_switch_atoms = TSet.empty
   }
  in
  let f fp domain =
    let fp_val_type = get_val_flat_pred_type fp in
    let flat_pred_ranges = 
      {
       fp_pred = fp;
       fp_pred_type = fp_val_type;
       fp_current_range = 0; 
       fp_range_map = IntMap.empty
     }
    in
    let type_domain = 
      {
       dom_type = fp_val_type;
       is_eq_domain = SSet.mem fp_val_type eq_types;
       dom_current_bound = 0; 
       dom_elements_map = IntMap.empty; 
       dom_flat_const_bounds = SMap.empty;
       dom_dis_eq_axioms = [];
     }
    in
    domain.type_domain_map <- SMap.add fp_val_type type_domain domain.type_domain_map;
    domain.flat_pred_ranges_map <- SMap.add fp flat_pred_ranges domain.flat_pred_ranges_map; 
    domain
  in
  let domain = SSet.fold f flat_preds init_domain in 
(*  out_warning " commented fill_triang_const_bounds domain flat_sig;";*)
  fill_triang_const_bounds domain flat_sig; 
  domain


(*-----------------------*)  
let get_domain_elements type_domain bound = 
  assert (bound <= type_domain.dom_current_bound);
  let f i dom_elem rest = 
    if i<= bound 
    then 
      (dom_elem::rest)
    else 
      rest 
  in
  List.rev 
    (IntMap.fold f type_domain.dom_elements_map [])
    (* fold is in increasing order so we reverse to get increasing order in the result*)
    

(*-----------------------*)  

(* symbol is a flat symbol, fp_range_switch_pred  is the predicate added to the clause *)
(* to encode crurrent range of the fp *)
(* ex if symb is R and domain terms [1;..;n] then *)
(* the result is range_switch_fp_n \/ R(1,x_1,x_2)\/R(2,x_1,x_2)\/...\/R(n,x_1,x_2)*)


let axiom_fp_range bound_pred symb dom_elements =
  let (symb_types, _bool_type) = Symbol.get_stype_args_val_def symb in
  (* first is val type  *)
  let arg_types, val_type =
    match symb_types with
    | h:: tl -> (tl, h)
    | []-> failwith "axiom_dom_pred_symb: symb should have at least one arg"
  in
  let var_env = Var.init_fresh_vars_env () in
  let rec get_var_args rest_vars rest_arg_types =
    match rest_arg_types with
    | [] -> List.rev rest_vars
    | h:: tl ->
	let new_vars = (add_var_term (Var.get_next_fresh_var var_env h)):: rest_vars in
	get_var_args new_vars tl
  in
  let var_args = get_var_args [] arg_types in
  (*
    let rec get_var_args rest current_var i =
    if i = 0 then List.rev rest
    else
    get_var_args
    ((add_var_term current_var):: rest) (Var.get_next_var current_var) (i -1)
    in
    let var_args =
    get_var_args [] (Var.get_first_var ()) ((Symbol.get_arity symb) -1)
    in
   *)
  let f rest dom_el =
    (add_fun_term symb (dom_el:: var_args)):: rest
  in
  let tstp_source = Clause.tstp_source_axiom_domain in
  let new_cl =
    (create_clause tstp_source (bound_pred:: (List.fold_left f [] dom_elements))) in

  dbg D_range_axs (lazy (Clause.to_string new_cl));
  new_cl

(*-----------------------*)
(*------------------*)
let get_range_bound_sw_pred domain switch_pred = 
  try 
    let (_fp,i) = SMap.find switch_pred domain.switch_pred_to_fp_range in 
    i  
  with 
    Not_found -> failwith "get_range_bound_sw_pred: switch_pred Not_found"

let sw_to_fp_i domain switch_pred = 
  (try
    SMap.find switch_pred domain.switch_pred_to_fp_range 
  with 
    Not_found -> failwith "filter_max_ranges: switch_pred Not_found"
  )
    
(*--------------------------------------------*)
let is_max_range_sw_const domain switch_pred =
  let (fp,i) = sw_to_fp_i domain switch_pred in    
  if (is_fp_constant fp) 
  then 
    try 
      let max_bound = 
	let fp_type = get_val_flat_pred_type fp in  
	let type_domain = SMap.find fp_type domain.type_domain_map in
	SMap.find fp type_domain.dom_flat_const_bounds 
      in
      assert(i<=max_bound);
      i = max_bound
    with 
      Not_found -> false
  else
    false

(*----------------------*)

let filter_max_ranges domain switch_preds = 
  let f fp_max_range_map sw_pred = 
    let (fp,i) = sw_to_fp_i domain sw_pred in        
    try 
      let (curr_bound,sw_fp_pred) = SMap.find fp fp_max_range_map in
      if (curr_bound < i) 
      then 
	SMap.add fp (i, sw_pred) fp_max_range_map 
      else
	fp_max_range_map
    with 
      Not_found -> 
	SMap.add fp (i, sw_pred) fp_max_range_map 
  in
  let fp_max_range_map = List.fold_left f SMap.empty switch_preds in 

  (* from map to list*)
  let f fp (i,sw_pred) rest = sw_pred::rest in 
  let max_range_sw_list = SMap.fold f fp_max_range_map [] in 
  max_range_sw_list
    
(*------*)
let filter_out_max_range_fp_const domain switch_preds = 
  List.filter (fun sw -> not (is_max_range_sw_const domain sw)) switch_preds

let filter_min_ranges domain switch_preds = 
  let compare_range sw_p1 sw_p2 = 
    Pervasives.compare (get_range_bound_sw_pred domain sw_p1) (get_range_bound_sw_pred domain sw_p2)
  in
  list_find_all_min_elements compare_range switch_preds

let cmp_sw_arity domain sw_1 sw_2 = 
  let (fp_1,_i) = sw_to_fp_i domain sw_1 in 
  let (fp_2,_i) = sw_to_fp_i domain sw_2 in 
  Pervasives.compare (Symbol.get_arity fp_1) (Symbol.get_arity fp_2) 
    
let filter_min_arity domain switch_preds = 
  list_find_all_min_elements (cmp_sw_arity domain) switch_preds
    
    

(*------------------*)
let get_domain_fp_active_switch_preds domain = 
  let f fp fp_ranges rest = 
    try 
      let fp_range = IntMap.find fp_ranges.fp_current_range fp_ranges.fp_range_map in
      TSet.add fp_range.fp_range_switch_atom rest
    with 
      Not_found -> failwith "get_domain_fp_switch_preds"
  in
  SMap.fold f domain.flat_pred_ranges_map TSet.empty

(* resturns (assumtions_list,adjoint_assumtions_list) *)
let get_domain_assumptions domain = 
  let active_switch_preds = get_domain_fp_active_switch_preds domain in
  
  let inactive_switch_preds = TSet.diff domain.all_switch_atoms active_switch_preds in

  let active_switch_preds_list = TSet.elements active_switch_preds in 

  let inactive_switch_preds_list = TSet.elements inactive_switch_preds in 

  let neg_active_switch_preds_list = List.map add_neg_atom active_switch_preds_list in 

(*  out_warning (" assumptions_list: remvoved inactive_switch_preds_list ");*)
  let assumptions_list = neg_active_switch_preds_list @inactive_switch_preds_list in 

  let adjoint_assumptions_list = active_switch_preds_list in (* predicates ajoint to simplified clauses *)

  dbg D_assumptions (lazy ("assumptions_list "^(Term.term_list_to_string assumptions_list)));
  dbg D_assumptions (lazy ("adjoint_assumptions_list "^(Term.term_list_to_string adjoint_assumptions_list)));
  (assumptions_list, adjoint_assumptions_list)

(*-------------------*)
let get_diseq_axioms domain = 
  let f _type type_domain rest = (type_domain.dom_dis_eq_axioms)@rest in
  SMap.fold f domain.type_domain_map []

(*------------------*)

let get_active_range_axioms domain = 
  let f fp flat_pred_ranges rest = 
    try 
      let fp_range = IntMap.find flat_pred_ranges.fp_current_range flat_pred_ranges.fp_range_map in 
      fp_range.fp_range_axiom :: rest 
    with
      Not_found -> failwith ("get_active_range_axioms  range not found for "^(Symbol.to_string fp))
  in
  SMap.fold f domain.flat_pred_ranges_map []

(*------------------*)
let get_domain fm_state = fm_state.domain

(*------------------*)
let get_domain_size domain =
(* get max of current bounds among domains*)
  let f _type type_domain curr_max = 
    if curr_max >=  type_domain.dom_current_bound
    then 
      curr_max 
    else 
      type_domain.dom_current_bound
  in
  SMap.fold f domain.type_domain_map 0
    
(*----------------------cyclic/non-cyclic-------------------------*)
(*--------------- SCC based non-flattening -----------------------*)

module DGS = Graph.Imperative.Digraph.Concrete(Symbol.Key)

(* Strongly connected component *)
module DGS_SCC = Graph.Components.Make(DGS)

(* type1 -> type2 graph if there is func. with arg in type1 and val in type2 *)
(* for predicates we add vetecies without edges *)
let get_type_graph signature =
  let type_graph = DGS.create ~size:1001 () in
  let f symb =
    let (arg_types, val_type) = Symbol.get_stype_args_val_def symb in
    if (val_type == Symbol.symb_bool_type)
    then (* just add vertices *)
      (List.iter (DGS.add_vertex type_graph) arg_types)
    else (* add edges *)
      (List.iter (fun t -> DGS.add_edge type_graph t val_type) arg_types)
  in
  SSet.iter f (signature.Clause.sig_fun_preds);
  type_graph

let get_scc type_graph =
  let scc_list = DGS_SCC.scc_list type_graph in
  (* non_cyclic separte scc consisting of a singe vertex v without an edge v->v *)
  let cyclic_scc, non_cyclic_single =
    let f scc_single =
      match scc_single with
      | [v] -> (DGS.mem_edge type_graph v v)
      | _ -> true
    in
    List.partition f scc_list
  in
  let non_cyclic_type_list = List.flatten non_cyclic_single in
  let non_cyclic_type_set = List.fold_left (fun rest t -> SSet.add t rest) SSet.empty non_cyclic_type_list in
  let cyclic_type_list = List.flatten cyclic_scc in
  let cyclic_type_set = List.fold_left (fun rest t -> SSet.add t rest) SSet.empty cyclic_type_list in

  Statistics.incr_int_stat (SSet.cardinal non_cyclic_type_set) Statistics.sat_num_of_non_cyclic_types;

  (cyclic_type_set, non_cyclic_type_set)



(*------------------*)
let init_fm_state input_clauses =
(*
  assert ( (* input clauses should not contain dead clauses *)
  let f c = (Clause.get_is_dead c) in 
  not (List.exists f input_clauses)
  );
 *)
  let basic_input_sig = Clause.clause_list_signature input_clauses in
  let epr_type_set = epr_type_set basic_input_sig in
  let epr_const_set = epr_const_set basic_input_sig epr_type_set in 
  let (cyclic_types, non_cyclic_types) =  (get_scc (get_type_graph basic_input_sig)) in 
  (* note: epr_type_set \subseteq non_cyclic_types *)

  dbg D_cyclic 
    (lazy (" EPR  types: "^(list_to_string Symbol.to_string (SSet.elements epr_type_set) ","))
    );

  dbg D_cyclic 
    (lazy (" Non-cyclic  types: "
	   ^(list_to_string Symbol.to_string (SSet.elements non_cyclic_types) ","))
    );

  dbg D_cyclic 
    (lazy (" Cyclic  types: "
	   ^(list_to_string Symbol.to_string (SSet.elements cyclic_types) ","))
    );

  let input_sig = 
    {
     basic_input_sig = basic_input_sig;
     epr_type_set = epr_type_set;
     epr_const_set = epr_const_set;
     cyclic_types = cyclic_types;
     non_cyclic_types = non_cyclic_types;
   }

  in

  let flat_sig = 
    {
     flattened_clauses = [];
     flat_to_orig = SMap.empty;
     flat_sym_set = SSet.empty;   
   }
  in
  let term_defs = (* TODO: term_defs*)
    {
     def_sym_set = SSet.empty;
     term_def_map = TMap.empty; (* term definitions *)   
   }
  in

  fill_flat_signature input_sig flat_sig;  
  flat_sig.flattened_clauses <- preprocess_after_flattening (flat_clause_list input_sig term_defs input_clauses);
  
  let domain = init_domain input_sig flat_sig in
  (*assign_all_fp_ranges domain 1; ... make all ranges non-empty *) 
  
  let fm_state = 
    {
     input_clauses = input_clauses;
     input_sig = input_sig;
     flat_sig = flat_sig;
     term_defs = term_defs;
     domain = domain;
     lemmas = [];
   }
  in
  fm_state

(*-------------------*)
let get_flat_clauses fm_state = 
  fm_state.flat_sig.flattened_clauses

(*-------------------*)

let get_non_flat_eq_axioms fm_state =
  let input_sig = fm_state.input_sig in
  let input_bsig = fm_state.input_sig.basic_input_sig in
(*  let flat_sig = fm_state.flat_sig in *)
  let non_flat_eq_types =
    if !current_options.sat_non_cyclic_types (* subsumse epr_types*)
    then
      (SSet.inter input_sig.non_cyclic_types input_bsig.Clause.sig_eq_types)
    else
      if !current_options.sat_epr_types
      then
	(SSet.inter input_sig.epr_type_set input_bsig.Clause.sig_eq_types)
      else
	SSet.empty
  in
(* compute sig of flat clauses *)
  let csig = Clause.clause_list_signature (get_flat_clauses fm_state) in
  csig.Clause.sig_eq_types <- non_flat_eq_types; (* override eq_types *)

(*
  let csig =
  {
  Clause.sig_fun_preds =
  SSet.union flat_sig.flat_sym_set input_bsig.Clause.sig_fun_preds;
  
  Clause.sig_eq_types = non_flat_eq_types;
  Clause.sig_pure_dis_eq_types = SSet.empty;
  Clause.sig_flat_args = flat_sig.Clause.sig_flat_args
  }
  in
 *)
  let non_flat_eq_ax = Eq_axioms.typed_eq_axioms_sig csig in
(*	out_str ("\n NON Flat eq ax: "^(Clause.clause_list_to_string non_flat_eq_ax )^"\n");*)
  non_flat_eq_ax

