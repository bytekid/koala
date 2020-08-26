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
open Statistics
open Logic_interface 




(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_input

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_input -> "input"
	
let dbg_groups =
  [
   D_trace; 
   D_input;
 ]
    
let module_name = "type_inf"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)

    

(* we assume all symbols we are dealing with are put to symbol_db_ref *)

(* we assume that the problem is typed initially, *)
(* (in fof, cnf all types initially are $i type);*)
(* then we 1) sub-type each type with (symbol, arg_ind) arg_ind includes value *)
(* 2) merge sub_types according occurences in args and var linking *)
(* we assume that sub_types of different types are never merged i.e. initially, the problem was correctly typed *)
(* 3) collaps sub_types due to unshielded positive eq: x=t, t=x, x=y *)
(*    we collaps all sub_types of eq_type   (we reinstate original type for any symbol with is type)  overriding sub_typing       *)

type sub_type =
    {
     sym : symbol;

     (* the number in the list of arguments, 0 is the value type *)
     arg_ind : int;
     arg_type : symbol
   }

let sub_type_to_str st =
  "$$"^"_"
  ^(Symbol.to_string st.sym)^"_"
  ^(string_of_int st.arg_ind)^"_"
  ^(Symbol.to_string st.arg_type)

      
let create_sub_type sym arg_ind arg_type =
  {
   sym = sym;
   arg_ind = arg_ind;
   arg_type = arg_type;
 }

let sub_type_to_type st =
  let st_name = sub_type_to_str st in
  (* we use the same functions as in parsing *)
  let st = Parser_types.ttf_atomic_type_fun st_name in
  Symbol.assign_is_essential_input true st;
  st

(* sub_type element of union find *)

module SubTypeE =
  struct
    type t = sub_type	  
    let equal t1 t2 =
      (t1.sym == t2.sym)
	&&
      (t1.arg_ind = t2.arg_ind)
	&&
      (t1.arg_type == t2.arg_type)	
    let hash t = ((Symbol.get_fast_key t.sym) lsl 5) + t.arg_ind

(* compare *)
    let cmp_sym t1 t2 =  Symbol.compare t1.sym t2.sym  
    let cmp_arg_ind t1 t2 = Pervasives.compare t1.arg_ind t2.arg_ind  
    let cmp_arg_type t1 t2 = Symbol.compare t1.arg_type t2.arg_type  
    let compare t1 t2 =  
      lex_combination [cmp_sym; cmp_arg_ind; cmp_arg_type] t1 t2
  end

module UF_ST = Union_find.Make(SubTypeE)

(* module VarTable = Hashtbl.Make (Var) *)
(* module SSet = Symbol.Set *)

module SubTypeSet = Set.Make(SubTypeE)

module SType_Map = Map.Make(SubTypeE)

module UF_Var = Union_find.Make(Var.VKey)

(*----------------*)
(* pair of symbol position is used to identify (symbol,position) that can not be used as guarding *)

type symb_pos = (symbol * int)

module SP = 
  struct
    type t = symb_pos
    let compare sp1 sp2 = pair_compare_lex Symbol.compare Pervasives.compare sp1 sp2 
  end

module SP_Set = Set.Make (SP)
(*---------------*)

(*----------------------------------------- -*)
(* use mapping in context: var_subtype from (clause,var) -> sub_type *)
(* this mapping is global *)
(* subtypes are not normalised in this map, since dynammically can chage from clause to clause *)
(*  *)

type clause_var = (clause * var)

module CV = 
  struct 
    type t = clause_var 
    let compare cv1 cv2 = pair_compare_lex Clause.compare Var.compare cv1 cv2
  end

module CV_Map = Map.Make (CV)

type context =
    {
     uf : UF_ST.t;
     
(* old *)
     (* types with X=Y, X=t, t=X are collapsed since all arg_subtypes should be merged *)
     (* can be relaxed later *)
     (* collapsed types implicitly override sub_types *)
     mutable collapsed_types : SSet.t;

(* collapsed types of x with clauses x =y \/ C where x or y does not occur in any proper term in C *)
     mutable pure_var_collapsed_types : SSet.t;

     mutable clause_var_subtype : sub_type CV_Map.t;

     (* not_shallow_guards: pair of (pred_symb, position)  which are *)
     (* not sutable for being used as a shallow guard (equality is not included here) *)
     (* currently simplified condition: (p,i) is not_shallow_guard if it has a positive occurence P(t,x_i,s) \/ C *)    
     (* arg positions start from 1 *)
     mutable non_guarding_symb_pos : SP_Set.t;
     mutable current_clause : clause param;

(* ---- used for statistics ---- *)
(* types that use guards, this will include collapsing types; not normalised *)
     mutable guarded_subtype_set : SubTypeSet.t 

   }

let context_get_current_clause context = 
  get_param_val context.current_clause


(*--aux--*)
let get_sym_types sym = Symbol.get_stype_args_val_def sym

(* aux fun *)
let get_val_type sym = Symbol.get_val_type_def sym

let get_val_sub_type sym =
  let val_type = get_val_type sym in
  let val_sub_type = (create_sub_type sym 0 val_type) in
  val_sub_type

(*---------check that literal is guarding for a vairable x-----------*)

(* the literal lit is (shallowly) guarding for a variable v if *)
(*  1)  the literal is negative 2) is non-equational and  *)
(*  3) at there is a (shallow) position in atom of lit in which x occurs and *)
(*       this position is not in context.non_guarding_symb_pos *)

(*  is_shallow_guarding returns Def(sub_type) where sub_type is the subtype of a guarding position *)
(*  or Undef if there exist no guarding position in lit *)

let shallow_guarding_subtype_lit context var_term lit = 
  if (Term.is_neg_lit lit) && (not (Term.is_eq_lit lit))
  then 
    let atom = Term.get_atom lit in 
    match atom with 
    |Term.Fun (pred_symb, args, _inf) ->
	let arg_types, _val_type = get_sym_types pred_symb in
	let arg_list = Term.arg_to_list args in

	let f (arg_ind, sub_type_param) arg_type arg_term =
	  if (param_is_def sub_type_param)
	  then 
	    (arg_ind, sub_type_param)
	  else
	    let new_arg_ind = arg_ind + 1 in 
	    if ((var_term == arg_term) (* we assume all terms are shared *) 
		  &&	
		(not (SP_Set.mem (pred_symb,arg_ind) context.non_guarding_symb_pos))) 
	    then 
	      let arg_sub_type = create_sub_type pred_symb arg_ind arg_type in
	      (arg_ind, Def(arg_sub_type))  
	    else
	      (new_arg_ind, Undef)
	in
	let (_final_arg_ind, sub_type_param) =  
	  List.fold_left2 f (1, Undef) arg_types arg_list 
	in 
	sub_type_param
    |Term.Var _ -> failwith "is_shallow_guarding pred should not be var"
  else
    Undef

(* returns guardin subtype; can be extended to also return guarding literal*)
let shallow_guarding_subtype_lit_list context var_term lit_list = 
  let f sub_type_param lit =
    if (param_is_def sub_type_param)
    then 
      sub_type_param 
    else
      (shallow_guarding_subtype_lit context var_term lit) 
  in
  List.fold_left f Undef lit_list

let shallow_guarding_subtype_clause context var_term =
  let current_clause =  (Clause.get_literals (get_param_val context.current_clause)) in
  shallow_guarding_subtype_lit_list context var_term current_clause

(*------------*)

(* not used *)
(* var -> sub_type table linking variables to a choosen sub_type of this var; local to each clause *)
(* needs to be reset with each clause, not very good *)

(* type vtable = (sub_type) VHashtbl.t *)

(*---------------------------------------------------*)
(*    top_type : sub_type option;                    *)
(* f(t_1,t_2) at t_2 we have top_type_top is f_arg_2 *)
(* top_type_opt_term_list = [(Some(top_sub_type),fun_term);(None, pred_term)...]  *)
    

let rec extend_uf_types context top_sub_type_opt_term_ass_list =
  let current_clause = context_get_current_clause context in
  (* first define a function for processing arguments that we will used several times *)
  let process_args_fun sym args =
    let arg_types, _val_type = get_sym_types sym in
    (*    let arg_list = Term.arg_to_list args in*)
    let (_, _, ass_list) =
      Term.arg_fold_left
	(fun (arg_ind, arg_types_rest, ass_list_rest) arg ->
	  match arg_types_rest with
	  | h:: tl ->
	      let arg_sub_type = create_sub_type sym arg_ind h in
	      ((arg_ind +1), tl, ((Some (arg_sub_type), arg):: ass_list_rest))
	  |[] -> failwith "process_args_fun: should not happen"
	)
	(1, arg_types,[])
	args
    in
    (* add_ass_list is reversed but should not matter *)
    ass_list 
      
      (*   extend_uf_types context new_ass_list *)
  in

(* process  var_term and new sub_type which this var should belong to; used in several places *)
  let process_var_subtype var_term sub_type =     
    try
      let var_sub_type = CV_Map.find (current_clause, var_term) context.clause_var_subtype in
      UF_ST.union context.uf sub_type var_sub_type;
      (* extend_uf_types context tl_ass *)
    with
      Not_found ->
	(
	 (* VHashtbl.add vtable var top_sub_type; *)
	 context.clause_var_subtype <- 
	   CV_Map.add (current_clause, var_term) sub_type context.clause_var_subtype;
	 UF_ST.add context.uf sub_type;
	 (* extend_uf_types context tl_ass *)
	)
  in
  
  (*----------- main part ---------------*)

  let f top_sub_type_opt_term = 
    match top_sub_type_opt_term with
    | (Some(top_sub_type), Term.Fun (sym, args, _)) ->
	(* here we assume that sym is fun (not pred) since Some *)
	let val_sub_type = get_val_sub_type sym in
	UF_ST.union context.uf top_sub_type val_sub_type;
	process_args_fun sym args
	  
    | (Some(top_sub_type), Term.Var(var_term, _inf)) ->
	(process_var_subtype var_term top_sub_type;
	 [])
    | (None,lit) ->
	(* here we assume that sym is pred/or ~pred, or f(t) where f e.g. x != f(y)  since None *)
	let atom = Term.get_atom lit in
	(* dealing with equality *)
	if (Term.is_eq_atom atom)
	then
	  match atom with
	  | Term.Fun (_sym, args, _) ->
	      let (type_term_eq, t, s) = get_triple_from_list (Term.arg_to_list args) in
	      let eq_v_type =
		try
		  Term.get_top_symb type_term_eq
		with 
		  Term.Var_term ->
		    failwith 
		      "equality should not have var as the type argument; \
		      proabably equality axioms are added which are not needed here"
	      in
	      
	      (*
		if (not (Term.is_neg_lit lit)) (* positive eq *)
		then
		(* for negative eq  more can be done than not putting it into collapsed? *)
	       *)
	      begin
		match (t, s) with
		| (Term.Fun(sym1, args1, _), Term.Fun(sym2, args2, _)) ->
		    (
		     let val_sub_type1 = get_val_sub_type sym1 in
		     let val_sub_type2 = get_val_sub_type sym2 in
		     UF_ST.add context.uf val_sub_type1;
		     UF_ST.add context.uf val_sub_type2;
		     
		     (* (if (not (Term.is_neg_lit lit)) (* positive eq *)
		        then
		        
		        (UF_ST.union context.uf val_sub_type1 val_sub_type2;)
                        
		        else () (* neg eq *)
                        );
                      *)
		     UF_ST.union context.uf val_sub_type1 val_sub_type2;
		     let add_ass_list1 = process_args_fun sym1 args1 in
		     let add_ass_list2 = process_args_fun sym2 args2 in
		     add_ass_list1@add_ass_list2
		    )
		      
		      (* type collaps cases *)
		      
		| ((Term.Var (v, _) as v_term), (Term.Fun(sym, args, _) as f_term))
		| ((Term.Fun(sym, args, _) as f_term), (Term.Var (v, _) as v_term))
		  ->		  
		    (*  (if (not (Term.is_neg_lit lit)) (* positive eq *) *)
		    (*    then *)
		    (*    (context.collapsed_types <- *)
		    (*    SSet.add eq_v_type context.collapsed_types;) *)
		    (*    else () *)
		    (*    ); *)
                    (*   *)
		    (* the same for both negative and positive X!=f(X) *)
		    (* better can be done for negative *)		    

       		    let fun_val_sub_type = get_val_sub_type sym in
		    begin
		      if (Term.is_neg_lit lit)
		      then 
			(
			 process_var_subtype v fun_val_sub_type;		
			)
		      else
			(
			 match (shallow_guarding_subtype_clause context v_term) with 		      
			 |Def(guarding_subtype) ->	
			     (process_var_subtype v guarding_subtype;			   
			      UF_ST.union context.uf guarding_subtype fun_val_sub_type;   
			      context.guarded_subtype_set <- 
				SubTypeSet.add guarding_subtype context.guarded_subtype_set;
			     )
			 | Undef -> 
			     (* there is no guard *)
			     (
			      process_var_subtype v fun_val_sub_type;
			      context.collapsed_types <-
				SSet.add eq_v_type context.collapsed_types;			       	    	   
			     )
			)
		    end;
		    [(None,f_term)]
		      
		| ((Term.Var(v1, _) as v1_term), (Term.Var (v2, _) as v2_term)) ->
		    ( 
                      (* we assume that x!=y are eliminated during preprocessing; *)
		      (if (Term.is_neg_lit lit)
		      then 
			( out_warning "type_inf: x!=y should be eliminated by preprocessing"));
		      
		      let guard_param_v1 = shallow_guarding_subtype_clause context v1_term in
		      let guard_param_v2 = shallow_guarding_subtype_clause context v2_term in
		      
		      (match (guard_param_v1, guard_param_v2) with 
		      |(Def (gv1) ,Def(gv2)) -> 
			  UF_ST.union context.uf gv1 gv2;
			  process_var_subtype v1 gv1;
			  process_var_subtype v2 gv2;
			  context.guarded_subtype_set <- 
			    SubTypeSet.add gv1 context.guarded_subtype_set;
		      |_ ->
			  begin
			    (* we assume that all literals of the form x=y in the clause are processed last! *)
			    (
			     try
			       let var_sub_type_1 = CV_Map.find (current_clause, v1) context.clause_var_subtype in
			       let var_sub_type_2 = CV_Map.find (current_clause, v2) context.clause_var_subtype in
			       UF_ST.union context.uf var_sub_type_1 var_sub_type_2;
			       (* extend_uf_types context tl_ass *)
			     with
			       Not_found ->  
				 (
				  context.pure_var_collapsed_types <- 
				    SSet.add eq_v_type context.pure_var_collapsed_types
				 )
			    );
			    context.collapsed_types <-
			      SSet.add eq_v_type context.collapsed_types
			  end
		      );
		      [] (* no additianl ass_list*)		     		    
		     )
	      end	      
	  | _ -> failwith "extend_uf_types: non-eq 2"
	else (* non eq predicate or fun *)
	  (match atom with
	  | Term.Fun (sym, args, _) ->
	      (process_args_fun sym args)
	  | _ -> failwith "extend_uf_types: var"
	  )
  in  (* end of add_ass_list *)
  List.iter 
    (fun top_sub_type_opt_term -> 
      let new_list = f top_sub_type_opt_term in 
      extend_uf_types context new_list)
    top_sub_type_opt_term_ass_list    

    
let extend_uf_types_clause context clause =
  let clause_lits = Clause.get_literals clause in
  context.current_clause <- Def(clause);
  let is_pur_var_eq_atom atom = 
    match (term_eq_view_type_term atom) with
    |Def(Eq_type_term(_type_term,t,s)) -> 
	(Term.is_var t) && (Term.is_var s)
    |Undef -> false 
  in
  let (pure_var_eq, non_pure_var_eq) = List.partition is_pur_var_eq_atom clause_lits in
(* non_pure_eq processed first *)
  let ordered_lits = non_pure_var_eq @ pure_var_eq in
  let top_sub_type_opt_term_ass_list =
    List.map (fun l -> (None, l)) ordered_lits
  in
  (* let vtable = VHashtbl.create 10 in *)
  extend_uf_types context top_sub_type_opt_term_ass_list

let extend_uf_types_clause_list context clause_list =
  List.iter (extend_uf_types_clause context) clause_list

module STypeTable = Hashtbl.Make(SubTypeE)

(* get_subt_nf_to_all_subt returns *)
(* STypeTable maping sub_type normal form into list of all sub_types it represents *)
(* does not take into account collapsed types *)

let st_nf_to_all_st_table context =
  let st_table = STypeTable.create (UF_ST.length context.uf) in
  let iter_fun st st_nf =
    try
      let old_list = STypeTable.find st_table st_nf in
      STypeTable.replace st_table st_nf (st:: old_list)
    with
      Not_found ->
	STypeTable.add st_table st_nf ([st])
  in
  UF_ST.iter iter_fun context.uf;
  st_table


let type_term_from_type_symb type_symb =
  Parser_types.create_theory_term type_symb [] 
    

(*------------------------------*)
exception Neg_eq_different_types
(* if Neg_eq_different_types then the clause is a tautology! *)
(* we assume that signature already retyped ! *)

let type_equality_lit context lit =
  let atom = Term.get_atom lit in
  (* dealing with equality *)
  if (Term.is_eq_atom atom)
  then
    match atom with
    | Term.Fun (_sym, args, info) ->
	
	let (type_term_eq, t, s) = get_triple_from_list (Term.arg_to_list args) in
	
	let eq_v_type =
	  try
	    Term.get_top_symb type_term_eq
	  with Term.Var_term ->
	    failwith
	      "equality should not have var as the type argument; proabably equality axioms are added which are not needed here"
	in
	if (SSet.mem eq_v_type context.collapsed_types)
	then
	  lit (* do not do anything to collapsed types *)
	else
	  begin
	    try
	      let new_eq_atom = 	     
		match (t, s) with
		| (Term.Fun(sym_t, _args1, _), Term.Fun(sym_s, _args2, _)) ->		
		    
		    (* newtypes of t and s should be the same so we take t  *)
		    (* out_str (Symbol.to_string sym_t);
		       out_str (Symbol.to_string sym_s);
		     *)
		    let t_vt = get_val_type sym_t in
		    let s_vt = get_val_type sym_s in
		    
		    (* out_str (Symbol.to_string t_vt);
		       out_str (Symbol.to_string s_vt);
		     *)
		    (if ((Term.is_neg_lit lit) &&
			 (not (t_vt == s_vt)))
		    then
		      raise Neg_eq_different_types
		    else ());
		    
		    assert (t_vt == s_vt);
		    let new_eq_type_term = type_term_from_type_symb t_vt in
		    let new_eq_atom =  add_typed_equality_term new_eq_type_term t s in
		    new_eq_atom			   
		| (Term.Var (v, _), _)
		| (_,Term.Var (v, _)) -> 
		    ( try
		      let current_clause = context_get_current_clause context in
		      let var_sub_type = CV_Map.find (current_clause, v) context.clause_var_subtype in
		      let sb_nf = UF_ST.find context.uf var_sub_type in
		      let eq_type_symb = sub_type_to_type sb_nf in
		      let new_eq_type_term = type_term_from_type_symb eq_type_symb in
		      let new_eq_atom = add_typed_equality_term new_eq_type_term t s in
		      new_eq_atom
		    with  		     	  
		      Not_found -> failwith "variables should be subtyped here"
		     )
	      in
	      (
	       if (not (Term.is_neg_lit lit)) (* positive eq *)
	       then
		 new_eq_atom
	       else
		 (add_neg_atom new_eq_atom)
	      )		    		
	    with Not_found -> failwith "type_equality_lit: should be subtyped" (* cna be thown by *)
	  end
    |Term.Var _ -> failwith "type_equality_lit: should be atom"
  else
    lit (* not euqality*)


(*----- fill non_guarding positions ------*)

let fill_non_guarding_set ng_set clause_list = 
  let fill_non_guarding_set_clause ng_set clause = 
    let fill_non_guardig_set_lit ng_set lit = 
      if ((Term.is_neg_lit lit) || (Term.is_eq_lit lit))
      then
	ng_set 
      else
	(* positive non-equality literal *)
	(* collect all variale positions *)
	begin
	  match lit with  
	  |Term.Fun(pred_symb,args,_inf) ->
	      let f (arg_ind, current_set) term =
		let new_arg_ind = arg_ind + 1 in
		let new_set = 
		  if (Term.is_var term) 
		  then 
		    SP_Set.add (pred_symb,arg_ind) current_set 
		  else
		    current_set
		in
		(new_arg_ind, new_set)
	      in 
	      let (_num_of_args,new_set) = Term.arg_fold_left f (1, ng_set) args in
	      new_set
	  | Term.Var _-> failwith "fill_non_guardig_set_lit"
	end
    in
    List.fold_left fill_non_guardig_set_lit ng_set (Clause.get_literals clause)
  in
  List.fold_left fill_non_guarding_set_clause ng_set clause_list


(*----------- monotonox version ---------*)
    
type pred_ext = symbol * bool (* predicate extension pos/neg *)

type pred_ext_lit = (bool * pred_ext)
type pre_prop_clause = pred_ext_lit list

(*
  type mon_env = 
  {
  mon_clauses : clause list; 
  mutable mon_types_to_process : SSet.t;
  mutable mon_pre_constraints : pred_ext list;
  mutable mon_collapsed_types : SSet.t;
  (* mon_current_clause = Undef; *)
  }
 *)



module PredExtKey =
  struct
    type t = pred_ext	  
    let equal (p1,b1) (p2,b2) = (p1 == p2) && (b1 = b2)

(* compare *)
    let cmp_sym (p1,_) (p2,_) =  Symbol.compare p1 p2  
    let cmp_b (_,b1) (_,b2) = Pervasives.compare b1 b2

    let compare p_e1 p_e2 =  
      lex_combination [cmp_sym; cmp_b] p_e1 p_e2
  end

module PE_Map = Map.Make(PredExtKey)
module PE_Set = Set.Make(PredExtKey)

    

(*-------*)


(* a type is monotone if all its subtypes are monotone *)
type mon_env = 
    {

(*   
     (* used as a hash for var guards, for vars in predicates needs to be extended before put to  mon_pre_constraints *)
     mutable mon_var_guards : (pred_ext_lit list) VMap.t; 
 *)
     mutable mon_pre_constraints : (pre_prop_clause list) SType_Map.t; (* a map from sub_types to pre-constraints *)

     (* all preds that are used in pred_ext in constraints for corresponding sub_type *)
     mutable mon_pred_map : SSet.t SType_Map.t; 

     (* mutable mon_collapsed_types : SSet.t; *) (* types that can not be shown monotone by monotonox type reasoning *)
     mon_st_context : context;
   }


let create_mon_env st_context = 
  {
(*   mon_var_guards = VMap.empty; *)
   mon_pre_constraints = SType_Map.empty;
   mon_pred_map = SType_Map.empty;
   mon_st_context = st_context
 }



(*--------helpers ---------*)
let mon_add_pre_constr mon_env sub_type pre_constr = 
  let old_pre_constr_list =
    try 
      SType_Map.find sub_type mon_env.mon_pre_constraints 
    with 
      Not_found -> [] 
  in
  mon_env.mon_pre_constraints <- SType_Map.add sub_type (pre_constr::old_pre_constr_list)  mon_env.mon_pre_constraints

let mon_add_pred_map mon_env sub_type pred = 
  let old_pred_set =
    try 
      SType_Map.find sub_type mon_env.mon_pred_map
    with 
      Not_found -> SSet.empty
  in
  let new_pred_set = SSet.add pred old_pred_set in 
  mon_env.mon_pred_map <- SType_Map.add sub_type new_pred_set mon_env.mon_pred_map

let norm_sub_type st_context sub_type = (UF_ST.find st_context.uf sub_type)

(*------*)
exception Neq_Guarded (* do not need to add guarding constraint *)

(* can raise Neq_Guarded *)
let mon_get_var_guards mon_env (* !var_guards_map *) cl_lits v_sub_type v = 
(* add hashing later *)
(*  try 
    VMap.find v !mon_env.mon_var_guards_map 
    with 
    Not_found -> 
 *)
  (
   let f rest lit = 
     let atom = Term.get_atom lit in
     let sign = Term.is_pos_lit lit in 
     
     (* equality *)
     match (term_eq_view_type_term atom) with 
     | Def(Eq_type_term (_eq_type, s, t)) -> 
	 if (not sign)  (* negative equality *)
	 then
	   match (s,t) with 	       
	   | (Term.Var (v_eq, _), Term.Fun(_,_,_))
	   | (Term.Fun (_,_,_),Term.Var (v_eq, _)) -> 	       
	       if (v == v_eq) 
	       then 
		 raise Neq_Guarded
	       else 
		 rest
	   | _-> rest
	 else (* pos eq *)	
	   rest
     | Undef -> (* non-eq*)
	 begin
	   match atom with 
	   |Term.Fun(pred,args, _) -> 
	       let args_list = Term.arg_to_list args in 
	       let v_is_in_args = 
		 (List.exists 
		    (fun t ->
		      match t with 
		      |Term.Var(v_t,_) -> v == v_t
		      |_-> false
		    )
		    args_list
		 )
	       in
	       if v_is_in_args 
	       then
		 (
		  mon_add_pred_map mon_env v_sub_type pred;
		  (true,(pred,sign))::rest
		 )
	       else
		 rest
	   |_-> rest (* should not happen *)
	 end
   in
   let pred_ext_list = List.fold_left f [] cl_lits in        
(*       mon_var_guards_map := VMap.add v pred_ext_list mon_var_guards_map; *)
   pred_ext_list
  )


    
(*-----------*)
let mon_process_lit mon_env clause cl_lits lit = 
  let atom = Term.get_atom lit in
  let sign = Term.is_pos_lit lit in 
  let st_context = mon_env.mon_st_context in
  let get_v_subtype v = 
    try 
      let sub_type = CV_Map.find (clause,v) st_context.clause_var_subtype in
      norm_sub_type st_context sub_type
    with 
      Not_found -> failwith "mon_process_lit: vars are assumed to be sub-typed here" 
  in
  let process_var pred_ext_param v =  (* for pred vars we need add a prefix [(pred,(not sign))]  *)
    try
      let v_sub_type = get_v_subtype v in       
      let var_constraint = 
	match pred_ext_param with 
	|Some((_sign,(pred,_ext_sign)) as pred_ext_lit) -> 

	    mon_add_pred_map mon_env v_sub_type pred;
	    pred_ext_lit::(mon_get_var_guards mon_env cl_lits v_sub_type v) 

	|None -> (mon_get_var_guards mon_env cl_lits v_sub_type v)
      in       
      mon_add_pre_constr mon_env v_sub_type var_constraint
    with 
      Neq_Guarded -> ()
  in
  let process_var_term pref t = 
    (match t with 
    | Term.Var (v, _) -> process_var pref v
    | _-> ()
    )
  in
  
  (* equality *)
  match (term_eq_view_type_term atom) with 
  | Def(Eq_type_term (_eq_type, t1, t2)) -> 
      if (not sign)  (* negative equality *)
      then
	() (* neg eq is monotone (since are not used as guards) *)
      else
	begin
	  (* empty prefix for eq atom *)
	  process_var_term None t1;
	  process_var_term None t2;		
	end

(* non-eq *)
  | Undef -> 
      begin
	match atom with 
	|Term.Fun(pred,args, _) -> 
	    let pref = Some ((false,(pred,(not sign)))) in
	    Term.arg_iter (process_var_term pref) args
	|Term.Var (_,_) -> () 
      end

(*------------*)
let mon_process_clause mon_env clause =
  let cl_lits = Clause.get_literals clause in
  List.iter (mon_process_lit mon_env clause cl_lits) cl_lits

let mon_process_clause_list mon_env clause_list = 
  let f c = 
(*    mon_env.mon_current_clause <-c;
      mon_env.mon_current_lits <- Clause.get_literals c;
 *)
    mon_process_clause mon_env c;
  in
  List.iter f clause_list


(*------- using prop solver ----------*)


(*------------------------------*)
exception Type_Undef
let sub_type_inf clause_list =
  
  dbg D_input (lazy ("Input clauses: \n"^(Clause.clause_list_to_string clause_list)));
  let start_time_st_inf = Unix.gettimeofday () in  

  let context =
    {
     uf = UF_ST.create 3001;
     collapsed_types = SSet.empty;
     pure_var_collapsed_types = SSet.empty;
     clause_var_subtype = CV_Map.empty;
     non_guarding_symb_pos = SP_Set.empty;
     current_clause = Undef;
     guarded_subtype_set = SubTypeSet.empty
   }
  in
  dbg D_trace (lazy (" start: fill_non_guarding_set "));
  context.non_guarding_symb_pos <- (fill_non_guarding_set context.non_guarding_symb_pos clause_list);
  dbg D_trace (lazy (" end: fill_non_guarding_set "));

  dbg D_trace (lazy (" start:  extend_uf_types_clause_list "));
  (*------*)
  extend_uf_types_clause_list context clause_list;
  dbg D_trace (lazy (" end:  extend_uf_types_clause_list "));

  context.current_clause <- Undef;

  dbg D_trace (lazy (" start: normalise_guarded_subtype_set  "));
  let normalise_guarded_subtype_set context = 
    let f gs new_set = 
      SubTypeSet.add (UF_ST.find context.uf gs) new_set
    in
    context.guarded_subtype_set <- SubTypeSet.fold f context.guarded_subtype_set SubTypeSet.empty 
  in
  normalise_guarded_subtype_set context;

  (*-----*)
  dbg D_trace (lazy (" end: normalise_guarded_subtype_set "));
  
  dbg D_trace (lazy (" start: st_nf_to_all_st_table "));

  let st_nf_table = st_nf_to_all_st_table context in
  (* process collapsed types in future; eliminate some of them *)
  
  dbg D_trace (lazy (" end: st_nf_to_all_st_table "));

  dbg D_trace (lazy (" start: monotonox "));


  dbg D_trace (lazy (" end: monotonox "));

  dbg D_trace (lazy (" start: stats "));
  (*------------*)
  (* num_of_subtypes (non-collapsed) *)
  
  STypeTable.iter
    (fun nf _st_list ->
      if (SSet.mem nf.arg_type context.collapsed_types)
      then ()
      else
	Statistics.incr_int_stat 1 Statistics.num_of_subtypes
    )
    st_nf_table;
  
  (*------------ statistics/output and an option ----------*)
  let get_non_collapsing_guarding_subtypes context = 
    let f sub_type = 
      not (SSet.mem sub_type.arg_type context.collapsed_types)
    in
    SubTypeSet.filter f context.guarded_subtype_set 
  in
  let non_collapsing_guarding_subtypes = get_non_collapsing_guarding_subtypes context in
  (incr_int_stat (SubTypeSet.cardinal non_collapsing_guarding_subtypes) sat_num_of_guarded_non_collapsed_types);

  (if !current_options.dbg_out_stat || dbg_flag
  then
    begin	
      out_str "\n---------------";
      out_str "Inferred subtypes:\n";
      STypeTable.iter
	(fun nf st_list ->
	  out_str ("NF: "^(sub_type_to_str nf)^" "
		   ^"["^(list_to_string sub_type_to_str st_list ";")^"]\n"
		  )
	) st_nf_table;
      
      out_str "\nCollapsed types: \n";
      SSet.iter
	(fun sym ->
	  out_str ((Symbol.to_string sym)^", ")) context.collapsed_types;
      
      out_str "\nGuarded non-collapsed types:\n ";
      SubTypeSet.iter 
	(
	 fun sub_type -> 
	   out_str (sub_type_to_str sub_type)
	) non_collapsing_guarding_subtypes;
      out_str "\n---------------";
    end 
  );

  dbg D_trace (lazy (" end: stats "));
  dbg D_trace (lazy (" start: retyping "));
  
  let typed_symbs_set_ref = ref SSet.empty in
  
  (* retype the signature *)
  (* add a check when we do not need to do anything: all types collapsed or merged *)
  (* this is for non-equality symbols *)
  if ((Statistics.get_val_stat Statistics.num_of_subtypes) <=1) (* TODO: extend to a proper test as descr. above*)
  then 
    clause_list 
  else
    begin
      let process_sym sym =
        if (SSet.mem sym !typed_symbs_set_ref)
        then () (* already processed *)
        else
          begin
	    try
	      let all_types =
	        match (Symbol.get_stype_args_val sym) with
	        | Def (arg_t, v_t) -> v_t:: arg_t
	        | _ -> raise Type_Undef
	      in
	      let (_, new_types_rev) =
	        List.fold_left
	          (fun (arg_ind, new_types_rest) arg_type ->
		    let arg_sub_type = create_sub_type sym arg_ind arg_type in
		    (*		 out_str ("sub_type: "^(sub_type_to_str arg_sub_type)); *)
		    let new_type =
		      if (SSet.mem arg_type context.collapsed_types)
		      then
		        arg_type
		          (* do not do anything to collapsed types *)
		      else
		        (
		         try
		           let sb_nf = UF_ST.find context.uf arg_sub_type in
		           (*			out_str ("sub_type_nf: "^(sub_type_to_str sb_nf)^"\n"); *)
		           sub_type_to_type sb_nf
		         with
		           Not_found -> arg_type
		        )
		    in
		    ((arg_ind +1), (new_type::new_types_rest))
	          )
	          (0,[])
	          all_types
	      in
	      let new_val_type, new_args_type = split_list (List.rev new_types_rev) in
	      Symbol.assign_stype sym (Symbol.create_stype new_args_type new_val_type);
	      typed_symbs_set_ref:= SSet.add sym !typed_symbs_set_ref;
	      (*       Symbol.out_full sym; *)
	    with
	      Type_Undef -> ()
          end
      in
      let rec process_lit lit =
        let atom = Term.get_atom lit in
        match atom with
        | Term.Fun(sym, args, _info) ->
	    if (Term.is_eq_atom atom)
	    then
	      (let (_type_term_eq, t, s) = get_triple_from_list (Term.arg_to_list args) in
	      (* ignore eq sym and first eq arg *)
	      process_lit t;
	      process_lit s;)
	    else
	      (process_sym sym;
	       List.iter process_lit (Term.arg_to_list args)
	      )
        | Term.Var _ -> ()
      in
      
      let process_clause cl =
        Clause.iter process_lit cl
      in
      List.iter process_clause clause_list;
      
      (*   SymbolDB.iter process_sym !symbol_db_ref;*)
      
      (* 1) type equalities, 2) merge history with christoph, 3) C\/t!=s and s has differen type from t then the clause is a tautology *)
      
      let typed_clause_list =
        let f rest clause =
          try
	    context.current_clause <- Def(clause);
	    (* switching off symbol type check/restore after retyping *)
	    let input_symbol_type_check = !current_options.symbol_type_check in
	    !current_options.symbol_type_check <- false;				
	    let lits = Clause.get_literals clause in
	    let typed_lits =
              List.map (type_equality_lit context) lits

(* Symbol.is_essential_input not appropriate here *)
(*
	      if (Symbol.is_essential_input Symbol.symb_typed_equality)
	      then
	        List.map (type_equality_lit context) lits
	      else
	        lits
*)
	    in
	    let typed_var_lits = Parser_types.retype_lits typed_lits in
	    !current_options.symbol_type_check <- input_symbol_type_check;
	    
	    if (typed_var_lits == lits)
	    then
	      clause::rest
	    else
	      (
	       let tstp_source = Clause.tstp_source_subtyping clause in
	       let new_clause =
	         create_clause tstp_source (Clause.normalise_lit_list term_db_ref typed_var_lits) in

(*	       Clause.assign_replaced_by (Def(Clause.RB_sub_typing new_clause)) clause;	 *)

               Clause.inherit_conjecture clause new_clause; 
	       (*			Clause.inherit_param_modif clause new_clause; *)
	       
	       
	       (*		out_str ("Typed: "^(Clause.to_string new_clause)^"\n"); *)
	       new_clause:: rest
	      )
          with
	    Neg_eq_different_types -> rest
        in
        List.fold_left f [] clause_list
      in
      let end_time_st_inf = Unix.gettimeofday () in
      assign_float_stat (end_time_st_inf -. start_time_st_inf) subtype_inf_time; 
      dbg D_trace (lazy (" end: retyping "));
      typed_clause_list
    end


(*-------------------Commented below-----------------*)

(*
  let rec extend_uf_types context top_type_opt term =
  match term with
  | Term.Fun (sym, args, _) ->
  let arg_types, v_type =
  match (Symbol.get_stype_args_val sym) with
  | Def (arg_t, v_t) -> (arg_t, v_t)
  | _ -> failwith "extend_uf_types: arg_types should be defined"
  in
(* extend args *)
  ignore(
  Term.arg_fold_left
  (fun (arg_ind, arg_types_rest) arg ->
  let h:: tl = arg_types_rest in
  let new_pnt = create_pnt sym arg_ind h in
  extend_uf_types context (Some new_pnt) arg;
  ((arg_ind +1), tl)
  )
  (1, arg_types)
  args
  );

  if (Symbol.is_pred sym)
  then
  (
  if (sym == Symbol.symb_typed_equality)
  then
  match args with
  | [type_eq_; t; s] ->
  if !(Term.is_var t) && !(Term.is_var s)
  then
  ..............
  extend_uf_types context top_type_opt
  ..............
  )
  else
  ( (* fun symb *)
  match top_type_opt with
  | Some top_type ->
  UF_PNT.union context.uf top_type (create_pnt sym 0 v_type);
  | None -> failwith "functions should not be at top"
  )

  | Term.Var (v, _) ->
  let top_type =
  match top_type_opt with
  | Some top_type -> top_type
  | None -> failwith "vars should not be at top"
  in
  try
  let v_type = VHashtbl.find context.vtable v in
  UF_PNT.union context.uf top_type v_type
  with
  Not_found ->
  VHashtbl.add context.vtable v top_type
 *)

(* let typify_clause clause type_context =

   let typify_clause_list clause_list =*)
