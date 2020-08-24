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
open Statistics
open Options

type var = Var.var
type term = Term.term
type lit = term
type clause = Clause.clause

(* instead of renaming we use binding to distinguish
   from which term the variables came
   note that renaming destroys sharing *)

type bound_var = Var.bound_var
type bound_term = Term.bound_term
type bound_subst = SubstBound.bound_subst
type subst = Subst.subst

exception Orient_equal
exception Orient_func_terms
exception Unif_occur_check_fails
exception Unification_failed
exception Matching_failed
exception Subsumtion_failed

type bound_equation = bound_term * bound_term
type eq = bound_equation
type var_eq = bound_var * bound_term
type eq_list = eq list
type eq_stack = eq Stack.t

(* env is a map from var to terms
   we assume that we have total ordering on vars,
   extend it to the binded vars by lex order and extend
   to pairs (var, func. term) assuming that any var is
   greater than any func. term (func terms can be replaced by new constants)
   then each entry in the map can be seen as a rewrite rule
   and env to be a convergent terminating rewrite system :
   in particular
   if eq = (x, t) in env then there is no (x, s) in env, s\not = t
   we don't reduce right handsides, since after this occur check
   becomes non - local
 *)

(* orients a pair one of which is bterm of var and reterns
   (bvar, bterm) such that bavr is greater in the ordering than bterm
   raises Orient_equal is bt and bs are equal variables and
   raises Orient_func_terms if both bt, bs are function terms
   in orientation we first compare bindings!
 *)

(* we assume variables are oriented such that vars of type symb_type_types are bigger than other vars *)
(* so they will be eliminated during unification whenever possible *)

let compare_types tv sv =
  let tv_type = Var.get_type tv in
  let sv_type = Var.get_type sv in
  if tv_type == sv_type
  then
    0
  else
    if tv_type == Symbol.symb_type_types
    then 1
    else -1

exception Unif_type_check_failed

let check_types (_b,t) (_b,s) = 
  let t_type = Term.get_term_type t in 
  let s_type = Term.get_term_type s in
  (* variables of Symbol.symb_type_types can unify with anything *)
  if (t_type == s_type)
      || (t_type == Symbol.symb_type_types) || (s_type == Symbol.symb_type_types) 
      || (t_type == Symbol.symb_bot_type)   || (s_type == Symbol.symb_bot_type)
  then ()
  else
    (
     out_warning ("Unif faild for term: "^(Term.to_string t)^" type: "^(Symbol.to_string t_type)^" term "^(Term.to_string s)^(" type ")^(Symbol.to_string s_type)^"\n"); 
(*
    failwith ("Unif faild for term: "^(Term.to_string t)^" type: "^(Symbol.to_string t_type)^" term "^(Term.to_string s)^(" type ")^(Symbol.to_string s_type)^"\n"); 
*)
  (*   raise Unification_failed*)
     raise Unif_type_check_failed
    )
      
let orient_eq bt bs =
  check_types bt bs;
  match bt with
  | (b_t, Term.Var(tv, _)) ->
      let btv = (b_t, tv) in
      (
       match bs with
       | (b_s, Term.Var(sv, _)) ->
	   let bsv = (b_s, sv) in				
	   let cmp_types = compare_types tv sv in
	   if not (cmp_types = 0)
	   then
	     if cmp_types > 0 
	     then (btv, bs)
	     else (bsv, bt)
		 
	   else (* cmp_types = 0 *)
	     (
	      let comp = (Var.compare_bvar btv bsv) in
	      if comp > cequal 
	      then (btv, bs)
	      else if comp < cequal then (bsv, bt)
	      else raise Orient_equal
	     )
       | _ -> (btv, bs)
      )
	
  | (b_t, Term.Fun(_, _, _)) ->
      (
       match bs with
       | (b_s, Term.Var(sv, _)) ->
	   let bsv = (b_s, sv) in
	   (bsv, bt)
       | _ -> raise Orient_func_terms
      )

(*--------------Unification------------------------------------*)

(* tail-recursive on lists rather than Stack's*)

(* occur_check returns true if bv doesnot occur in trans. closure
   and false otherwise
   we assume that bx strictly greater than bs *)

(* separate pairs with at least one top var,  and non-var top terms *)
(* first to unify non-var top terms *)

type eqt_stack = 
    {
     mutable eqt_top_var : (bound_term *  bound_term) list;
     mutable eqt_top_non_var : (bound_term *  bound_term) list;       
   }

let eqt_stack_create () = 
  {
   eqt_top_var     = [];
   eqt_top_non_var = [];
 }


let eqt_stack_push eqt_stack (((bt,t), (bs,s)) as bpair) = 
(* first check if both are ground *)

  if ((Term.is_ground t) && (Term.is_ground s))
  then 
    if (t == s)
    then
      ()      
    else
      raise Unification_failed
  else

    if ((not (Term.is_var t)) && (not (Term.is_var s)))
    then 
      (
       eqt_stack.eqt_top_non_var <- bpair::(eqt_stack.eqt_top_non_var)
      )
    else
      (
       eqt_stack.eqt_top_var <- bpair::(eqt_stack.eqt_top_var)
      )

exception Eq_stack_is_empty

(* can raise Eq_stack_is_empty *)
let eqt_stack_pop eqt_stack = 
  match eqt_stack.eqt_top_non_var with 
  | bpair::tl -> 
      (
       eqt_stack.eqt_top_non_var <- tl;
       bpair
      )
  | [] -> 
      (
        match eqt_stack.eqt_top_var with 
        | bpair::tl -> 
            (
             eqt_stack.eqt_top_var <- tl;
             bpair
            )
        | [] -> 
            (raise Eq_stack_is_empty)
      )



let rec occur_check' bterm_stack (env : bound_subst) bx =
  match bterm_stack with
  | [] -> true
  | bs:: tl ->
      match bs with
      | (b, Term.Fun(_, args, _)) ->
	  let appl_to_args rest t = (b, t):: rest
	  in
	  let new_stack = Term.arg_fold_left appl_to_args tl args in
	  occur_check' new_stack env bx
      | (b, Term.Var(v, _)) ->
	  let bv = (b, v) in
	  if (Var.equal_bvar bx bv)
	  then false
	  else
	    let new_stack =
	      (try
		let new_bs = SubstBound.find bv env in
		new_bs:: tl
	      with
		Not_found -> tl
	      )
	    in
	    occur_check' new_stack env bx

let occur_check (env : bound_subst) ((bx, bs) : var_eq) =
  occur_check' [bs] env bx

(* we should not unify variables with functions which are obtained *)
(* as Non-eq to eq transformation see preprocess.ml *)

let is_funpred_term t =
  match t with
  | Term.Fun (t_sym, _, _) ->
      (match (Symbol.get_property t_sym) with
      | Symbol.FunPred -> true
      | _ -> false
      )
  | _ -> false

(* we cannot completely reduce vars on the righthandsides since *)
(* new pairs can reduce vars in the environment*)
(*returns env -- substitution with bindings or raises Unification_failed *)
(* the substitution is guarnteed to be such that  b_v v-> b_u u then*)
(* bv > b_u (where v,u are vars)*)

let rec unify_eqt_stack' (env_ref : bound_subst ref) eqt_stack =    
  let ((b_t, t), (b_s, s)) = eqt_stack_pop eqt_stack in 
  match t with
  | Term.Fun(t_sym, t_args, _) ->
      (
       match s with
       | Term.Fun(s_sym, s_args, _) ->
	   if (Symbol.equal t_sym s_sym)
	   then
             begin
               (* equality is polymorphic, but if we have different instantiated sorts then we first need to check *)
               (* that equality sorts are the same; *)
               (* otherwise we can try to unify  terms and a vars later which would be of different sorts *)
               (if (t_sym == Symbol.symb_typed_equality) 
               then
                 (let t_type_term_eq = List.hd (Term.arg_to_list t_args) in
                 let s_type_term_eq = List.hd (Term.arg_to_list s_args) in
                 if  
                   (Term.is_ground t_type_term_eq) &&  
                   (Term.is_ground s_type_term_eq) &&
                   (not (t_type_term_eq == s_type_term_eq))
                 then 
                   ( raise Unification_failed  )
                 )
               );               
	       let push_eq t' s' = eqt_stack_push eqt_stack ((b_t, t'), (b_s, s')) in
               Term.arg_iter2 push_eq t_args s_args;
	       unify_eqt_stack' env_ref eqt_stack
             end
	   else raise Unification_failed
       | _ ->
           ( 
             eqt_stack_push eqt_stack  ((b_s, s), (b_t, t));
	     unify_eqt_stack' env_ref eqt_stack
            )
      )
  | Term.Var(t_v, _) ->
      if (is_funpred_term s)
      then 
        raise Unification_failed
      else
	begin
	  if (b_t = b_s && t == s)
	  then (*(b_t,t) = (b_s,s))*)
	    (unify_eqt_stack' env_ref eqt_stack)
	  else
            begin
	      let (l, r) = orient_eq (b_t, t) (b_s, s) in
	      let new_env =
	        (try
		  (
                   let reduced_l = SubstBound.find l !env_ref in
                   eqt_stack_push eqt_stack (reduced_l, r);
		   !env_ref
                  )
	        with Not_found ->
		  if (occur_check !env_ref (l, r))
		  then
		  let new_env = SubstBound.add l r !env_ref in
		  new_env
		  else 
                    raise Unification_failed
	        )
	      in
              env_ref := new_env;
	      unify_eqt_stack' env_ref eqt_stack
            end
	end


let rec unify_eqt_stack (env : bound_subst) eqt_stack =    
  let env_ref = ref env in 
  try
    unify_eqt_stack' (env_ref : bound_subst ref) eqt_stack
  with 
    Eq_stack_is_empty ->  (*success*) !env_ref


let unify_bterms_eqt_stack bt bs =
  let eqt_stack = eqt_stack_create () in 
  eqt_stack_push eqt_stack (bt, bs);
  try
    unify_eqt_stack (SubstBound.create ()) eqt_stack
  with 
    Unif_type_check_failed -> 
      (
       out_warning ("Type check failed when unifying: "
                    ^(binded_to_string Term.to_string bt)^" "
                    ^(binded_to_string Term.to_string bs)
                    ^"\n"); 
       raise Unif_type_check_failed 
      )

let unify_beq_list_eqt_stack eq_list =
  let eqt_stack = eqt_stack_create () in 
  List.iter (eqt_stack_push eqt_stack) eq_list;
  unify_eqt_stack (SubstBound.create ()) eqt_stack
        

(*-------------old works but is replaced by unify_eqt_stack above which should be more  efficeint --------------*)

let rec unify_eq_stack (env : bound_subst) eq_stack =  
  match eq_stack with
  |[] -> (*success*) env
  | ((b_t, t), (b_s, s)) :: tl_stack ->
      match t with
      | Term.Fun(t_sym, t_args, _) ->
	  (
	   match s with
	   | Term.Fun(s_sym, s_args, _) ->
	       if (Symbol.equal t_sym s_sym)
	       then
                 begin
                 (* equality is polymorphic, but if we have different instantiated sorts then we first need to check *)
                 (* that equality sorts are the same; *)
                 (* otherwise we can try to unify  terms and a vars later which would be of different sorts *)
                 (if (t_sym == Symbol.symb_typed_equality) 
                 then
                   (let t_type_term_eq = List.hd (Term.arg_to_list t_args) in
                   let s_type_term_eq = List.hd (Term.arg_to_list s_args) in
                   if  
                     (Term.is_ground t_type_term_eq) &&  
                     (Term.is_ground s_type_term_eq) &&
                     (not (t_type_term_eq == s_type_term_eq))
                   then 
                     ( raise Unification_failed  )
                   )
                 );
                   
		   let push_eq rest t' s' = ((b_t, t'), (b_s, s')):: rest in
		   let new_stack = Term.arg_fold_left2
		       push_eq tl_stack t_args s_args in
		   unify_eq_stack env new_stack
                 end
	       else raise Unification_failed
	   | _ -> let new_stack = ((b_s, s), (b_t, t)):: tl_stack in
	     unify_eq_stack env new_stack
	  )
      | Term.Var(t_v, _) ->
	  if (is_funpred_term s)
	  then raise Unification_failed
	  else
	    begin
	      if (b_t = b_s && t == s)
	      then (*(b_t,t) = (b_s,s))*)
		unify_eq_stack env tl_stack
	      else
		let (l, r) = orient_eq (b_t, t) (b_s, s) in
		let (new_stack, new_env) =
		  (try
		    let reduced_l = SubstBound.find l env in
		    ((reduced_l, r):: tl_stack, env)
		  with Not_found ->
		    if (occur_check env (l, r))
		    then
		      let new_env = SubstBound.add l r env in
		      (tl_stack, new_env)
		    else raise Unification_failed
		  )
		in
		unify_eq_stack new_env new_stack
	    end



let unify_bterms_eq_stack bt bs =
  let eq_stack = [(bt, bs)] in	
  try
    unify_eq_stack (SubstBound.create ()) eq_stack
  with 
    Unif_type_check_failed -> 
      (
       out_warning ("Type check failed when unifying: "
                    ^(binded_to_string Term.to_string bt)^" "
                    ^(binded_to_string Term.to_string bs)
                    ^"\n"); 
       raise Unif_type_check_failed 
      )

let unify_beq_list_eq_stack eq_list =   
  unify_eq_stack (SubstBound.create ()) eq_list


(*--------------------end old------------------*)

let unify_bterms bt bs =
  unify_bterms_eqt_stack bt bs

let unify_beq_list eq_list =
  unify_beq_list_eqt_stack eq_list
  

(* to activate old unif version uncomment: *)

(*
let unify_bterms bt bs =
  unify_bterms_eq_stack bt bs

let unify_beq_list eq_list =
  unify_beq_list_eq_stack eq_list
*)



(*---------Not tested-------------------------------*)
(*      Unif subsitiution is a matching             *)
(* we use property that  the substitution           *)
(* is guarnteed to be such that  b_v v-> b_u u then *)
(* bv > b_u (where v,u are vars)                    *)
(* we have that high bind is matches the low bind   *)
(* for this we need just to check that low bind does not occur on the lefthandside*)

exception HBind_match_failed
let mgu_high_bind_is_matching b_high bsubst =
  let check (b_v, v) (b_t, t) =
    if b_v = b_high
    then ()
    else
      if b_v < b_high
      then
	raise HBind_match_failed
      else out_warning "mgu_high_bind_is_matching: b_high is not the highest!\n"
  in
  try
    SubstBound.iter check bsubst;
    true
  with
    HBind_match_failed -> false

(* for low bind to be matching we need *)
(*  (i)  check that high bind does not bind var with non_var term *)
(* (ii)  all high binds have different normal forms *)

module VKey =
  struct
    type t = bound_var
    let compare = Var.compare_bvar
  end

module VM = Map.Make (VKey)

exception LBind_match_failed

(* note that the argument should be the high binding not the low! *)
let mgu_low_bind_is_matching b_high bsubst =
  let current_normal_forms = ref VM.empty in
  let check bv bt_not_normal =
    let (b_v, v) = bv in
    if b_v = b_high
    then
      (let nf = (SubstBound.find_norm bv bsubst) in
      let (b_t, t) = nf in
      match t with
      | Term.Fun(_, _, _) -> raise LBind_match_failed
      | Term.Var(tv, _) ->
	  let btv = (b_t, tv) in
	  if (VM.mem btv !current_normal_forms)
	  then raise LBind_match_failed
	  else
	    current_normal_forms := VM.add btv btv !current_normal_forms
      )
    else
      if b_v < b_high
      then ()
      else out_warning "mgu_low_bind_is_matching: b_high is not the highest!\n"
  in
  try
    SubstBound.iter check bsubst;
    true
  with
    LBind_match_failed -> false

(*-----------------------Matching----------------------------------------------*)
(* matching: check if t matches s by a substitution
   extending subst, returns the resulting substitution
   here we implicitly treating t and s as renamed *)

(* tail-rec and  stack is impl as list *)
(* eq stack contains (t_i, s_i) terms to match  *)
let rec matches_eq_stack (subst : subst) eq_stack =
  match eq_stack with
  |[] -> subst
  | (t, s):: tl_stack ->
      (* simple test*)
      if (Term.get_num_of_symb t) <= (Term.get_num_of_symb s)
      then
	(match t with
	| Term.Fun(t_sym, t_args, _) ->
	    (
	     match s with
	     | Term.Fun(s_sym, s_args, _) ->
		 if (Symbol.equal t_sym s_sym)
		 then
		   let push_eq rest t' s' = (t', s'):: rest in
		   let new_stack = Term.arg_fold_left2
		       push_eq tl_stack t_args s_args in
		   matches_eq_stack subst new_stack
		 else raise Matching_failed
	     | _ -> raise Matching_failed
	    )
	| Term.Var(t_v, _) ->
	    if (is_funpred_term s)
	    then raise Matching_failed
	    else
	      begin
		
		let new_subst =
		  try
		    if (Term.compare s (Subst.find t_v subst)) = cequal
		    then
		      subst
		    else
		      raise Matching_failed
		  with
		    Not_found ->
		      Subst.add t_v s subst
		in
		matches_eq_stack new_subst tl_stack
	      end
	)
      else
	raise Matching_failed

(* check t matching s  with extending subst returns extened subst*)

let matches_subst t s subst =
  let eq_stack = [(t, s)] in
  matches_eq_stack subst eq_stack

let matches t s =
  matches_subst t s (Subst.create ())

(*----------------- Subsumption --------------------------*)

type occupied_lit = lit * bool ref

exception Find_match_failed

(* returns substitution and tail of the list that wasn't tried*)
let rec find_match_subst subst lit1 (list2_occup : occupied_lit list) =
  match list2_occup with
  | (lit2, occupied):: tl ->
      if not (!occupied)
      then
	try
	  let new_subst = matches_subst lit1 lit2 subst in
	  occupied:= true;
	  (new_subst, occupied, tl)
	with
	  Matching_failed ->
	    find_match_subst subst lit1 tl
      else find_match_subst subst lit1 tl
  |[] -> raise Find_match_failed

let rec subsumes_list subst lit_list1 list2_occup unexplored_part_of_list2 =
  match lit_list1 with
  | lit1:: tl ->
      (try
	let (new_subst, occupied, unexplored_rest) =
	  find_match_subst subst lit1 unexplored_part_of_list2 in
	(try
	  subsumes_list new_subst tl list2_occup list2_occup
	with
	  Subsumtion_failed ->
	    (if unexplored_rest != [] then
	      (occupied:= false;
	       subsumes_list subst lit_list1 list2_occup unexplored_rest
	      )
	    else raise Subsumtion_failed
	    )
	)
      with
	Find_match_failed -> raise Subsumtion_failed
      )
  |[] -> subst

let subsumes c1 c2 =
(*  check_disc_time_limit (); *)
  incr_int_stat 1 res_clause_to_clause_subsumption;
  (* out_str ("Try Subsumes: "^(Clause.to_string c1)^" \n "
     ^(Clause.to_string c2)^"\n");*)
  (* order large first *)
  
  let pos_order_fun () =
    Term.lit_cmp_type_list_to_lex_fun
      [Lit_Sign true; Lit_Num_of_Symb true; Lit_Num_of_Var false] in
  let order_lits_fun lits =
    List.sort (compose_sign false (pos_order_fun ())) lits
  in
  let c1_lit_list = order_lits_fun (Clause.get_literals c1) in
  let c2_lit_list = order_lits_fun (Clause.get_literals c2) in
  let c2_occup =
    List.map (fun lit -> (lit, ref false)) c2_lit_list in
  (* old
     try
     List.fold_left
     (fun subst lit1 -> find_match_subst subst lit1 c2_occup)
     (Subst.create ()) c1_lit_list
     with
     Find_match_failed -> raise Subsumtion_failed
   *)
  subsumes_list (Subst.create ()) c1_lit_list c2_occup c2_occup

(*-------------------------- Commneted

(*-----------Different implementations of unif and matching-------------------*)

(* works but non - tail rec because of exceptions...

(* occur_check returns true if bv doesnot occur in trans. closure
   and raise Unif_occur_check_fails otherwise
   we assume that bx strictly greater than bs *)

   let rec occur_check (env : bound_subst) ((bx, bs) : var_eq) =
   match bs with
   | (b, Term.Fun(_, args, _)) ->
   let appl_to_args prev t = (prev && (occur_check env (bx, (b, t)))) in
   Term.arg_fold_left appl_to_args true args
   | (b, Term.Var(v, _)) ->
   let bv = (b, v) in
   if (Var.equal_bvar bx bv)
   then (*false*)
   raise Unif_occur_check_fails
   else
   try
   let new_bs = SubstBound.find bv env in
   occur_check env (bx, new_bs)
   with
   Not_found -> true

(* we cannot completely reduce vars on the righthandsides since *)
(* new pairs can reduce vars in the environment*)
(*returns env -- substitution with bindings or raises Unification_failed *)
(* the substitution is guarnteed to be such that  b_v v-> b_u u then*)
(* bv > b_u (where v,u are vars)*)

   let rec unify_eq_stack (env : bound_subst) (eq_stack : eq_stack) =
   try
   let ((b_t, t), (b_s, s)) = Stack.pop eq_stack in
   match t with
   | Term.Fun(t_sym, t_args, _) ->
   (
   match s with
   | Term.Fun(s_sym, s_args, _) ->
   if (Symbol.equal t_sym s_sym)
   then
   let push_eq t' s' = Stack.push ((b_t, t'), (b_s, s')) eq_stack in
   let () = Term.arg_iter2 push_eq t_args s_args
   in unify_eq_stack env eq_stack
   else raise Unification_failed
   | _ -> let () = Stack.push ((b_s, s), (b_t, t)) eq_stack in
   unify_eq_stack env eq_stack
   )
   | Term.Var(t_v, _) ->
   try
   let (l, r) = orient_eq (b_t, t) (b_s, s) in
   try
   let reduced_l = SubstBound.find l env in
   Stack.push (reduced_l, r) eq_stack;
   unify_eq_stack env eq_stack
   with Not_found ->
   try
   let _ = occur_check env (l, r) in
   let new_env = SubstBound.add l r env in
   unify_eq_stack new_env eq_stack
   with Unif_occur_check_fails -> raise Unification_failed
(* if (occur_check env (l, r))
   then
   let new_env = SubstBound.add l r env in
   unify_eq_stack new_env eq_stack
   else raise Unification_failed *)
   with Orient_equal -> unify_eq_stack env eq_stack
   with Stack.Empty -> env

   let unify_bterms bt bs =
   let eq_stack = Stack.create () in
   let () = Stack.push (bt, bs) eq_stack in
   unify_eq_stack (SubstBound.create ()) eq_stack

 *)

(* checkes if bx occurs in bterm_stack *)
(* of initially non var bound terms w.r.t. env subst *)
(* Stack impl. tail recursive
   exception Occur_check_success
   exception Occur_check_fails
   let rec occur_check' bterm_stack (env : bound_subst) bx =
   let bs =
   try Stack.pop bterm_stack
   with Stack.Empty -> raise Occur_check_success
   in
   match bs with
   | (b, Term.Fun(_, args, _)) ->
   let appl_to_args t =
   Stack.push (b, t) bterm_stack
   in
   Term.arg_iter appl_to_args args;
   occur_check' bterm_stack env bx
   | (b, Term.Var(v, _)) ->
   let bv = (b, v) in
   if (Var.equal_bvar bx bv)
   then raise Occur_check_fails
   else
   ((try
   let new_bs = SubstBound.find bv env in
   Stack.push new_bs bterm_stack
   with
   Not_found -> ()
   );
   occur_check' bterm_stack env bx)

   let occur_check (env : bound_subst) ((bx, bs) : var_eq) =
   let bterm_stack = Stack.create () in
   Stack.push bs bterm_stack;
   try
   let () = occur_check' bterm_stack env bx in
   failwith "Unif.occur_check: should not happen\n"
   with
   | Occur_check_success -> true
   | Occur_check_fails -> false
 *)

(* list implementatin tail rec.*)
(*
  exception Occur_check_success
  exception Occur_check_fails
  let rec occur_check' bterm_stack (env : bound_subst) bx =
  match bterm_stack with
  | [] -> true
  | bs:: tl ->
  match bs with
  | (b, Term.Fun(_, args, _)) ->
  let appl_to_args rest t = (b, t):: rest
  in
  let new_stack = Term.arg_fold_left appl_to_args tl args in
  occur_check' new_stack env bx
  | (b, Term.Var(v, _)) ->
  let bv = (b, v) in
  if (Var.equal_bvar bx bv)
  then false
  else
  let new_stack =
  (try
  let new_bs = SubstBound.find bv env in
  new_bs:: tl
  with
  Not_found -> tl
  )
  in
  occur_check' new_stack env bx

  let occur_check (env : bound_subst) ((bx, bs) : var_eq) =
  occur_check' [bs] env bx
 *)

(*
  let rec occur_check (env : bound_subst) ((bx, bs) : var_eq) =
  match bs with
  | (b, Term.Fun(_, args, _)) ->
  let appl_to_args prev t = (prev && (occur_check env (bx, (b, t)))) in
  Term.arg_fold_left appl_to_args true args
  | (b, Term.Var(v, _)) ->
  let bv = (b, v) in
  if (Var.equal_bvar bx bv)
  then false
(*raise Unif_occur_check_fails  *)
  else
  try
  let new_bs = SubstBound.find bv env in
  occur_check env (bx, new_bs)
  with
  Not_found -> true
 *)

(* tail rec but Stacks make it ugly ....*)
(*
  let unify_eq_stack (env_ref : bound_subst ref) (eq_stack : eq_stack) =
  let fail = ref false in
  try
  while (not !fail)
  do
  let ((b_t, t), (b_s, s)) = Stack.pop eq_stack in
  match t with
  | Term.Fun(t_sym, t_args, _) ->
  (
  match s with
  | Term.Fun(s_sym, s_args, _) ->
  if (Symbol.equal t_sym s_sym)
  then
  let push_eq t' s' = Stack.push ((b_t, t'), (b_s, s')) eq_stack in
  Term.arg_iter2 push_eq t_args s_args
  else (fail := true) (*raise Unification_failed *)
  | _ ->
  Stack.push ((b_s, s), (b_t, t)) eq_stack
  )
  | Term.Var(t_v, _) ->
  try
  let (l, r) = orient_eq (b_t, t) (b_s, s) in
  try
  let reduced_l = SubstBound.find l !env_ref in
  Stack.push (reduced_l, r) eq_stack
  with Not_found ->
(* try
   out_str "occur_check before\n";
   let _ = occur_check !env_ref (l, r) in
   out_str "occur_check after\n";
   env_ref := SubstBound.add l r env in
   unify_eq_stack env_ref eq_stack
   with Unif_occur_check_fails -> raise Unification_failed *)
  ( (*out_str "occur_check before\n"; *)
  if (occur_check !env_ref (l, r))
  then
  (	     (* out_str "occur_check after\n";  *)
  env_ref := SubstBound.add l r !env_ref
  )
  else
  ( (*out_str "occur_check after\n";  *)
  fail:= true )(*raise Unification_failed*)
  )
  with Orient_equal -> ()
  done;
  if !(fail) then false
  else failwith "Unif.unify_eq_stack should not happen\n"
  with Stack.Empty -> true

  let unify_bterms bt bs =
  let eq_stack = Stack.create () in
  let () = Stack.push (bt, bs) eq_stack in
  let env_ref = ref (SubstBound.create ()) in
  if (unify_eq_stack env_ref eq_stack)
  then
  !env_ref
  else
  raise Unification_failed

 *)

(*-----------------------------------------------------------------------*)
(* matching: check if t matches s by a substitution
   extending subst, returns the resulting substitution
   here we implicitly treating t and s as renamed *)

(* works but not tail-rec and on Stack *)
(* eq stack contains (t_i, s_i) terms to match  *)
  let rec matches_eq_stack (subst : subst) eq_stack =
  try
  let (t, s) = Stack.pop eq_stack in
(* simple test*)
  if (Term.get_num_of_symb t) <= (Term.get_num_of_symb s)
  then
  (match t with
  | Term.Fun(t_sym, t_args, _) ->
  (
  match s with
  | Term.Fun(s_sym, s_args, _) ->
  if (Symbol.equal t_sym s_sym)
  then
  (let push_eq t' s' = Stack.push (t', s') eq_stack in
  Term.arg_iter2 push_eq t_args s_args;
  matches_eq_stack subst eq_stack)
  else raise Matching_failed
  | _ -> raise Matching_failed
  )
  | Term.Var(t_v, _) ->
  try
  if (Term.compare s (Subst.find t_v subst)) = cequal
  then
  matches_eq_stack subst eq_stack
  else
  raise Matching_failed
  with
  Not_found ->
  let new_subst = Subst.add t_v s subst in
  matches_eq_stack new_subst eq_stack
  )
  else
  raise Matching_failed
  with Stack.Empty -> subst

(* check t matching s  with extending subst returns extened subst*)

  let matches_subst t s subst =
  let eq_stack = Stack.create () in
  let () = Stack.push (t, s) eq_stack in
  matches_eq_stack subst eq_stack

  let matches t s =
  matches_subst t s (Subst.create ())
 *)
