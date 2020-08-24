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

(* input clauses : unit propagate*)
exception Satisfiable 
exception Unsatisfiable 


module type PropStruct = 
  sig
    type var
    type lit 
    type clause = lit list 
    val pos_lit : lit -> bool
    val get_var : lit -> var
    val compare_var : var -> var -> int
    val var_to_string : var -> string
	(*  val compare_lit : lit -> lit -> int
	    val get_num_lit : clause -> int
	    val iter_clause : (lit -> unit) -> clause -> unit
	    val find_lit    : (lit -> bool) -> clause -> lit
	 *)
  end

module type DPLL = 
  sig
(*    type var 
      type lit *)
    type clause 
    type state
    val create_init_state : unit -> state
(* returns *)
    val dpll : state -> clause list -> unit
  end

module Make(PropStruct:PropStruct) = 
  struct
    type var      =  PropStruct.var
    type lit      =  PropStruct.lit
    type clause   =  PropStruct.clause
    let get_var   = PropStruct.get_var
    let compare_var = PropStruct.compare_var
    let pos_lit     = PropStruct.pos_lit
(* use later 
   module VarSetElm =     
   struct
   type t = var
   let compare =  PropStruct.compare_var
   end

   module VarSet = Set.Make(VarSetElm)
 *)
    type decision_status = Decision | Implied
    type polarity = Pos | Neg
    type clause_ext = 
	{
	 mutable lit_list : lit_ext list;
	 mutable num_of_lit : int;
	 mutable num_of_true_lit  : int;
	 mutable num_of_false_lit : int
       }	 
    and lit_ext = {polarity : polarity; var_ext : var_ext} 
    and var_ext = 
	{
	 var : var;
	 mutable assignment : bool param;
	 mutable is_flipped : bool;
(*	 mutable splitting_priority : int; currently not used*)
	 mutable var_decision_level : int param;
	 mutable decision_status    : decision_status param;
	 mutable pos_occur    : clause_ext list;
	 mutable neg_occur    : clause_ext list;
	 mutable implied_vars : var_ext list   ;
(* later might change to conflict clause_ext *)
	 mutable var_conflict_lit_list : (lit_ext list) param
       }

    type state = 
	{
	 mutable var_list        : var_ext list; (*VarSet.t;*)
	 mutable clause_list     : clause_ext list;
	 mutable decision_level  : int;          
	 mutable decision_var    : var_ext param;
	 mutable decision_stack  : var_ext Stack.t;
(* later might change to conflict clause_ext *)
	 mutable conflict_lit_list : (lit_ext list) param;
(* some new clauses are units (w.r.t. current state) *)
	 mutable init_units      : clause_ext list
       }

    let create_free_var var =
      { 
	var                = var;
        assignment         = Undef;
        is_flipped         = false;
        var_decision_level = Undef; 
	decision_status    = Undef; 
        pos_occur          = [];
        neg_occur          = [];
        implied_vars       = [];
	var_conflict_lit_list  = Undef
      }
	
    let create_empty_clause () = 
      {	
        lit_list = []; 
        num_of_lit = 0;
        num_of_true_lit = 0; 
        num_of_false_lit = 0;
      }

    let create_init_state () = 
      {
       var_list         = []; (*VarSet.empty;*)
       clause_list      = [];
       decision_level   = 0; 
       decision_var     = Undef;
       decision_stack   = Stack.create ();
       conflict_lit_list  = Undef;
       init_units       = []    
     }

    let param_to_str val_to_string param = 
      match param with 
      |Def(v) -> val_to_string v
      |Undef  -> "Undef" 
	    
    let decison_status_to_str = function 
	Implied -> "Implied"
      |Decision -> "Decision"

    let var_to_str_long var_ext =
      " Var:"
      ^(PropStruct.var_to_string var_ext.var) 
      ^" assignment:"^(param_to_str string_of_bool var_ext.assignment)
      ^" is_flipped:"^(string_of_bool var_ext.is_flipped) 
      ^" decision_level:"^(param_to_str string_of_int var_ext.var_decision_level)
      ^" decision_status:"^(param_to_str decison_status_to_str var_ext.decision_status ) 
      ^"\n"  

    let lit_to_str_long lit= 
      let pol_str =  
	if lit.polarity = Pos 
	then ""
	else "-"
      in pol_str^(var_to_str_long lit.var_ext)
		    

    let clause_to_str_long clause =
      "["^(list_to_string lit_to_str_long clause.lit_list ",")^"]\n" 
								  
    let get_param p =
      match p with 
      | Def(v) -> v
      |_-> failwith "get_param: param undef"
	    
    let get_decision_var state = 
      match state.decision_var with 
      |Def(var) -> var
      |_-> failwith "dpll: get_decision_var"

    let get_assingment var = 
      match var.assignment with 
      |Def(a) -> a
      |_-> failwith "dpll: get_assingment"

    let is_free var_ext =
      if (var_ext.assignment = Undef) 
      then true 
      else false 

    let is_sat clause_ext = 
      if (clause_ext.num_of_true_lit > 0) 
      then true 
      else false 

    let is_unit clause_ext = 
      if ((not (is_sat clause_ext)) && 
	  (clause_ext.num_of_lit - clause_ext.num_of_false_lit = 1))
      then true 
      else false
	  
    let is_conflict clause_ext =
      if clause_ext.num_of_lit = clause_ext.num_of_false_lit
      then true
      else false


    let add_clause state clause = 
      let clause_ext = create_empty_clause () in
      let add_lit lit = 
	let var = get_var lit in
	let equal_to_var var_ext = 
	  if (compare_var var var_ext.var)=0 then true else false in      
	let var_ext =   
	  try 
	    List.find equal_to_var state.var_list 
	  with 
	    Not_found -> 
	      (let new_var_ext = create_free_var var in
	      state.var_list <- new_var_ext::state.var_list;
	      new_var_ext )
	in 
	clause_ext.num_of_lit <- clause_ext.num_of_lit+1;
	if (pos_lit lit)
	then 
          (var_ext.pos_occur <- clause_ext::var_ext.pos_occur; 
	   clause_ext.lit_list <- 
	     ({var_ext =var_ext; polarity = Pos })::clause_ext.lit_list;
	   match var_ext.assignment with
	   |Def(true) -> 
	       clause_ext.num_of_true_lit <- clause_ext.num_of_true_lit+1 
           |Def(false) ->   
	       clause_ext.num_of_false_lit <- clause_ext.num_of_false_lit+1 
	   |_->()
	  )
	else (* neg lit*)
	  (var_ext.neg_occur <- clause_ext::var_ext.neg_occur; 
	   clause_ext.lit_list <- 
	     ({var_ext =var_ext; polarity = Neg })::clause_ext.lit_list;
	   match var_ext.assignment with
	   |Def(true) -> 
	       clause_ext.num_of_false_lit <- clause_ext.num_of_false_lit+1 
           |Def(false) ->   
	       clause_ext.num_of_true_lit <- clause_ext.num_of_true_lit+1 
	   |_->()
	  )
      in     
      List.iter add_lit clause;
      (if (is_conflict clause_ext)   
      then raise Unsatisfiable
      else 
	(if (is_unit clause_ext) 
	then state.init_units <- clause_ext::state.init_units)
      );
      state.clause_list <- clause_ext::state.clause_list
					 (* out_str (clause_to_str_long clause_ext)*)


    let add_clause_list state clause_list = 
      List.iter (add_clause state) clause_list
	


    let num_of_unsat_with_var var = 
      let add_unsat rest clause =
	if (is_sat clause) then rest else rest + 1 in 
      match var.assignment with 
      |Undef -> 
	  (List.fold_left add_unsat 0 var.pos_occur) + 
	    (List.fold_left add_unsat 0 var.neg_occur)                 
      |Def(true)  -> (List.fold_left add_unsat 0 var.neg_occur)
      |Def(false) -> (List.fold_left add_unsat 0 var.pos_occur)


    let make_next_split state =    
      let cmp v1 v2 = 
	compare (num_of_unsat_with_var v1) (num_of_unsat_with_var v2) in      
      let split_var = 
	(try (list_find_max_element_p is_free cmp state.var_list)
	with Not_found -> 
	  (*out_str "\n make_next_split: not found\n"; *)
	  raise Satisfiable )
      in
      let add_unsat rest clause =
	if (is_sat clause) then rest else rest + 1 in 
      let pos_unsat = List.fold_left add_unsat 0 split_var.pos_occur in 
      let neg_unsat = List.fold_left add_unsat 0 split_var.neg_occur in 
      if (pos_unsat = 0 && neg_unsat = 0 )
      then raise Satisfiable (* since we choose var with max unsat*) 
      else  
	(
	 state.decision_var <- Def(split_var);
	 split_var.var_decision_level <- Def(state.decision_level);
	 split_var.decision_status <- Def(Decision);
	 Stack.push split_var state.decision_stack; 
	 (if pos_unsat > neg_unsat 
	 then split_var.assignment <- Def(true)
	 else split_var.assignment <- Def(false));
	 out_str 
	   (" Decision Level: "^(string_of_int state.decision_level)^"\n"
	    ^"Decision_var:"^(var_to_str_long split_var)^"\n")
	)

    let rec free_var var =
      var.is_flipped <- false;
      var.decision_status <- Undef;  
      var.var_decision_level <- Undef;    
      let (sat_occur,unsat_occur) = 
	match var.assignment with
	|Def(true)  -> (var.pos_occur,var.neg_occur)
	|Def(false) -> (var.neg_occur,var.pos_occur)
	|_          -> failwith "dpll: free var ass "
      in	
      let dec_true_lit clause =
	clause.num_of_true_lit <- clause.num_of_true_lit - 1 in
      List.iter dec_true_lit sat_occur;
      let dec_false_lit clause =
	clause.num_of_false_lit <- clause.num_of_false_lit - 1 in
      List.iter dec_false_lit unsat_occur;
      var.assignment <- Undef;	 
      List.iter free_var var.implied_vars;
      var.implied_vars <- [];
      var.var_conflict_lit_list <- Undef

(*flips the var and changes state.decision_level to this var.var_decision_level
  assign conflict lits from state to this var *)
	  
    let flip_var state var = 
      if (not var.is_flipped)
      then
	match var.assignment with
	|Def(bv)-> 
	    (
	     state.decision_level <- (get_param var.var_decision_level);	   
	     free_var var;
	     var.var_decision_level <- Def(state.decision_level);
	     var.assignment <- Def(not bv);
	     var.is_flipped <- true;
	     var.var_conflict_lit_list <- state.conflict_lit_list;
	     state.decision_var <- Def(var)	    
	    )
	|_-> failwith "dpll: flip_var ass undef"
      else
	failwith "dpll: flip_var var already flipped"
	  
(* later change to backjumping using state.conflict_clause*)

    exception Backtrack
	
    let rec backtrack state = 
      (*out_str "Start Backtrack\n";*)
      try  
	let var = Stack.pop state.decision_stack in  
	if var.is_flipped 
	then 
	  (free_var var;
	   backtrack state)
	else	  
	  (flip_var state var;
	   Stack.push var state.decision_stack)
      with Stack.Empty -> raise Unsatisfiable
	  
(* resolve by level: C D results in all lit in C\up D 
   with decision level less than  level
   since resolv only conflics we assume no free vars in c1 c2*)

    let resolve lit_list1 lit_list2 level = 
      let less_level lit = 
	(get_param lit.var_ext.var_decision_level) < level in
      let r1 = List.filter less_level lit_list1 in
      let r2 = List.filter less_level lit_list2 in
      r1@r2
	    
    let get_max_level lit_list = 
      let cmp lit1 lit2 = 
	compare  (get_param lit1.var_ext.var_decision_level) 
	  (get_param lit2.var_ext.var_decision_level) 
      in
      let max_lit = list_find_max_element cmp lit_list in
      get_param max_lit.var_ext.var_decision_level


    let rec free_to_level state level =
      try 
	let top = Stack.top state.decision_stack in
	if get_param top.var_decision_level > level
	then 
	  let var = Stack.pop state.decision_stack in
	  free_var var;
	  free_to_level state level
	else
	  state.decision_level <- (get_param top.var_decision_level)
      with Stack.Empty -> raise Unsatisfiable
	  
(* not correct.... do later 

   exception Backjump 

   let rec backjump state = 
   try   
   let var = Stack.top state.decision_stack in  
   state.decision_level <- (get_param var.var_decision_level);
   if var.is_flipped 
   then 
   (	
   let var_conflict =  get_param var.var_conflict_lit_list in
   let state_conflict = get_param state.conflict_lit_list in
   let new_conflict =  
   resolve var_conflict state_conflict state.decision_level in
   out_str 
   ("Decision Level: "^(string_of_int state.decision_level)^"\n"
   ^"Var_conflict: "^(list_to_string lit_to_str_long var_conflict "," )^"\n"
   ^"State_conflict: "
   ^(list_to_string lit_to_str_long state_conflict "," )^"\n");
   (if new_conflict = [] then raise Unsatisfiable);
   state.conflict_lit_list <- Def(new_conflict);

   let new_level = analyse_conflict state in
   free_to_level state new_level;
   backjump state
   )
   else	  
   flip_var state var
   with Stack.Empty -> raise Unsatisfiable
 *)	  
	  
    let rec deduce state var = 
      let (sat_occur,unsat_occur) = 
	match var.assignment with
	|Def(true)  -> (var.pos_occur,var.neg_occur)
	|Def(false) -> (var.neg_occur,var.pos_occur)
	|_          -> failwith "dpll: deduce var ass "
      in
      let incr_true_lit clause =
	clause.num_of_true_lit <- clause.num_of_true_lit + 1 in
      List.iter incr_true_lit sat_occur;
      let incr_false_lit clause =
	clause.num_of_false_lit <- clause.num_of_false_lit + 1 in
      List.iter incr_false_lit unsat_occur;
(*incr_false_lit separated from check_impl beckause when backtrack 
  we would need to remember what clauses were incr. and what not *)
      let check_impl clause =
	if (is_conflict clause)
	then 
	  (state.conflict_lit_list <- Def(clause.lit_list);
	   raise Backtrack)
	else
	  (if (is_unit clause) 
	  then  unit_propagate state clause)	    
      in
      List.iter check_impl unsat_occur
    and
	
	unit_propagate state clause =
      
      let is_free_lit lit = 
	is_free lit.var_ext in
      let free_lit = 
	try 
	  List.find is_free_lit clause.lit_list 
	with Not_found -> failwith "unit propagate: not unit"
      in
      let var = free_lit.var_ext in
      let decision_var = get_decision_var state in   
      decision_var.implied_vars  <- 
	var::decision_var.implied_vars;
      var.var_decision_level <- Def(state.decision_level);
      var.decision_status <- Def(Implied);
      out_str 
	("\n Unit Pr: "^(clause_to_str_long clause)^"\n"
	 ^"On Lit:"^(lit_to_str_long free_lit)^"\n"); 

      match free_lit.polarity with 
      |Pos ->
	  (var.assignment <- Def(true);
	   deduce state var)
      |Neg -> 
	  (var.assignment <- Def(false);
	   deduce state var)
	    
	    
    let dpll_loop state =
      try 
(*	while true 
  do  
 *)
	make_next_split state;
	(*out_str 
	  ("Nex split Var: "
	  ^(var_to_str_long 
	  (get_decision_var state))
	  ^"Assignment: "
	  ^(string_of_bool (get_assingment (get_decision_var state)))^"\n");*)
	while true  
	do
	  try	    
	    deduce state (get_decision_var state);	   
	    state.decision_level <- state.decision_level + 1;	 
	    make_next_split state;
	    (*    out_str ("Nex split Var: "
		  ^(var_to_str_long 
		  (get_decision_var state))
		  ^"Assignment: "
		  ^(string_of_bool (get_assingment (get_decision_var state)))^"\n")*)
	  with Backtrack -> backtrack state (* state is changed on backtrack*)
	done
(*	done*)
      with 
      |Satisfiable -> 
	  out_str 
	    ("Sat Assignment: \n"
	     ^(list_to_string var_to_str_long state.var_list "\n"));
	  raise Satisfiable
      |Unsatisfiable -> raise Unsatisfiable 
	    
	    
    let dpll state clause_list = 
      add_clause_list state clause_list;      
(* cannot unit popagate initial clauses yet...
   problem with the finding the decision var which caused the unit 

   let init_unit_propagate unit_cl = 
   if (is_unit unit_cl) then 
   unit_propagate state unit_cl
   else 
   if (is_conflict unit_cl) 
   then raise Unsatisfiable 
   in
   List.iter (unit_propagate state) state.init_units;	
   state.init_units <- [];    
 *)  
      dpll_loop state
	
  end
    
