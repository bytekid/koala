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
open Parser_types 


type var = Var.var
type clause = Clause.clause

let input_clauses_ref         = ref []
let input_neg_conjectures_ref = ref []


type parsed_var = string
(*association*)
type var_map = (parsed_var*var) list 

(*to avoid passing max var as parameter to functions we assume global max_var*)

let e_prover_parsing_success = ref false

let max_var_ref   = ref (Var.get_first_var()) 
let symbol_db_ref = ref (SymbolDB.create_name "All_Symbols_DB")
let term_db_ref   = ref (TermDB.create_name "All_Terms_DB")

let () = Statistics.assign_fun_stat 
    (fun () -> TermDB.size !term_db_ref) Statistics.num_of_terms

let () = Statistics.assign_fun_stat 
    (fun () -> SymbolDB.size !symbol_db_ref) Statistics.num_of_symbols


(*
let clause_db_ref = ref (ClauseAssignDB.create_name "All_Clauses_DB")
*)



let bot_term = TermDB.add_ref (Term.create_fun_term Symbol.symb_bot []) term_db_ref
let top_term = TermDB.add_ref (Term.create_fun_term Symbol.symb_top []) term_db_ref


let current_is_neg_conjecture = ref false

(* is_negative is not needed*)
let rec is_negative = function
  |UnaryFormula(Negation,formula)
    -> bool_plus true (is_negative formula)
  |_-> false 
      
let rec get_list_of_literals parsed_formula = 
  match parsed_formula with
  |BinaryFormula(binary_connective,formula1,formula2) ->
      if binary_connective = Or then 
	(get_list_of_literals formula1)@(get_list_of_literals formula2)
      else failwith 
	  "Some input formula is not in CNF: some binary connective is not |"
  | Atom(atom) -> 
      (match atom with  
      | TheoryTerm(NegEquality(t1,t2)) -> 
	  [UnaryFormula(Negation,Atom(TheoryTerm(Equality(t1,t2))))]    
(* remove false*)
      | TheoryTerm(False) -> []    
      |_-> [parsed_formula]
      )
  | UnaryFormula(Negation,formula) ->
     ( match formula with 
      |Atom(atom) -> 
          (match atom with 
	  |TheoryTerm(NegEquality(t1,t2)) -> 
	      [Atom(TheoryTerm(Equality(t1,t2)))] 
(* remove false *)
	  |TheoryTerm(True) -> []
	  |_-> [parsed_formula]
	  ) 
      |_-> failwith "Some input formula is not in CNF:" 
      ) 	    
  |QuantifiedFormula(_,_,_) ->
      failwith "CNF formula should be without quantifiers 
	(all variables are implicitly universally quantifiered)"
	

let rec parsed_term_to_term var_map_ref symbol_type = function 
  |TheoryTerm(theory_term) -> 
      theory_term_to_term var_map_ref symbol_type theory_term
  |UserTerm(user_term) ->  
      user_term_to_term var_map_ref symbol_type user_term
  |Var(parsed_var) -> 
      (try 
	Term.create_var_term (List.assoc parsed_var !var_map_ref)
      with
	Not_found -> 
          let new_var = !max_var_ref in 
          max_var_ref := Var.get_next_var !max_var_ref;
 	  var_map_ref:=(parsed_var,new_var)::!var_map_ref;
	  Term.create_var_term new_var
      )  

and theory_term_to_term var_map_ref symbol_type = function 
  |Equality(parsed_term1, parsed_term2) -> 
      Symbol.assign_is_input true Symbol.symb_equality;
      Symbol.incr_num_input_occur Symbol.symb_equality;
      Term.create_fun_term Symbol.symb_equality 
	[(parsed_term_to_term var_map_ref Symbol.Fun parsed_term1); 
	 (parsed_term_to_term var_map_ref Symbol.Fun parsed_term2)]
	(* NegEquality is eliminated before*)
  |True ->   
      Symbol.assign_is_input true Symbol.symb_true;
      Symbol.incr_num_input_occur Symbol.symb_true;
      (Term.create_fun_term Symbol.symb_true [])
  |False ->  
      Symbol.assign_is_input true Symbol.symb_false;
      Symbol.incr_num_input_occur Symbol.symb_false;
      (Term.create_fun_term Symbol.symb_false [])
(* numbers as constants no theory treatment, can be added infuture*)
  |PositiveInteger (int)->  
      let int_symb = 
	(SymbolDB.add_ref 
	   (Symbol.create_from_str_arity 
	      (string_of_int int) Symbol.Fun 0) symbol_db_ref) in
      Symbol.assign_is_input true int_symb;
      Symbol.incr_num_input_occur int_symb;
      Term.create_fun_term int_symb []
  |RealNumber(int1,int2)->
      let real_str = (string_of_int int1)^"."^(string_of_int int2) in 
      let real_symb = 
	SymbolDB.add_ref 
	  (Symbol.create_from_str_arity real_str  Symbol.Fun 0) 
	  symbol_db_ref in
      Symbol.assign_is_input true real_symb;
      Symbol.incr_num_input_occur real_symb;
      Term.create_fun_term real_symb []
  |Plus(parsed_term1, parsed_term2)->
      Symbol.assign_is_input true Symbol.symb_plus;
      Symbol.incr_num_input_occur Symbol.symb_plus;
      Term.create_fun_term Symbol.symb_plus 
	[(parsed_term_to_term var_map_ref Symbol.Fun parsed_term1); 
	 (parsed_term_to_term var_map_ref Symbol.Fun parsed_term2)]
	
  |Minus(parsed_term1, parsed_term2)->
      Symbol.assign_is_input true Symbol.symb_minus;
      Symbol.incr_num_input_occur Symbol.symb_minus;
      Term.create_fun_term Symbol.symb_minus
	[(parsed_term_to_term var_map_ref Symbol.Fun parsed_term1); 
	 (parsed_term_to_term var_map_ref Symbol.Fun parsed_term2)]
  |UnaryMinus(parsed_term) ->
      Symbol.assign_is_input true Symbol.symb_unaryminus;
      Symbol.incr_num_input_occur Symbol.symb_unaryminus;
      Term.create_fun_term Symbol.symb_unaryminus
	[(parsed_term_to_term var_map_ref Symbol.Fun parsed_term)]

  |NegEquality(_,_)-> 
      failwith "strange error: NegEquality should of been eliminated" 	
          (* NegEquality is eliminated before*)	

and user_term_to_term var_map_ref symbol_type = function
  |Fun(parsed_symbol,parsed_term_list) ->
      (let symb = 
	SymbolDB.add_ref 
	  (Symbol.create_from_str_arity 
	     parsed_symbol symbol_type (List.length parsed_term_list)) 
	  symbol_db_ref in
      Symbol.assign_is_input true symb;
      Symbol.incr_num_input_occur symb;
      (if !current_is_neg_conjecture then
	Symbol.set_bool_param 
	  true Symbol.is_conj_symb symb);
     (* out_str ("Symb: "
	       ^(Symbol.to_string symb)
	       ^" is conj symb: "
	       ^ (string_of_bool
		    (Symbol.get_bool_param Symbol.is_conj_symb symb ))^"\n");*)
      let args = 
	list_map_left (parsed_term_to_term var_map_ref Symbol.Fun) 
	  parsed_term_list in 
      Term.create_fun_term symb args
      )     
	
   
let rec parsed_literal_to_literal var_map_ref = function 
  |Atom(atom) -> 
      parsed_term_to_term var_map_ref Symbol.Pred atom
  |UnaryFormula(Negation,formula) -> 
(* here formula can be only Atom(...)*)  
      Symbol.assign_is_input true Symbol.symb_neg;
      Symbol.incr_num_input_occur Symbol.symb_neg;
      (Term.create_fun_term Symbol.symb_neg
	 [(parsed_literal_to_literal var_map_ref formula)])
  |_ -> failwith 
	"parsed_literals_to_literals -- this shouldnot happen"

(* in list_of_literals_to_clauses
   clauses here are not normalised and 
   therefore terms are not added to db but symbols are
*)
	
let list_of_literals_to_clauses list_of_literals = 
  let var_map_ref = ref [] in 
  Clause.create 
    (list_map_left 
       (parsed_literal_to_literal var_map_ref) list_of_literals  
    )


(*let _ =  out_str "\n !!!!!!!!Uncomment!!!!!!! \n 
          input_clauses_ref := new_clause::!input_clauses_ref;
        in parsed_input_to_db.ml  \n "
*)
let cnf_formula_to_db parsed_formula =  
  let clause_tmp = 
    list_of_literals_to_clauses (get_list_of_literals parsed_formula) in 
  let new_clause = (Clause.normalise term_db_ref clause_tmp) in
  Clause.assign_input_history new_clause;
  input_clauses_ref := new_clause::!input_clauses_ref;
  new_clause
    
(*
  ClauseAssignDB.add_ref 
    (Clause.normalise clause_tmp term_db_ref) clause_db_ref
*)






let parsed_input_to_db input_list = 
  let conj_list = ref [] in

(* non_conj_list can be too big so we do not keep non_conj_list  with a bit of overhead of adding conjecture clauses twice *)


  let non_conj_list = ref [] in

(* we need to separate conjectures and add them first *)
(* to have correct has_conj_symb *)
  let rec f list = 
    match list with 	
    |Formula(CNF,name,formula_type,parsed_formula,
	     formula_annotation_list)::tl -> 	 
	       (incr_int_stat 1 num_of_input_clauses;
		match formula_type with 
		|UserType(Negated_conjecture) -> 
		    conj_list:= parsed_formula::!conj_list;
		   incr_int_stat 1 num_of_input_neg_conjectures;
		    f tl   
		|_ -> 
		    non_conj_list:= parsed_formula::!non_conj_list; 
		    f tl
	       )
    |Formula(FOF,_,_,_,_)::tl -> 
	failwith "The input should be translated into cnf format, or a path to E prover specified, see options --eprover_path and --fof" 
(*    |Formula(_,_,_,_,_)::tl -> 
	failwith "This language is not supported yet try to transfer to CNF" *)
    |Include(_,_)::_ -> failwith "should be no includes here..."
    |Comment(_)::tl  ->  f tl
    |CommentEprover(str)::tl ->

	f tl
    |Annotation(_)::tl  -> f tl
    |[] -> ()
  in
  let () = f input_list in
(* conjecture part *)
  current_is_neg_conjecture := true;
  let f_conj_param formula = 
    let clause = cnf_formula_to_db formula in
    Clause.assign_conjecture_distance 
      Clause.conjecture_int clause;
    input_neg_conjectures_ref:= clause::!input_neg_conjectures_ref
  in
 (* let conj_cnf = *)
  List.iter f_conj_param (!conj_list); (* in*)
  current_is_neg_conjecture := false;
(* end conjecture part *)
(*  let non_conj_cnf = *)
  List.iter (fun p -> let _ = cnf_formula_to_db p in ())  (!non_conj_list) 
(*  conj_cnf@non_conj_cnf*)
      


(*------------debug version -------*)
let parsed_input_to_db_debug input_list =
  let f formula = 
    match formula with 	
    |Formula(CNF,name,formula_type,parsed_formula,
	     formula_annotation_list) -> 	 
	       (incr_int_stat 1 num_of_input_clauses;
		match formula_type with 
		|UserType(Negated_conjecture) -> 		   
		    incr_int_stat 1 num_of_input_neg_conjectures;
		   ignore (cnf_formula_to_db parsed_formula);
		   
		|_ -> 
		   ignore (cnf_formula_to_db parsed_formula);
	       )
    |Formula(FOF,_,_,_,_) -> 
	failwith "The input should be translated into cnf format, or a path to E prover specified, see options --eprover_path and --fof" 
(*    |Formula(_,_,_,_,_)::tl -> 
	failwith "This language is not supported yet try to transfer to CNF" *)
    |Include(_,_) -> failwith "should be no includes here..."
    |Comment(_)  ->  () 
    |CommentEprover(_str) -> ()
    |Annotation(_) -> ()
  in
  List.iter f input_list 

      

(*--------------Commented--------------------*)
(*!!!!! sort that neg_conj first!!!!!!!1! *)
(* old works but need conjectures to be parsed first*)
(*
let rec parsed_input_to_db = function 
  |Formula(CNF,name,formula_type,parsed_formula,
	   formula_annotation_list)::tl -> 	    
	     let clause =
	       (match formula_type with 
	     |UserType(Negated_conjecture) -> 
		 (current_is_neg_conjecture := true;
		  let clause = cnf_formula_to_db parsed_formula in		
		  Clause.assign_conjecture_distance 
		    Clause.conjecture_int clause;
	          current_is_neg_conjecture := false;
		  clause)	   
	     |_ ->  
		 (let clause = cnf_formula_to_db parsed_formula in
		 Clause.assign_conjecture_distance 
		   Clause.max_conjecture_dist clause; 
		 clause)
	       ) in
	     clause::(parsed_input_to_db tl)
  |Formula(_,_,_,_,_) :: tl -> 
      failwith "This language is not supported yet try to transfer to CNF" 
  |Include(_,_)::_ -> failwith "should be no includes here..."
  |Comment(_)::tl  -> (parsed_input_to_db tl)
  |Annotation(_)::tl  -> (parsed_input_to_db tl)
  |[] -> []
*)


(*  List.iter top_element_to_db parsed_input *)
    
    

(*
(* theory symbols *)              
let neg_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "~" Symbol.Neg 1) symbol_db_ref
let () = Symbol.assign_is_input false neg_symb 

let true_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "true" Symbol.True 0) symbol_db_ref
let () = Symbol.assign_is_input false true_symb

let false_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "false" Symbol.False 0) symbol_db_ref
let () = Symbol.assign_is_input false false_symb

let equality_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "equal" Symbol.Equality 2) symbol_db_ref
let () = Symbol.assign_is_input false equality_symb

let plus_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "+" Symbol.Plus 2) symbol_db_ref
let () = Symbol.assign_is_input false plus_symb

let minus_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "-" Symbol.Minus 2) symbol_db_ref
let () = Symbol.assign_is_input false minus_symb

(* unary minus should be different since name is a key (it can be changed in future)*)
let unary_minus_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "-u" Symbol.UnaryMinus 1) symbol_db_ref
let () = Symbol.assign_is_input false unary_minus_symb

let bot_symb = 
  SymbolDB.add_ref 
    (Symbol.create_from_str_arity "bot" Symbol.Bot 0) symbol_db_ref
let () = Symbol.assign_is_input false bot_symb
*)
