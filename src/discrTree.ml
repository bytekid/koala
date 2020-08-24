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








(* discrimination tree *)

open Lib
open Logic_interface

exception Empty_elem_in_disc_tree


type sym_or_var = Sym of symbol | Var


let init_num_of_kes_bound = 2 (*11*)

exception Not_in_discr_tree

module type Param = 
  sig
    val num_of_symb : int
  end

module type DiscrTree =
  sig   
    type 'a index 
    val create   : unit -> 'a index
    val mem      : term -> 'a index -> bool 
    val find          : term -> 'a index -> 'a ref_elem
    val add_term_path : term -> ('a index) ref -> 'a ref_elem 
    val remove_term_path : term -> ('a index) ref -> unit
    val remove_term_path_ret : term -> ('a index) ref -> 'a ref_elem
(* removes grounding path*)
(*    val remove_grounding_path : term -> grounding_term -> 
      ('a index) ref -> 'a list *)
    val unif_candidates : ('a index) -> term -> 'a list
    val unif_cand_exists : 'a index -> term -> bool 
    val iter_elem     : ('a ref_elem -> unit) -> 'a index -> unit
(*only for debug*)
(*    val get_key_list : term -> sym_or_var list *)
  end

module Make (P:Param) =
  struct    
    module Key =
      struct
	type t = sym_or_var
              
	let equal t s = 
	  match (t,s) with 
	  | (Sym(_),Var)   -> false
	  | (Var,Sym(_))   -> false 
	  | (Var,Var) -> true
	  | (Sym(s1),Sym(s2)) -> 
	      if (Symbol.compare s1 s2)=cequal then true 
	      else false  
		  
 	let hash t = 
	  match t with 
	  | Sym(s) -> (Symbol.hash s) + 1 (* >= 1 *)
	  | Var -> 0

        let init_num_of_keys = 
	  min (P.num_of_symb + 1) init_num_of_kes_bound
      end

    module DTM =  Trie.Make (Key)
    type 'a index = 'a DTM.trie

    let  create () = DTM.create ()

(* works but slow because of many append 
   let rec get_key_list term  =
   match term with
   | Term.Fun(sym,args,_) ->
   let f list t = List.append list (get_key_list t)
   in Sym(sym)::(Term.arg_fold_left f [] args)
   | Term.Var(_,_) ->
   [Var]
 *)

(* auxilary for get_key_list *)
    let rec get_key_list' rest term  =
      match term with
      | Term.Fun(sym,args,_) ->
	  Term.arg_fold_left get_key_list' (Sym(sym)::rest) args
      | Term.Var(_,_) ->
          Var::rest

    let get_key_list term =
      List.rev (get_key_list' [] term)

    let mem term index = DTM.mem (get_key_list term) index  

    let find term index = DTM.find (get_key_list term) index 

    let iter_elem f index = DTM.iter_elem f index

(* works 
   let add_term_path term ref_index = 
   DTM.add_path (get_key_list term) ref_index 
 *)
(*debug*)
    let add_term_path term ref_index =
      (*     out_str "Key List before\n"; *)
      let  key_list = (get_key_list term) in 
(*     out_str "Key List After\n";
       out_str ("Key length: "^(string_of_int (List.length key_list)));*)
      DTM.add_path key_list ref_index 

    let remove_term_path term ref_index = 
      try
	DTM.remove_path (get_key_list term) ref_index
      with 
	DTM.Trie_remove_path_too_long 
      |DTM.Trie_remove_path_too_short
      |DTM.Trie_remove_remove_from_emptytrie
      |DTM.Not_in_tree  -> raise Not_in_discr_tree


    let remove_term_path_ret term ref_index = 
      try
	DTM.remove_path_ret (get_key_list term) ref_index
      with 
	DTM.Trie_remove_path_too_long 
      |DTM.Trie_remove_path_too_short
      |DTM.Trie_remove_remove_from_emptytrie
      |DTM.Not_in_tree  -> raise Not_in_discr_tree


    exception Skip_error 
	
    let rec unif_candidates' candis_ref index skip term_list = 
      (* let key_list = get_key_list term in*)
      if skip = 0 then 
	match term_list with 
	| Term.Fun(sym,args,_)::tl ->
	    (try 
	      (*     let next_trie_fun_node =  in*)
	      unif_candidates' candis_ref 
		(DTM.get_subtrie (Sym(sym))  index)  
		skip ((Term.arg_to_list args)@tl)
	    with Not_found -> ());	       
	    (try             
	      unif_candidates' candis_ref 
		(DTM.get_subtrie Var  index) skip tl
	    with Not_found -> ()
	    )		       
	| Term.Var(v,_)::tl ->  	
	    unif_candidates' candis_ref index 1 tl

	| [] -> 
	    (match !(DTM.get_from_leaf index) with
	    |Elem(elem) -> candis_ref := elem::!candis_ref
	    |_ -> raise Empty_elem_in_disc_tree
	    )    
      else 
	if skip > 0 then 
	  let f key_sym trie = 
            (match key_sym with 
	    |Sym(s) -> 
		(unif_candidates' candis_ref 
		   trie (skip-1+(Symbol.get_arity s)) term_list)
		  
	    |Var -> 
		(unif_candidates' candis_ref 
		   trie (skip-1) term_list)
	    )	
	  in	
	  DTM.iter_level0 f index  
	else raise Skip_error 
	    
	    
    let unif_candidates index term = 
      if  DTM.is_empty index then [] 
      else	
	let candis_ref = ref [] in 
	unif_candidates' candis_ref index 0 [term];
	!candis_ref

(*--------unif_cand_exists' checks whether there is a unif candidate in the index-------------------------*)	
(*-----raises Found if unif candidate is found otherwise returns unit----*)

    exception Found

    let rec unif_cand_exists' index skip term_list = 
      (* let key_list = get_key_list term in *)
      begin
	if skip = 0 then 
	  match term_list with 
	  |Term.Fun(sym,args,_)::tl ->
	      ( 
		try 
		  unif_cand_exists' 
		    (DTM.get_subtrie (Sym(sym)) index)
		    skip ((Term.arg_to_list args)@tl)		  
		with Not_found -> ());	       
	      (try	       
		(
		 unif_cand_exists'  
		   (DTM.get_subtrie Var index) skip tl
		)
	      with Not_found -> ()
	      )
	 	
	  | Term.Var(v,_)::tl ->  	
	      unif_cand_exists' index 1 tl
		
	  | [] -> 
	      (match !(DTM.get_from_leaf index) with
	      |Elem _elem_list -> 
		  raise Found
		    (* candis_ref := (List.rev_append elem_list !candis_ref)*)
	      |Empty_Elem ->  
		  raise Found 
		    (* we allow empty element, in some cases index is needed to *)
                    (* check unif candidates without storing actual elements *)
                    (*raise Empty_elem_in_disc_tree*)
	      )    
	else 
	  if skip > 0 then 
	    let f key_sym trie = 
	      (match key_sym with 
	      |Sym(s) -> 
		  (unif_cand_exists' 
		     trie (skip-1+(Symbol.get_arity s)) term_list)
		    
	      |Var -> 
		  (unif_cand_exists'
		     trie (skip-1) term_list)
	      )	
	    in	
	    DTM.iter_level0 f index  
	  else raise Skip_error 
      end

    let unif_cand_exists index term =
      try  
	(unif_cand_exists' index 0 [term]);
	false
      with 
      |Found -> true
      |Not_found -> failwith "unif_cand_exists should not happen"


(* TO FINISH *)	  	  
(*    let remove_grounding_path' index_ref grounding_term term_list =
      match term_list with 
      | Term.Fun(sym,args,_)::tl ->
      let candis1 = 
      (try             
      unif_candidates' 
      (DTM.get_subtrie (Sym(sym))  index) 
      skip ((Term.arg_to_list args)@tl)
      with Not_found -> []
      ) 
 *)       
  end 




(*---------------------Commented

(*  pure functional version *)

  let rec unif_candidates' index skip term_list = 
  (* let key_list = get_key_list term in*)
  if skip = 0 then 
  match term_list with 
  | Term.Fun(sym,args,_)::tl ->
  let candis1 = 
  (try             
  unif_candidates' 
  (DTM.get_subtrie (Sym(sym))  index) 
  skip ((Term.arg_to_list args)@tl)
  with Not_found -> []
  ) 
  and candis2 =
  (try             
  unif_candidates' 
  (DTM.get_subtrie Var  index) skip tl
  with Not_found -> []
  ) in
  candis1@candis2
  
  | Term.Var(v,_)::tl ->  	
  unif_candidates' index 1 tl
  | [] -> 
  (match !(DTM.get_from_leaf index) with
  |Elem(elem_list) -> elem_list
  |_ -> raise Empty_elem_in_disc_tree
  )    
  else 
  if skip > 0 then 
  let f key_sym trie rest = 
  (match key_sym with 
  |Sym(s) -> 
  (unif_candidates' trie (skip-1+(Symbol.get_arity s)) term_list)@rest
  
  |Var -> 
  (unif_candidates' trie (skip-1) term_list)@rest
  )	
  in	
  DTM.fold_level0 f index []  
  else raise Skip_error 
  



 *)
