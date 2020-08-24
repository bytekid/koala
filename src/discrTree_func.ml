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

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace
  | D_add
  | D_cnds

let dbg_gr_to_str = function 
  | D_trace -> "trace"
  | D_add -> "add" 
  | D_cnds -> "cnds"

let dbg_groups =
  [
   D_trace;
   D_add;
   D_cnds;
 ]

let module_name = "discrTree_func"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)



exception Empty_elem_in_disc_tree
exception Not_in_discr_tree

type sym_or_var = Sym of symbol | Var

module Key =
  struct
    type t = sym_or_var 

    let compare (t:t) (s:t) =
      match (t,s) with 
      | (Sym(_), Var)   -> cless
      | (Var, Sym (_))   -> cgreater 
      | (Sym(s1),Sym(s2))  -> Symbol.compare s1 s2
      | (Var,Var) -> cequal         
  end
    

module DTM =  Trie_func.Make (Key)
type 'a index = ('a ref_elem) DTM.trie
      
let  create () = DTM.create ()


(* auxilary for get_key_list *)
let rec get_key_list' rest term  =
  match term with
  | Term.Fun(sym,args,_) ->
      Term.arg_fold_left get_key_list' (Sym(sym)::rest) args
  | Term.Var(_,_) ->
      Var::rest

let get_key_list term =
  List.rev (get_key_list' [] term)

(*-------------*)

let mem term index = DTM.mem (get_key_list term) index  
    
let find term index = DTM.find (get_key_list term) index 

let iter_elem f index = DTM.iter_elem f index 


(*------ add -------*)

let add_term_path term ref_index =
  let key_list = (get_key_list term) in 
  try 
    DTM.find key_list !ref_index
  with 
    Not_found -> 
      (
       let new_elem = ref Empty_Elem in 
       ref_index := DTM.add key_list new_elem !ref_index; 
       new_elem
      )


let remove_term_path term ref_index = 
  try
    ref_index := DTM.remove (get_key_list term) !ref_index
  with 
    Trie_func.Trie_remove_path_too_long 
  |Trie_func.Trie_remove_path_too_short
  |Trie_func.Trie_remove_remove_from_emptytrie
  (* |DTM.Not_in_tree *) 
    -> raise Not_in_discr_tree


let remove_term_path_ret term ref_index = 
  let elem = find term !ref_index in
  remove_term_path term ref_index;
  elem


exception Skip_error 
	
let rec unif_candidates' candis_ref index skip term_list = 
  (* let key_list = get_key_list term in*)
  if skip = 0 then 
    match term_list with 
    | Term.Fun(sym,args,_)::tl ->
	(try 
	  (*     let next_trie_fun_node =  in*)
	  unif_candidates' candis_ref 
	    (DTM.get_subtrie (Sym(sym)) index)  
	    skip ((Term.arg_to_list args)@tl)
	with Not_found -> ());	       
	(try             
	  unif_candidates' candis_ref 
		(DTM.get_subtrie Var index) skip tl
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
  if DTM.is_empty index then [] 
  else	
    (
    let candis_ref = ref [] in 
    unif_candidates' candis_ref index 0 [term];
    !candis_ref
    )



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


(*------------------ OLD --------------------*)

(*
type term   = Term.term
type symbol = Symbol.symbol
type var    = Var.var
type sym_or_var = Sym of symbol | Var of var
    
module Key =
  struct
    type t = sym_or_var
          
    let compare (t:t) (s:t) =
      match (t,s) with 
      | (Sym(_),Var(_))   -> cless
      | (Var(_),Sym(_))   -> cgreater 
      | (Sym(s1),Sym(s2))  -> Symbol.compare s1 s2
      | (Var(v1),Var(v2)) -> Var.compare v1 v2

  end
    (*   
	 module type DiscrTree = 
	 sig
	 type index 
(*only for debug*)
	 type sym_or_var = Sym of Symbol.symbol | Var of var  
	 val get_key_list : term -> sym_or_var list
	 end
     *)
(* module DiscrTree = *)
    
module IndexM  =  Trie.Make (Key)
type 'a index = Empty|Not of 'a
    
    
let rec get_key_list term  = 
  match term with 
  | Term.Fun(sym,args,_) -> 
      let f list t = List.append list (get_key_list t)
      in Sym(sym)::(Term.arg_fold_left f [] args)
  | Term.Var(v) -> 
      [Var(v)]  

let create () = Empty
let add term  index  = index
let remove term index = index 

    
(************old
	     module Make (IndexData : UnifIndex.IndexData)=
	     struct 
	     type indexData = IndexData.t  
	     module IndexM  =  
	     type index = Empty|Not
	     
(* var is grater than sym, 
   so in traversal we first visit sym then var*)   

	     let compare_sym_var t s =
	     match (t,s) with 
	     | (Sym(_),Var(_))   -> cless
	     | (Var(_),Sym(_))   -> cgreater 
	     | (Sym(s1),Sym(s2))  -> Symbol.compare s1 s2
	     | (Var(v1),Var(v2)) -> Var.compare v1 v2
	     

	     

(* to be cont....  *)	    
(*    type unif_result *)
	     let create () = Empty
	     let add  term index  = index
	     let remove term  index = index 
(*    val unify  : term -> index -> unif_result *)
	     
	     end
 ************old*)
*)
