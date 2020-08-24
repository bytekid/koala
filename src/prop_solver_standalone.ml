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

type lit = PropSolver.lit


(*- read from stdin -*)
(* create an incremental solver (if true simplification solver is created) *)

let solver     = PropSolver.create_solver false 

type i_lit = int
type clause = int list

(* PropSolver.create_lit solver PropSolver.Pos var_id*)


let get_sign i_l = 
  if i_l> 0
  then
    PropSolver.Pos
  else
    if i_l=0
    then
      failwith "lit should not be equal to 0"
    else 
      PropSolver.Neg

let create_lit sign var_id = 
  PropSolver.add_var_solver solver var_id; 
  PropSolver.create_lit solver sign var_id

let add_clause i_c = 
  let lit_list = 
    List.map 
      (fun l ->
	let var_id = abs l in
        create_lit (get_sign l) var_id
      ) i_c  
  in        
  out_str ((PropSolver.lit_list_to_string solver lit_list)^"\n");
  PropSolver.add_clause solver lit_list

let read_clauses () =
  let current_clause = ref [] in
  let clause_list = ref [] in
  try
    while true do
      let str = read_line () in
      if (String.length str = 0)
      then ()
      else
	(
	 if (str.[0] = 'c' || str.[0] ='p'|| str.[0] ='%') 
	 then ()
	 else
	   let str_list = Str.split (Str.regexp " ") str in
	   let l_list = List.map (fun s -> int_of_string s) str_list in
	   
	   let rec fill_str list = 
	     match list with 
	     |h::tl -> 
		 if h = 0 
		 then 
		   (
		    assert (list_non_empty !current_clause);
		    clause_list := (!current_clause)::(!clause_list);
		    current_clause := [];
		    fill_str tl
		   )
		 else
		   (
		    current_clause:=h::(!current_clause);
		    fill_str tl
		   )
	     |[] -> ()
	   in
	   fill_str l_list
	)
    done;
    !clause_list
  with 
    End_of_file ->      
      (
       if (list_non_empty !current_clause)
       then
	 (
	  clause_list := (!current_clause)::(!clause_list);
	  current_clause := [];
	  !clause_list
	 )
       else
	 !clause_list
      )
	   

let out_all_unit_clauses ~ass solver = 
  out_str ("---- unit clauses ass "^(string_of_bool ass)^":");
  (try 
    while true 
    do
      let unit_lit = 
        if ass 
        then 
          PropSolver.get_next_ass_implied_unit solver 
        else
          PropSolver.get_next_implied_unit solver 
      in 
      out_str (PropSolver.lit_to_string solver unit_lit); 
    done
  with 
    Not_found -> ()
  );
  out_str "---- end unit clauses"




let () = 
  let c_list = read_clauses () in 
  try
    List.iter (fun c -> add_clause c) c_list;
    match  (PropSolver.solve solver) 
    with 
    |PropSolver.Sat   -> 
        out_all_unit_clauses ~ass:false solver;
        out_str "------ dbg -------\n\n";
        let ln7 = create_lit PropSolver.Neg 7 in
        let ln8 = create_lit PropSolver.Neg 8 in
(*        add_clause [-7]; *)
          
(*        ignore(PropSolver.solve_assumptions solver [ln7]); *)
        ignore(PropSolver.fast_solve solver [ln7]);
        out_all_unit_clauses ~ass:true solver;
(*        ignore(PropSolver.solve solver); *)
        ignore(PropSolver.fast_solve solver [ln8]);
        out_all_unit_clauses ~ass:true solver;
        out_str "SATISFIABLE"
    |PropSolver.Unsat -> 
        out_str "UNSATISFIABLE"
  with 
    Unsatisfiable_gr_na -> 
      out_str "UNSATISFIABLE"
	
