(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2017 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.
   See LICENSE for the license terms.                                       *)
(*----------------------------------------------------------------------[C]-*)


open Lib 
open Options
open Logic_interface

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

let dbg_groups =
  [
   D_trace; 
 ]


let module_name = "def_discovery"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

(* currently only conj/disj definitions are covered  *)
(* definitions are of the form l -> [u_1,..,u_1] where l is a literal and (\forall x [l <-> u_1 &..& u_n ]) *)
(* implied literals are difinitions of the from l -> []; [] stands for T *)
(* if defintion is simple l1<-> l2 then both l1->[l2] and l2 -> [l1] will be in the map *)
(* it is possible that both lit and its compl have definitions; (unless one is implied) *)
(* def are wrt the current state of the solver + input clauses *)
(* TODO: several definitions of the same literal  *)

type def_map = (term list) list TMap.t

(* can rase Unsatisfiable_gr_na *)
type def_state = 
    {
     mutable def_map : def_map; 
     mutable def_atom_candidates : TSet.t; (* candidates of left-hand-sides of definitions *)
   }

let out_def_map def_map = 
  let def_list_to_str def_lits = 
    if def_lits = [] 
    then 
      "T"
    else
      (list_to_string Term.to_string def_lits "&")
  in
  let f lit def_lits_list =
    let g def_lits = 
      out_str ((Term.to_string lit)^"<->("^(def_list_to_str def_lits)^")");
    in 
    List.iter g def_lits_list
  in
  TMap.iter f def_map

let unsat_up lits = 
  match (Prop_solver_exchange.fast_solve ~solver_in:Prop_solver_exchange.solver_sim lits) with 
  | PropSolver.FUnsat -> true	         
  | PropSolver.FSat | PropSolver.FUnknown -> false

(* ds = def_state *)
let has_simple_def ds lit = 
  try 
    let def_lits = TMap.find lit ds.def_map in 
    match def_lits with 
    | [[]] -> (* |  [_] ->*) true  (* either implied or equiv to single lit *)
    |_-> false
  with 
   Not_found -> false 
        
let extend_def_state ?cmp ds lit =   
  let compl_lit = add_compl_lit lit in 
  if (has_simple_def ds compl_lit) (* do not exted if already compl has a simple def *)
  then 
    ()
  else 
    begin    
      try 
        let impl_lits = Implied_units.all_implied_lits lit in (* impl_lits exclude lit*)
        dbg D_trace (lazy ("lit: "^(Term.to_string lit)^" impl_lits: "^(Term.term_list_to_string impl_lits)));
        if (impl_lits != []) 
        then
          begin 
            try 
              let reduced_defs_compl_lit = minimise_list_enum ?cmp ~keep:(fun l -> l == compl_lit) ~test:unsat_up (compl_lit::impl_lits) in
              let reduced_defs = List.map (List.filter (fun l -> not (l == compl_lit))) reduced_defs_compl_lit in
              if (not (reduced_defs = []))
              then
                (
                 dbg D_trace (lazy ("def: "^(Term.to_string lit)
                                    ^" <-> ["
                                    ^(Lib.list_to_string Term.term_list_to_string reduced_defs " ]; [ ")^"]"));
                 ds.def_map <- TMap.add lit reduced_defs ds.def_map
                )
              else
                ()
            with 
              Not_found -> 
                dbg D_trace (lazy ("lit: "^(Term.to_string lit)^" reverse sat: no def"));
          end
        else
          ()
      with 
        Implied_units.Impl_Unit(impl_lit) ->  (* impl_lit is ether lit or compl_lit *)
          (
           ds.def_map <- TMap.add impl_lit [[]] ds.def_map;
          )
    end

let fill_def_state ?cmp ds = 
(* pos *)
  TSet.iter (extend_def_state ?cmp ds) ds.def_atom_candidates;

(* neg *)
  TSet.iter (fun atom -> extend_def_state ?cmp ds (add_neg_atom atom)) ds.def_atom_candidates


(* TODO: impl_lits_to_def_map def_state*)

(* cmp priority larger prioritised for right handsides of definitions; (smaller are eliminated first from defs) *)
let get_def_map ?cmp clause_list = 
  assert(Prop_solver_exchange.is_empty_assumptions ());
  List.iter Prop_solver_exchange.add_clause_to_solver clause_list;
  (if (Prop_solver_exchange.solve ()) = PropSolver.Unsat
  then
    raise Unsatisfiable_gr_na
  );

(* TODO: for fof make p(x1,..,x_n) for p in Pred(S) as atoms *)
  let all_atoms = Clause.get_atoms_clause_list clause_list in 
  
(* TODO: use all glb implied lits rather than newly *)
(* let top_implied_lits = Prop_sovler_exchange.get_all_newly_implied_lits ~is_relevant:(fun: _-> true) in  *)
  let glb_implied_lits = Prop_solver_exchange.get_all_impl_lits () in
  let glb_implied_atoms = TSet.map Term.get_atom glb_implied_lits in
  
(* deal with top impl lits separately *)  
  let atoms_of_top_impl_lits =TSet.inter glb_implied_atoms all_atoms in
  let top_impl_lits = 
    TSet.map 
      (fun atom -> 
        if (TSet.mem atom glb_implied_lits)
        then 
          atom 
        else
          (
           let neg_atom = add_neg_atom atom in
           assert (TSet.mem neg_atom glb_implied_lits);
           neg_atom
          )
      )
      atoms_of_top_impl_lits
  in
  let init_def_map = 
  TSet.fold (fun impl_lit rest_map -> TMap.add impl_lit [] rest_map) top_impl_lits TMap.empty
  in
(* consists of top_impl_lits -> [] *)
    
  let def_state = 
    {   
     def_map = init_def_map;
     def_atom_candidates = all_atoms;
(*
     def_implied_lits = top_impl_lits; 
     def_implied_atoms = atoms_of_top_impl_lits;      
*)
   }
  in
  fill_def_state ?cmp def_state;
  def_state.def_map



(*  let is_relevant_atom def_state atom = (not (TSet.mem atom def_state.def_implied_atoms)) in *)
  

(*---------------------  equivalence definitions  ---------*)
(* defs of the form a <-> (~)(b <-> c) *)

type eqiv_defs = term list list (* [a;b;c] include all 3 elements of the def *)

module TSetSet = Set.Make(TSet) (* set of term sets *)
module TSetMap = Map.Make(TSet) (* map from set of terms *)

type equiv_defs = (* eqd *)
    {
     mutable eqd_odd  : term list list; (* atom list *)
     mutable eqd_even : term list list; (* atom list *)
   }


let out_equiv_defs eqd = 
  let def_list_to_str even def_atoms = 
    match def_atoms with 
    |[a;b;c] -> 
        if even 
        then
          (out_str ((Term.to_string a)^"<->("^(Term.to_string b)^" <-> "^(Term.to_string c)^")");)
        else
          (out_str ((Term.to_string a)^"<->("^(Term.to_string b)^" <~> "^(Term.to_string c)^")");)
    | _ -> failwith "out_equiv_def: should be triple"
  in
  List.iter (def_list_to_str true)  eqd.eqd_even;
  List.iter (def_list_to_str false) eqd.eqd_odd
  

type pre_eqd_el  = 
    {
     mutable peqd_odd  : TSetSet.t; (* lit set consiting of all sequences with odd negs with the same atom base {(~)a;(~)b;(~)c} *)
     mutable peqd_even : TSetSet.t;    
   }

type pre_eqd = pre_eqd_el TSetMap.t (* map from atom base {a;b;c} *)
      
let get_pre_eqd clause_list = 
  let f pre_eqd clause = 
    if ((Clause.length clause) = 3)
    then
      let lits  = Clause.get_lits clause in
      let atoms = List.map Term.get_atom lits in
      let atom_set = TSet.of_list atoms in
      let lit_set  = TSet.of_list lits in
      let num_neg  = list_count_p Term.is_neg_lit lits in
      let is_even  = (num_neg mod 2) = 0 in
      let pre_eqd_el = 
        try 
          TSetMap.find atom_set pre_eqd 
        with 
          Not_found -> 
            {
             peqd_odd  = TSetSet.empty;
             peqd_even = TSetSet.empty;
           }
      in
      (if is_even 
      then
        (pre_eqd_el.peqd_even <- TSetSet.add lit_set pre_eqd_el.peqd_even)
      else
        (pre_eqd_el.peqd_odd <- TSetSet.add lit_set pre_eqd_el.peqd_odd)
      );
      TSetMap.add atom_set pre_eqd_el pre_eqd
    else
      pre_eqd
  in
  List.fold_left f TSetMap.empty clause_list
    
let get_equiv_defs clause_list = 
  let pre_eqd = get_pre_eqd clause_list in
  let eqd = 
    {eqd_odd = []; 
     eqd_even =[]}
  in
  let f atom_set pre_eqd =   
    assert(((TSetSet.cardinal pre_eqd.peqd_odd) <= 4) && ((TSetSet.cardinal pre_eqd.peqd_even) <= 4));
    if (TSetSet.cardinal pre_eqd.peqd_odd) = 4 
    then
     ( 
       eqd.eqd_odd <- (TSet.elements atom_set)::eqd.eqd_odd;
      )
    else
      if (TSetSet.cardinal pre_eqd.peqd_even) = 4
      then
        ( 
          eqd.eqd_even <- (TSet.elements atom_set)::eqd.eqd_even;
         )
      else
        ()
  in
  TSetMap.iter f pre_eqd;
  eqd
      

(*
type eq_defs = 
    {
     eq_dfs : TMap.t
     defs_even = 
     defs_odd  = 
   }
let eq_defs 
*)
