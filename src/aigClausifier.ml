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


open AigCommon
open Lib
open Bmc1Common (* for helpers for creating theory *)
open Logic_interface
open Statistics
open Options

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_elapsed
  | D_create
  | D_trace
  | D_latch
  | D_stat
  | D_cone
  | D_input_var
  | D_latch_non_const
let dbg_gr_to_str = function
  | D_elapsed -> "elapsed"
  | D_create -> "create"
  | D_trace -> "trace"
  | D_latch -> "latch"
  | D_stat -> "statistics"
  | D_cone -> "cone"
  | D_input_var -> "input_var"
  | D_latch_non_const -> "non-const latch"
let dbg_groups =
  [
(*
    D_elapsed;
    (* D_latch; *)
    D_stat;
    D_cone;
*)
   D_input_var;
  D_latch_non_const;
 ]

let module_name = "aig_clausifier"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


(*-------------------------------------------------*)
(* elapsed time code *)
(*-------------------------------------------------*)

(* keep the time *)
let last_timestamp = ref 0.0

(* set the timestamp *)
let timestamp () = last_timestamp := Unix.gettimeofday ()

(* helper: print the elapsed time, keep the time stamp *)
let elapsed_helper status =
  (* current time *)
  let current = Unix.gettimeofday () in
  (* report *)
  out_str (Format.sprintf "AIG:Timer report: %s: elapsed time %.3fs" status (current -. !last_timestamp));
  (* return current time *)
  current

(* print the elapsed time, keep the time stamp *)
let elapsed status = ignore (elapsed_helper status)

(* print the elapsed time, reset timer *)
let elapsed_ts status = last_timestamp := (elapsed_helper status)

(*----------------------------------------------------------------*)
(* map between main var of AND or LATCH and corresponding clauses *)
(*----------------------------------------------------------------*)

(* aig var into set of clauses that define it: complete *)
(* for ANDs and only $$init clauses for latches *)
let aig2clauses_ref = ref IntMap.empty
(* maps latch var into the $$next clauses *)
let latch2clauses_ref = ref IntMap.empty
(* clauses for the outputs *)
let output_clauses_ref = ref []
(* outputs themselves *)
let outputs_ref = ref []

(* latch var into next index const *)
let latch_consts_ref = ref IntMap.empty
(* next index const into latch var symbol *)
let consts_vars_map_ref = ref TMap.empty
(* next index const into latch var index *)
let latch2var_ref = ref TMap.empty

(* next index const into set of clauses from cone *)
let latch_cone_ref = ref TMap.empty

(* cone for the output *)
let output_cone_ref = ref []

(* use the same const Cj for both NEXT and INIT clauses *)
let latch_const_ref = ref None

(* input vars as a set *)
let input_vars_ref = ref SSet.empty

(* input vars as a list *)
let input_vars_list_ref = ref []

(* return true is symb is an input var symbol *)
let aig_is_input_var symb =
  SSet.mem symb !input_vars_ref

(* return true is lit is an input var predicate *)
let aig_is_input_pred lit =
  aig_is_input_var (Term.get_top_symb (Term.get_atom lit))

(* latch vars as a set *)
let latch_vars_ref = ref SSet.empty

(* return true is symb is an latch var symbol *)
let aig_is_latch_var symb =
  SSet.mem symb !latch_vars_ref

(* return true is lit is an latch var predicate *)
let aig_is_latch_pred lit =
  aig_is_latch_var (Term.get_top_symb (Term.get_atom lit))

(*----------------------------------------------------------------*)
(* Load the AIG problem into the prover *)
(*----------------------------------------------------------------*)

let clausify_aig problem =
  dbg D_trace (lazy ("start clausifier"));
  (* state type *)
  let state_type = Symbol.symb_ver_state_type in
  (* current state *)
  let var_curr = term_x0 state_type in
  (* next state *)
  let var_next = term_x1 state_type in
  (* constB0 -- need for grounding *)
  let constB0 = create_state_term 0 in
  (* negate atom *)
  let neg atom = add_compl_lit atom in
  (* $property(x0) *)
  let property_atom = create_property_atom var_curr in

  (*-----------------*)
  (* names machinery *)
  (*-----------------*)

  (* map from vars to symbols *)
  let var_symbol_ref = ref IntMap.empty in

  (* symbol v_i *)
  let v_i_symbol idx =
    try
      IntMap.find idx !var_symbol_ref
    with Not_found ->
      (* get a string "v_i" by an index idx *)
      let str_v_i = Format.sprintf "v_%d" idx in
      (* type of a symbol *)
      let stype = Symbol.create_stype [state_type] Symbol.symb_bool_type in
      (* create a symbol with an appropriate name *)
      let symbol = create_symbol str_v_i stype in
      (* record it in the map *)
      var_symbol_ref := IntMap.add idx symbol !var_symbol_ref;
      (* return that symbol *)
      symbol
  in
  (* get a string "v_i" by an index idx *)
  let v_i_name idx = Symbol.get_name (v_i_symbol idx) in
  (* term v_i(var) *)
  let v_i idx var = add_fun_term (v_i_symbol idx) [var] in
  (* {~}v_i(var) by the AIG literal *)
  let l_i lit var =
    (* lit = 0/1 = false/true*)
    if lit = 0
    then term_false ()
    else if lit = 1
    then term_true ()
    else begin
      (* var index *)
      let idx = lit/2 in
      (* var atom *)
      let atom = v_i idx var in
      (* negate if necessary *)
      if lit mod 2 = 0
      then atom
      else neg atom
    end
  in
  (* v_i(x0) *)
  let v_cur lit = l_i lit var_curr in
  (* v_i(x1) *)
  let v_next lit = l_i lit var_next in
  (* TSTP source FIXME!! for now *)
  let tstp_source = Clause.TSTP_inference_record (Clause.TSTP_bmc1_init_or_property_axiom, []) in
  (* make a normal clause out of literals *)
  let cl lits =
    (* make normal clause *)
    let clause = create_clause tstp_source lits in
    (* debug *)
    dbg D_create (lazy ("normal clause "^(Clause.to_string clause)));
    (* return clause *)
    clause
  in
  (* make a negated conjecture out of literals *)
  let nc lits =
    (* make negated conjecture *)
    let clause = Clause.create_neg_conjecture term_db_ref tstp_source lits in
    (* debug *)
    dbg D_create (lazy ("negated conjecture "^(Clause.to_string clause)));
    (* return clause *)
    clause
  in
  (*----------------------------------------------------------------*)
  (* clauses for AND *)
  (*----------------------------------------------------------------*)
  (* a = b & c is clausified as {~a,b}, {~a,c} and {a,~b,~c} *)
  let clauses_for_and conj =
    (* define vars *)
    let a = v_cur conj.lhs in
    let b = v_cur conj.rhs0 in
    let c = v_cur conj.rhs1 in
    (* define negs *)
    let neg_a = neg a in
    (* make clauses *)
    let clauses =
    [
      cl [ a; (neg b); (neg c) ];
      cl [ neg_a; c ];
      cl [ neg_a; b ];
    ]
    in
    (* save clauses in the map *)
    aig2clauses_ref := IntMap.add conj.lhs clauses !aig2clauses_ref;
    (* return those clauses *)
    clauses
  in
  let skip_and = ref 0 in
  (* clausification of AND *)
  let clausify_and accum conj =
    if conj.in_use
    then (clauses_for_and conj) @ accum
    else (skip_and := succ !skip_and; accum)
  in
  (* process ands, add them to TAIL *)
  let process_ands tail =
    dbg D_trace (lazy ("generate and clauses"));
    let tail_length = List.length tail in
    let new_clauses = List.fold_left clausify_and tail problem.ands in
    dbg_env D_elapsed (fun () -> (elapsed_ts "process_ands"));
    let new_length = (List.length new_clauses) - tail_length in
    dbg D_stat (lazy ("ands translated into "^(string_of_int new_length)^" clauses"));
    dbg D_stat (lazy ("AIG: skip "^(string_of_int !skip_and)^" ands"));
    new_clauses
  in

  (*----------------------------------------------------------------*)
  (* latch clauses: here l_c = latch current = latch.lit, *)
  (* l_n = latch next = latch.next, l_r = latch reset = latch.reset *)
  (*----------------------------------------------------------------*)

  (* literals for {$init,[~]l_c} clause to have bi-imp of init (BMC1 case) *)
  let init_to_lits = ref [] in
  (* clauses of the form {$init(Cj),[~]lj_c} to have bi-imp of init (UCM case) *)
  let init_to_clauses = ref [] in
  (* determine whether we beed bi-imp for init *)
  let need_init_biimp () =
    false
  in

  (* init clause for latch: {~$init,[~]l_c} *)
  let init_latch l_c l_r =
    dbg D_latch (lazy ("init_latch "^(string_of_int l_c)^" "^(string_of_int l_r)));
    (* MULTIPRED!! ~$init(x0) and $init(x0) should be the same*)
    let init_lit =
      match !latch_const_ref with
      | None -> (* no const defined by transition; generate new const *)
        out_str ("AIGWARNING: no transition for init latch "^(string_of_int l_c));
        create_auto_init_atom var_curr
      | Some const -> (* reuse const *)
        latch_const_ref := None;
        create_init_atom const var_curr
    in
    let neg_init_lit = neg init_lit in
    (* save Cj->l_c map for cones *)
    let cj = List.hd (Term.arg_to_list (Term.get_args init_lit)) in
    let symb = v_i_symbol (l_c/2) in
    consts_vars_map_ref := TMap.add cj symb !consts_vars_map_ref;
    (* create latch atom *)
    let latch_atom = v_cur l_c in
    (* negate if necessary *)
    let latch_lit =
      if l_r = 0
      then neg latch_atom
      else latch_atom
    in
    
    (* create a clause *)
    let init_clause = cl [ neg_init_lit; latch_lit ] in
    if need_init_biimp ()
    then (
      if !current_options.bmc1_ucm
      then (
        (* create inverted clause *)
        let inv_clause = cl [ init_lit; (neg latch_lit) ] in
        (* save that clause to use later *)
        init_to_clauses := inv_clause::!init_to_clauses;
        (* save both clause in the map (for cones) *)
        aig2clauses_ref := IntMap.add l_c [init_clause; inv_clause] !aig2clauses_ref;
      )
      else (* add negation of latch_lit to a list of init_to lits *)
        init_to_lits := (neg latch_lit)::!init_to_lits;
    )
    else
      (* save single clause in the map (for cones) *)
      aig2clauses_ref := IntMap.add l_c [init_clause] !aig2clauses_ref;

    (* return the clause *)
    init_clause
  in
  (* support method: save const Cj from $$next(Cj,s,s') into map *)
  let map_latch next_lit l_c =
    (* extract Cj *)
    let atom = Term.get_atom next_lit in
    let args = Term.arg_to_list (Term.get_args atom) in
    assert (3 = List.length args);
    let cj = List.hd args in
    (* save cj to use in init *)
    latch_const_ref := Some cj;
    (* map cj to v_i *)
    let symb = v_i_symbol (l_c/2) in
    consts_vars_map_ref := TMap.add cj symb !consts_vars_map_ref;
    latch2var_ref := TMap.add cj l_c !latch2var_ref;
    (* map l_c to cj *)
    latch_consts_ref := IntMap.add l_c cj !latch_consts_ref
  in
  (* const clause for latch: {[~]l_c} *)
  let const_latch l_c l_n =
    dbg D_latch (lazy ("const_latch "^(string_of_int l_c)^" "^(string_of_int l_n)));
    (* create latch atom *)
    let latch_atom = v_cur l_c in
    (* negate if necessary *)
    let latch_lit =
      if l_n = 0
      then neg latch_atom
      else latch_atom
    in
    (* create a clause *)
    cl [ latch_lit ]
  in
  (* half latch clause: {~$next(c,n),[~]l_c(n)}, for the case l_n = 0/1 *)
  let half_latch l_c l_n =
    dbg D_latch (lazy ("half_latch "^(string_of_int l_c)^" "^(string_of_int l_n)));
    (* MULTIPRED!! ~$next(x0,x1) *)
    let next_lit = neg (create_auto_path_atom var_curr var_next) in
    (* add new Cj to map *)
    map_latch next_lit l_c;
    (* create latch atom *)
    let latch_atom = v_next l_c in
    (* negate if necessary *)
    let latch_lit =
      if l_n = 0
      then neg latch_atom
      else latch_atom
    in
    (* create a clause *)
    cl [ next_lit; latch_lit ]
  in
  (* full latch clauses: {~$next(c,n),~l_c(n),l_n(c)}, {~$next(c,n),l_c(n),~l_n(c)}*)
  let full_latch l_c l_n =
    dbg D_latch (lazy ("full_latch "^(string_of_int l_c)^" "^(string_of_int l_n)));
    (* MULTIPRED!! ~$next(x0,x1) *)
    (* have to keep them same for both parts *)
    let next_lit = neg (create_auto_path_atom var_curr var_next) in
    (* add new Cj to map *)
    map_latch next_lit l_c;
    (* create latch and next atoms *)
    let l_a = v_next l_c in
    let n_a = v_cur l_n in
    (* create clauses *)
    [
      cl [ next_lit; l_a; (neg n_a) ];
      cl [ next_lit; (neg l_a); n_a ];
    ]
  in
  (* clausification of a general latch in use *)
  let clausify_used_latch latch =
    dbg D_latch (lazy ("clausify latch "^(latch_as_string latch)));
    (* get fields *)
    let l_c = latch.lit in
    let l_n = latch.next in
    let l_r = latch.reset in
    (* choose generated clauses *)
    let trans_clauses =
      if l_n > 1
      then full_latch l_c l_n
      else if l_n = l_r
      then [const_latch l_c l_n]
      else [half_latch l_c l_n]
    in
    (* add init if necessary *)
    let add_init clauses =
      (* TODO!! Double check that condition: we don't need to add the init if l_r > 2 *)
      if (l_n < 2) && (l_n = l_r)
      then clauses (* no need to add init here *)
      else (init_latch l_c l_r) :: clauses
    in
    (* return all clauses *)
    let clauses = add_init trans_clauses in
    (* save $$next clauses in the map *)
    latch2clauses_ref := IntMap.add latch.lit trans_clauses !latch2clauses_ref;
    (* return clauses *)
    clauses
  in
  let skip_latch = ref 0 in
  (* clausification of a general latch *)
  let clausify_latch accum latch =
    if latch.used
    then List.rev_append (clausify_used_latch latch) accum
    (* DEBUG use the line below instead to compare with aig2cnf *)
    (* then (clausify_used_latch latch) @ accum *)
    else (skip_latch := succ !skip_latch; accum)
  in
  (* put together init bi-imp clauses *)
  let init_extra_clauses () =
    if !current_options.bmc1_ucm
    then (* just collected clauses *)
      !init_to_clauses
    else (* let new_init = cl ( (create_auto_init_atom var_curr) :: !init_to_lits ) in *)
      []
  in
  (* process latches, add them to TAIL *)
  let process_latches tail =
    dbg D_trace (lazy ("generate latch clauses"));
    let tail_length = List.length tail in
    let new_clauses = List.fold_left clausify_latch tail problem.latches in

    dbg_env D_elapsed (fun () -> (elapsed_ts "process_latches"));
    let new_length = (List.length new_clauses) - tail_length in
    dbg D_stat (lazy ("latches translated into "^(string_of_int new_length)^" clauses"));
    dbg D_stat (lazy ("AIG: skip "^(string_of_int !skip_latch)^" latches"));
    let clauses_with_extra_init =
      if need_init_biimp ()
      then List.rev_append (init_extra_clauses ()) new_clauses
      else new_clauses
    in
    (* out_str ("Init:\n"^(Clause.to_string new_init)); *)
    clauses_with_extra_init
  in


  (*----------------------------------------------------------------*)
  (* clausification of a constraint: {constr} *)
  (*----------------------------------------------------------------*)
  let clausify_constraint accum constr =
    (cl [ v_cur constr.lit ]) :: accum
  in
  (* process constraints, add them to TAIL *)
  let process_constraints tail =
    dbg D_trace (lazy ("generate constraints clauses"));
    let tail_length = List.length tail in
    let new_clauses = List.fold_left clausify_constraint tail problem.constraints in
    dbg_env D_elapsed (fun () -> (elapsed_ts "process_constraints"));
    let new_length = (List.length new_clauses) - tail_length in
    dbg D_stat (lazy ("constraints translated into "^(string_of_int new_length)^" clauses"));
    new_clauses
  in


  (*----------------------------------------------------------------*)
  (* clausification of bad/outputs: for o1...oN being ALL outputs, *)
  (* property axiom:  ($property <-> ~o1 &...& ~oN) clausified to *)
  (* {$property,o1,...,oN}, {~$property,~o1},..., {~$property,~oN}, *)
  (**)

  (* generate {~$property,~o1},..., {~$property,~oN} given outs={o1,...,oN} *)
  let generate_from_property_clauses outs =
    (* create negated property atom *)
    let neg_property = neg property_atom in
    (* create an axiom {~$property,~out} *)
    let create_sp_clause accum out = 
      (nc [ neg_property; (neg (v_cur out.lit)) ]) :: accum in
    (* create all axioms of the form {~$property,~oK} *)
    List.fold_left create_sp_clause [] outs
  in
  let clausify_output outs =
    dbg D_trace (lazy ("process outputs"));
    (* save outputs *)
    let save_out accum out =
      if out.used
      then out.lit::accum
      else accum
    in
    outputs_ref := List.fold_left save_out [] outs;
    (* create $property,o1,...,oN *)
    let f accum out = (v_cur out.lit) :: accum in
    let arguments = List.fold_left f [property_atom] outs in
    (* create property clause; note negated conj *)
    let clause = nc arguments in
    (* return all clauses *)
    let new_clauses = clause :: (generate_from_property_clauses outs) in
    dbg_env D_elapsed (fun () -> (elapsed_ts "clausify_output"));
    let new_length = (List.length new_clauses) in
    dbg D_stat (lazy ("outputs translated into "^(string_of_int new_length)^" clauses"));
    (* save corresponding clauses *)
    output_clauses_ref := new_clauses;
    (* return out clauses *)
    new_clauses
  in

  (*----------------------------------------------------------------*)
  (* father_of support *)
  (*----------------------------------------------------------------*)

  (* add a father to a given child (both are lits) *)
  let add_father l_child l_father =
    (* add a father to a given child (both are vars) *)
    let add_non_empty child father =
      assert (child > 0);
      assert (father > 0);
      (* we have a map from symbols to strings *)
      let ch_symbol = v_i_symbol child in
      let father_str = v_i_name father in
      (* shortening *)
      let fom = Parser_types.father_of_map in
      (* retrieve known fathers if any *)
      let known_fathers =
        try SMap.find ch_symbol !fom
        with Not_found -> []
      in
      (* update the map *)
      fom := SMap.add ch_symbol (father_str::known_fathers) !fom
    in
    (* add father only if both parties are non-const *)
    if l_child > 1 && l_father > 1
    then add_non_empty (lit2var l_child) (lit2var l_father)
  in
  (* add father for conj *)
  let add_father_and conj =
    (* really add *)
    let add_father_used_and conj =
      add_father conj.lhs conj.rhs0;
      add_father conj.lhs conj.rhs1
    in
    (* check whether conj is used *)
    if conj.in_use
    then add_father_used_and conj
  in
  (* add father for latch *)
  let add_father_latch latch =
    (* really add *)
    let add_father_used_latch latch =
      add_father latch.lit latch.next;
      add_father latch.next latch.lit
    in
    (* check whether latch is used *)
    if latch.used
    then add_father_used_latch latch
  in
  (* init father_of for the whole problem *)
  let init_father_of () =
    dbg D_trace (lazy ("init father_of"));
    (* process all ANDs *)
    List.iter add_father_and problem.ands;
    (* process all latches *)
    List.iter add_father_latch problem.latches;
    dbg_env D_elapsed (fun () -> (elapsed_ts "init_father_of"))
  in

  (*----------------------------------------------------------------*)
  (* cone of influence support *)
  (*----------------------------------------------------------------*)

  let mark_all_cones problem =
    (* temporary list to gather all the clauses *)
    let clauses_ref = ref [] in
    (* AND processing method *)
    let process_and var =
      try
        let cls = IntMap.find var !aig2clauses_ref in
        (* dbg D_cone (lazy (" Processing cone for AND "^(string_of_int var))); *)
        (* save clauses corresponding to var *)
        clauses_ref := List.rev_append cls !clauses_ref
      with Not_found -> failwith "mark_cone: lit not found"
    in
    (* latch processing method *)
    let mark_latch latch =
      assert (list_is_empty !clauses_ref);
      dbg D_cone (lazy ("Processing cone for latch "^(string_of_int latch.lit)));
      (* mark cone started from next with addition of lit *)
      (* FIXME!!! latch.lit not in the aig2clauses_ref anymore *)
      AigOptimiser.apply_to_cone process_and latch.next latch.lit;
      (* save the result in the map *)
      let cj = IntMap.find latch.lit !latch_consts_ref in
      latch_cone_ref := TMap.add cj !clauses_ref !latch_cone_ref;
      (* clear temp list *)
      clauses_ref := [];
    in
    (* output processing method *)
    let mark_output symbol =
      dbg D_cone (lazy ("Processing cone for output "^(string_of_int symbol.lit)));
      (* mark cone started from the output adding the output itself *)
      AigOptimiser.apply_to_cone process_and symbol.lit symbol.lit;
      (* save the result in the array *)
      output_cone_ref := List.rev_append !clauses_ref !output_cone_ref;
      (* do not clear the list, accumulate clauses from all the outputs *)
    in
    (* mark the whole problem *)
    let mark_all problem =
      (* mark used latches *)
      let latch_folder latch =
        if latch.used
        then mark_latch latch
      in
      (* process all latches *)
      dbg D_cone (lazy ("Processing latches "^(string_of_int (List.length problem.latches))));
      List.iter latch_folder problem.latches;
      (* mark all outputs *)
      dbg D_cone (lazy ("Processing outputs"));
      List.iter mark_output problem.outputs;
      List.iter mark_output problem.bad;
      dbg D_cone (lazy ("done"));
      (* all done -- clear temp list *)
      clauses_ref := []
    in

    (* main body *)
    if !current_options.bmc1_ucm_cone_mode = Options.BMC1_Ucm_Cone_Mode_AIG
    then mark_all problem
    else ()
  in

  (*----------------------------------------------------------------*)
  (* important literals support *)
  (*----------------------------------------------------------------*)

  (* mark literal as important *)
  let add_imp_lit l =
    if l > 1
    then Important_lit.add_lit (v_i_symbol (l/2))
  in
  (* mark symbol as important *)
  let add_imp_symbol symbol =
    if symbol.used
    then add_imp_lit symbol.lit
  in
  (* mark latch as important *)
  let add_imp_latch latch =
    (* really add *)
    let add_imp_used_latch latch =
      add_imp_lit latch.lit;
      add_imp_lit latch.next
    in
    (* check whether latch is used *)
    if latch.used
    then add_imp_used_latch latch
  in
  (* important literals *)
  let mark_important_lits () =
    dbg D_trace (lazy ("mark important_lits"));
    (* important vars *)
    List.iter add_imp_symbol problem.inputs;
    (* important latches *)
    List.iter add_imp_latch problem.latches;
    dbg_env D_elapsed (fun () -> (elapsed_ts "mark_important_lits"))
  in
  (* add tautology to introduce constB0 *)
  let tautology () =
    (* property(b0) *)
    let prop = create_property_atom constB0 in
    (* tautology: {prop(B0),~prop(B0)} *)
    cl [ prop; (neg prop) ]
  in

  (* register symbols in natural order *)
  (* FIXME!! remove after there would be no need in comparison with CNF *)
  (* KK commented *)
  let register_var_symbols () =
    let rec reg_symbols min max =
      if min = max then ()
      else begin
        ignore (v_i_symbol min);
        reg_symbols (succ min) max
      end
    in
    dbg D_trace (lazy ("register var symbols"));
    reg_symbols 1 problem.max_var;
    dbg_env D_elapsed (fun () -> (elapsed_ts "register_var_symbols"))
  in

  (*----------------------------------------------------------------*)
  (* load clauses into parser *)
  (*----------------------------------------------------------------*)
  let load_into_parser cl nc =
    dbg D_trace (lazy ("loading into parser"));
    Parser_types.parsed_clauses := cl;
    Parser_types.neg_conjectures := nc;
    incr_int_stat ((List.length cl)+(List.length nc)) num_of_input_clauses;
    incr_int_stat 1 num_of_input_neg_conjectures;
    (* incr_int_stat (List.length nc) num_of_input_neg_conjectures *)
    dbg D_trace (lazy ("finish clausifier"));
    dbg_env D_elapsed (fun () -> (elapsed_ts "load_into_parser"))
  in

  (*----------------------------------------------------------------*)
  (* prepare witness structures *)
  (*----------------------------------------------------------------*)

  (* fill in latch data *)
  let fill_in_latches () =
    (* initialise the latches *)
    AigWitness.set_state_size (List.length problem.latches);
    (* init latch with a const value; return true if it was not a const *)
    let init_const i value =
      if value < 2
      then (
        AigWitness.set_latch_value i value;
        false
      )
      else
        true
    in
    (* folder for the latch *)
    let f i latch =
      (* record the latch var *)
      let l_c = latch.lit in
      if l_c > 1
      then (
        let latch_symb = v_i_symbol (l_c/2) in
        latch_vars_ref := SSet.add latch_symb !latch_vars_ref;
      );
      (* if the latch is const-initialised, set this const *)
      if (init_const i latch.reset)
      then (
        dbg D_latch_non_const (lazy ("Latch non-const: "^(latch_as_string latch)));
        (* non-const latch reset means it is uninitialised *)
        (* this means that for the AIG witness purposes we need to *)
        (* check the model and write the value of the latch here. *)
        (* For all other purposes it does not matter, so we just keep *)
        (* going here. The value of the init left 'x' *)
        (* TODO!! FIXME!! Correct this before the next competition!! *)
        ()

        (* out_str "UNEXPECTED!!"; *)
        (* (* make sure that the actual value of a latch *)                *)
        (* let syn = resolve_synonym latch.lit in                          *)
        (* (* if latch is reduced to a const then so is the init *)        *)
        (* if (init_const i syn)                                           *)
        (* then (* it is not a constant, so it have to be another latch *) *)
        (*   failwith "Unexpected twice!!"                                 *)
      )
    in
    List.iteri f problem.latches
  in

  (* fill in input data *)
  let fill_in_inputs () =
    (* initialise the inputs *)
    AigWitness.set_input_size (List.length problem.inputs);
    (* process single input *)
    let f i input =
      (* for consts we know the value *)
      if input.lit < 2
      then AigWitness.set_input_value i input.lit
      else (* no know value: mark as a symbol to obtain from the model *)
      (
        let var_symb = v_i_symbol (input.lit/2) in
        AigWitness.set_input_index i var_symb;

        dbg D_input_var (lazy (Symbol.to_string var_symb));
        input_vars_ref := SSet.add var_symb !input_vars_ref;
        input_vars_list_ref := var_symb::!input_vars_list_ref;
      )
    in
    (* pass through all inputs *)
    List.iteri f problem.inputs;
    (* reverse the input var list *)
    input_vars_list_ref := List.rev !input_vars_list_ref;
    (* that's it *)
    ()
  in

  (* fill in both latch and input data *)
  let fill_in_witness_data () =
    fill_in_latches ();
    fill_in_inputs ();
    dbg D_input_var (lazy ("number of input vars: "^(string_of_int (List.length !input_vars_list_ref))));
  in

  (*----------------------------------------------------------------*)
  (* actial build: clauses for different constructions *)
  (*----------------------------------------------------------------*)

  dbg_env D_elapsed (fun () -> timestamp ());

  (* register symbols in natural order *)
  register_var_symbols ();
  (* add father_of *)
  init_father_of ();
  (* mark some literals as important *)
  mark_important_lits ();
  (* process ands *)
  let and_clauses = process_ands [] in
  (* process latches *)
  let latch_clauses =process_latches and_clauses in
  (* process constraints *)
  let constraint_clauses = process_constraints latch_clauses in
  (* process outputs *)
  let out_clauses = clausify_output (problem.outputs @ problem.bad) in
  (* all input clauses *)
  let input_clauses = tautology () :: constraint_clauses in
  dbg D_trace (lazy ("merging clauses"));

  (* put generated clauses into parser *)
  load_into_parser input_clauses out_clauses;

  dbg D_trace (lazy ("prepare witnesses"));
  fill_in_witness_data ();

  (* make cones starting from latches *)
  (* dbg D_trace (lazy ("marking cones")); *)
  (* mark_all_cones problem;               *)
  dbg D_trace (lazy ("finish AIG clausification"));
  (* that's it *)
  ()

(*----------------------------------------------------------------*)
(* generate cone clauses  on the fly *)
(*----------------------------------------------------------------*)

let get_cone consts depth =
  (* get the active latch set *)
  let find_latch_var latch_term set =
    try
      IntSet.add (TMap.find latch_term !latch2var_ref) set
    with Not_found -> failwith "No latch const defined"
  in
  let latch_vars = TSet.fold find_latch_var consts IntSet.empty in
  (* get the vars in the cone *)
  out_str ("Output size: "^(string_of_int (List.length !outputs_ref)));
  let (cone, latches) = AigOptimiser.create_cone !outputs_ref latch_vars depth in
  (* helper to add a list of clauses correspond to an index in map to accum *)
  let add_from_map map index accum =
    try
      let clauses = IntMap.find index map in
      dbg D_cone (lazy ("clauses for var "^(string_of_int (index/2))^":\n"^(Clause.clause_list_to_string clauses)));
      List.rev_append clauses accum
    with Not_found ->
      dbg D_cone (lazy ("No clauses for var "^(string_of_int (index/2))));
      accum
  in
  (* merge all clauses together *)
  let latches_and_outputs = IntSet.fold (add_from_map !latch2clauses_ref) (IntSet.of_list latches) !output_clauses_ref in
  let all_cone = IntSet.fold (add_from_map !aig2clauses_ref) cone latches_and_outputs in
  (* return that clauses *)
  all_cone

(*----------------------------------------------------------------*)
(* get access to clause cones *)
(*----------------------------------------------------------------*)

(* get clauses for the property cone(s) *)
let get_property_cone () =
  !output_cone_ref

(* get clauses for the term (const Cj from the next predicate) *)
let get_latch_cone cj =
  try
    TMap.find cj !latch_cone_ref
  with
  | Not_found ->
    out_str ("Error: no cone for "^(Term.to_string cj));
    (* return nothing *)
    []

(* support for the symb clauses: return set of latch.lit that have Cj not is given set *)
let get_remainder consts =
  (* get all the bindings (predicates) from the symbol map *)
  let folder cj symb set = SSet.add symb set in
  let all_preds = TMap.fold folder !consts_vars_map_ref SSet.empty in
  (* folder that removes symbols coresponding Cj from the set *)
  let remove_const cj set =
    try
      let symb = TMap.find cj !consts_vars_map_ref in
      dbg D_cone (lazy ("Cone symbol "^(Symbol.to_string symb)));
      SSet.remove symb set
    with Not_found -> set
  in
  (* remove all found terms from full_problem *)
  let preds = TSet.fold remove_const consts all_preds in
  (* return that set *)
  preds
