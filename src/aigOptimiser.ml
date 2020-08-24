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

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr =
  | D_simplify_lit
  | D_synonym
  | D_simp_and
  | D_simp_latch
  | D_non_growing
  | D_simplify_value
  | D_same_structure
  | D_cone_process
  | D_stat_depth
  | D_simp_chain

let dbg_gr_to_str = function
  | D_simplify_lit -> "simplify_lit"
  | D_synonym -> "synonym"
  | D_simp_and -> "simplify_and"
  | D_simp_latch -> "simplify_lch"
  | D_non_growing -> "non_growing_subst"
  | D_simplify_value -> "simplify_value"
  | D_same_structure -> "same_structure"
  | D_cone_process -> "cone_process"
  | D_stat_depth -> "depth"
  | D_simp_chain -> "chain"

let dbg_groups =
  [
   D_simplify_lit;
   D_synonym;
   D_simp_and;
   D_simp_latch;
   D_same_structure;
   (* D_non_growing; *)
   (* D_simplify_value; *)
   D_stat_depth;
   (* D_simp_chain; *)
 ]

let module_name = "aig_optimiser"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)

let indent_str = ref 0

let inc_indent () = ()
(* indent_str := succ !indent_str *)
let dec_indent () = ()
(* indent_str := pred !indent_str *)
let indent () =
  let rec indent_f n =
    if n <= 0
    then ""
    else " "^(indent_f (pred n))
  in
  indent_f !indent_str

(* data structures for non-growing clausifier *)

module Key =
  struct
    type t      = int
    let compare = (-)
  end

module VarMap = Map.Make(Key)

module OrderedIntPair =
  struct
    type t = int * int
    let compare (x1,x2) (y1,y2) =
      if x1 < y1 then -1
      else if x1 > y1 then 1
      else if x2 < y2 then -1
      else if x2 > y2 then 1
      else 0
  end

module OrdIntMap = Map.Make(OrderedIntPair)

(*----------------------------------------------------------------*)
(* statistics-related stuff *)
(*----------------------------------------------------------------*)

(* statistics *)
let num_synonyms = ref 0
let num_non_growing_subst = ref 0
let num_reducing_subst = ref 0
let num_const_latches = ref 0
let num_same_ands = ref 0
let num_same_latches = ref 0

(* get total number of all applied optimisations *)
let get_total_stat () = !num_synonyms + !num_non_growing_subst + !num_const_latches

(* print statistics *)
let print_stat () =
  let pref = "AIG optimisation stat: " in
  out_str (pref^(string_of_int !num_synonyms)^" synonyms");
  out_str (pref^(string_of_int !num_same_ands)^" same ands");
  out_str (pref^(string_of_int !num_same_latches)^" same latches");
  out_str (pref^(string_of_int !num_non_growing_subst)^" non-growing inlinings");
  out_str (pref^(string_of_int !num_reducing_subst)^" shrinking inlinings");
  out_str (pref^(string_of_int !num_const_latches)^" constant latches")

(*----------------------------------------------------------------*)
(* initialisation of structures *)
(*----------------------------------------------------------------*)

(* chain of applied simplifications *)
let simp_chain = ref []


(* map every AIG literal to its synonym *)
let synonyms = ref (Array.make 0 0)
(* map var corresponding to latch into the latch itself *)
let latch_map = ref VarMap.empty
(* map var corresponding to and into the and itself *)
let and_map_ref = ref VarMap.empty

(* map for all active ANDs, x1*x2->y *)
let and_syn_map = ref OrdIntMap.empty
(* map for all active latches, next*reset->lit *)
let latch_syn_map = ref OrdIntMap.empty

(* clear all intermediate AIG structures *)
let clear_aig_structures () =
  and_syn_map := OrdIntMap.empty;
  latch_syn_map := OrdIntMap.empty;
  simp_chain := [];
  (* and_map_ref := VarMap.empty; *)
  (* latch_map := VarMap.empty;   *)
  (* that's it *)
  ()

(* creates a default array for synonyms *)
let create_synonyms_array problem =
  (* get the proper length *)
  let len = 2*(succ problem.max_var) in
  (* init function: just get the index *)
  let f i = i in
  (* create an array of a proper length *)
  synonyms := Array.init len f

(* creates a map from vars (not lits) to ANDs *)
let create_and_map ands =
  (* add a single conj to map *)
  let add_conj map conj = VarMap.add (lit2var conj.lhs) (ref conj) map in
  (* apply to the list *)
  and_map_ref := List.fold_left add_conj VarMap.empty ands

(* creates a map from vars (not lits) to latches *)
let create_latch_map latches =
  (* add a single conj to map *)
  let add_latch map latch = VarMap.add (lit2var latch.lit) (ref latch) map in
  (* apply to the list *)
  latch_map := List.fold_left add_latch VarMap.empty latches

(* chain manipulation *)

let simp_chain_to_str () =
  let out_val acc value = (string_of_int value)^","^acc in
  let tail = List.fold_left out_val "]" !simp_chain in
  "["^tail

let add_to_chain lit =
  simp_chain := (lit2var lit)::!simp_chain

let del_from_chain () =
  simp_chain := List.tl !simp_chain

let report_chain lit =
  dbg_env D_simp_chain (fun () ->
    let var = lit2var lit in
    let same v = (v = var) in
    if List.exists same !simp_chain
    then
      dbg D_simp_chain (lazy ("found "^(string_of_int lit)^
        " (as "^(string_of_int var)^") in "^(simp_chain_to_str ())))
  )

(* lit manipulation *)

(* return lit if sign=0 of ~lit if sign=1 *)
let adjust_lit lit sign =
  assert (sign >= 0);
  assert (sign < 2);
  if sign = 0
  then lit (* positive lits stay *)
  else (neg lit)

(* get lit by its var an the sign given by an original lit *)
let var2lit var lit =
  if lit < 2 (* original lit was const *)
  then lit (* return that const *)
  else adjust_lit (2*var) (lit mod 2)

(* synonyms *)

(* set synonym for the literal *)
let set_synonym lit syn =
  assert (lit > 1);
  !synonyms.(lit) <- syn;
  !synonyms.(neg lit) <- (neg syn);
  num_synonyms := (succ !num_synonyms);
  (* debug print *)
  dbg D_synonym (lazy ("set synonym for "^(string_of_int lit)^" to "^(string_of_int syn)))

(* resolve synonym for the literal *)
let rec resolve_synonym lit =
  (* check whether there are no synonyms *)
  if !synonyms.(lit) = lit
  (* then return the var itself *)
  then lit
  else begin
    let syn = resolve_synonym !synonyms.(lit) in
    dbg D_synonym (lazy ("synonym for "^(string_of_int lit)^" is "^(string_of_int syn)));
    (* save that synonym *)
    (* synonyms.(lit) <- syn; *)
    (* return it *)
    syn
  end

(*----------------------------------------------------------------*)
(* synonym elimination and non-growing inlining *)
(*----------------------------------------------------------------*)

exception Simplified_Latch of int
exception Simplified_And of int

(* simplify literal *)
let rec simplify_lit lit =
  dbg D_simplify_lit (lazy ((indent())^(string_of_int lit)));
  inc_indent ();
  (* debug: change value to lit in general case *)
  report_chain lit;
  add_to_chain lit;
  let ret =
    if lit < 2
    then lit  (* nothing to do with consts *)
    else begin
      (* get a synonym of literal *)
      let syn = resolve_synonym lit in
      (* try to simplify AND wrt synonym *)
      try
        (* simplify AND *)
        let tmp = simplify_and (VarMap.find (lit2var syn) !and_map_ref) in
        (* adjust the literal *)
        adjust_lit tmp (syn mod 2)
      with (* not an AND -> try LATCH *)
      | Not_found -> try
        (* get latch *)
        let tmp = simplify_latch (VarMap.find (lit2var syn) !latch_map) in
        (* adjust the literal *)
        adjust_lit tmp (syn mod 2)
      with (* not a LATCH -> done *)
      | Not_found -> syn
    end
  in
  (* debug out *)
  dec_indent ();
  del_from_chain ();
  dbg_env D_simplify_lit (fun () ->
    let s_l = (string_of_int lit) in
    let s_r = (string_of_int ret) in
    let conn =
      if lit = ret
      then " remains "
      else " became "
    in
    dbg D_simplify_lit (lazy ((indent())^s_l^conn^s_r))
  );
  (* return the value *)
  ret

(* simplify latch n n reset making n synonym to reset *)
and simplify_latch latch_ref =
  (* check the constant latch *)
  let check_const_latch latch_ref =
    if (!latch_ref.lit = !latch_ref.next) (* here next(l) = l, so the latch is a const determined by reset *)
      || (!latch_ref.next = !latch_ref.reset) (* here next(l) = r, where r is 0/1, so -''- *)
    then begin
      num_const_latches := (succ !num_const_latches);
      (* TODO!! check what if reset is unset *)
      raise (Simplified_Latch !latch_ref.reset);
    end
  in
  (* check whether latch with the same arguments already found *)
  let find_same_latch latch_ref =
    try
      let syn = OrdIntMap.find (!latch_ref.next, !latch_ref.reset) !latch_syn_map in
      num_same_latches := (succ !num_same_latches);
      dbg D_same_structure (lazy ("Found synonym for "^(latch_as_string !latch_ref)^": "^(latch_as_string syn)));
      raise (Simplified_Latch syn.lit)
    with Not_found ->
      latch_syn_map := OrdIntMap.add (!latch_ref.next, !latch_ref.reset) !latch_ref !latch_syn_map
  in

  (* function starts here *)

  (* check whether latch need to be processed *)
  if (not !latch_ref.used) && (not !latch_ref.removed)
  then begin
    (* mark it used straight away, to prevent infinite recursion. *)
    (* If it will be simplified later, then the next round *)
    (* of optimisaitons will pick the optimised version up. *)
    !latch_ref.used <- true;
    (* debug out *)
    dbg D_simp_latch (lazy ((indent())^(string_of_int !latch_ref.lit)^" as "^(latch_as_string !latch_ref)));
    try
      let old_next = !latch_ref.next in
      !latch_ref.next <- simplify_lit !latch_ref.next;
      check_const_latch latch_ref;
      find_same_latch latch_ref;
      (* debug out *)
      if old_next <> !latch_ref.next
      then
        dbg D_simp_latch (lazy ((indent())^(string_of_int !latch_ref.lit)^" became "^(latch_as_string !latch_ref)))
      else
        dbg D_simp_latch (lazy ((indent())^(string_of_int !latch_ref.lit)^" stays the same"))
    with Simplified_Latch lit ->
      (* debug out *)
      dbg D_simp_latch (lazy ((indent())^(string_of_int !latch_ref.lit)^" became "^(string_of_int lit)));
      (* mark it a removed *)
      !latch_ref.removed <- true;
      (* update synonyms *)
      set_synonym !latch_ref.lit lit;
      (* do not keep that latch *)
      !latch_ref.used <- false;
  end;
  (* return the representation of the latch's head *)
  let ret =
    if !latch_ref.removed
    (* return the synonym of a latch *)
    then resolve_synonym !latch_ref.lit
    else !latch_ref.lit
  in
  (* return the representative *)
  ret


(* simplify and *)
and simplify_and and_ref =
  (* simplify AND with two given arguments, evaluating the 1st one *)
  let simplify_and_of_const arg0 arg1 =
    (* (and 0 n) = 0, (and n ~n) = 0 *)
    if (arg0 = 0) || (arg0 = (neg arg1))
    then (
      dbg D_simp_and  (lazy ((indent())^"is false: "^(string_of_int arg0)^","^(string_of_int arg1)));
      raise (Simplified_And 0)
    )
    (* (and 1 n) = n, (and n n) = n *)
    else if (arg0 = 1) || (arg0 = arg1)
    then (
      dbg D_simp_and  (lazy ("is synonym: "^(string_of_int arg0)^","^(string_of_int arg1)));
      raise (Simplified_And (simplify_lit arg1))
    )
  in
  (* substitute conj into and_ref if non-growing *)
  let substitute_if_non_growing and_ref conj =
    (* vars in the original and *)
    let op0 = !and_ref.rhs0 in
    let op1 = !and_ref.rhs1 in
    (* head of conj *)
    let head = (lit2var conj.lhs) in
    (* is true iff the substitutions head is at rhs0 *)
    let subst_0 = (lit2var op0) = head in
    (* other op in the original and with a sign *)
    (* same_a is true iff x = a & ... *)
    let (op, same_a) =
      if subst_0
      then (op1, (!and_ref.rhs0 mod 2 == 0))
      else (op0, (!and_ref.rhs1 mod 2 == 0))
    in
    (* ops of conj *)
    let o0 = conj.rhs0 in
    let o1 = conj.rhs1 in
    (* test applicability *)
    if ((lit2var op) = (lit2var o0) || (lit2var op) = (lit2var o1))
    then begin
      dbg D_simp_and (lazy ((and_as_string !and_ref)^" with substitution "^(and_as_string conj)));
      num_non_growing_subst := (succ !num_non_growing_subst);
      (* same_b is true iff x = ... & b *)
      let (b, c, same_b) =
        if (lit2var op) = (lit2var o0)
        then (o0, o1, o0 = op)
        else (o1, o0, o1 = op)
      in
      (* now same_a and same_b gives up 4 options *)
      if ( (not same_a) && (not same_b) )
      then
        begin
          (* here a = b & c and x = ~a & ~b *)
          dbg D_non_growing (lazy ("case 4: a = b & c and x = ~a & ~b"));
          num_reducing_subst := (succ !num_reducing_subst);
          (* replace with x = ~b *)
          !and_ref.rhs0 <- (neg b);
          !and_ref.rhs1 <- 1;
        end
      else if ( same_a && (not same_b) )
      then
        begin
          (* here a = b & c and x = a & ~b *)
          dbg D_non_growing (lazy ("case 2: a = b & c and x = a & ~b"));
          num_reducing_subst := (succ !num_reducing_subst);
          (* replace with x = 0 *)
          !and_ref.rhs0 <- 0;
          !and_ref.rhs1 <- 1;
        end
      else
        begin
          (* here a = b & c and x = (~)a & b *)
          dbg D_non_growing (lazy ("case 1,3: a = b & c and x = (~)a & b"));
          (* replace with x = (~)c & b *)
          let repl =
            if same_a
            then c
            else (neg c)
          in
          (* replace (~)a with (~)c to keep the changes minimal *)
          if subst_0
          then !and_ref.rhs0 <- repl
          else !and_ref.rhs1 <- repl
        end
      ;
      dbg D_simp_and (lazy ("after application "^(and_as_string !and_ref)));
      (* there might be some opportunity to simplification *)
      simplify_and_of_const !and_ref.rhs1 !and_ref.rhs0
    end
  in
  (* non-growing substitution here *)
  let substitute_non_growing and_ref =
    (* substitute op0 *)
    try
      substitute_if_non_growing and_ref !(VarMap.find (lit2var !and_ref.rhs0) !and_map_ref)
    with
    | Not_found -> ();
    if (not !and_ref.simplified)
    then (* substitute op1 *)
      try
        substitute_if_non_growing and_ref !(VarMap.find (lit2var !and_ref.rhs1) !and_map_ref)
      with
      | Not_found -> ();
  in

  (* check whether AND with the same arguments already found *)
  let find_same_and and_ref =
    try
      let syn = OrdIntMap.find (!and_ref.rhs0, !and_ref.rhs1) !and_syn_map in
      num_same_ands := (succ !num_same_ands);
      dbg D_same_structure (lazy ("Found synonym for "^(and_as_string !and_ref)^": "^(and_as_string syn)));
      raise (Simplified_And syn.lhs)
    with Not_found ->
    try
      let syn = OrdIntMap.find (!and_ref.rhs1, !and_ref.rhs0) !and_syn_map in
      num_same_ands := (succ !num_same_ands);
      dbg D_same_structure (lazy ("Found synonym for "^(and_as_string !and_ref)^": "^(and_as_string syn)));
      raise (Simplified_And syn.lhs)
    with Not_found ->
      and_syn_map := OrdIntMap.add (!and_ref.rhs0, !and_ref.rhs1) !and_ref !and_syn_map
  in

  (* function starts here *)

  inc_indent ();
  (* if the AND is not processed *)
  if (not !and_ref.in_use) && (not !and_ref.simplified)
  then begin
    (* debug out *)
    dbg D_simp_and (lazy ((indent())^(string_of_int !and_ref.lhs)^" as "^(and_as_string !and_ref)));
    (* mark it used straight away, to prevent infinite recursion. *)
    (* If it will be simplified later, then the next round *)
    (* of optimisaitons will pick the optimised version up. *)
    !and_ref.in_use <- true;
    try
      let old_0 = !and_ref.rhs0 in
      let old_1 = !and_ref.rhs1 in
      simplify_and_of_const !and_ref.rhs0 !and_ref.rhs1;
      simplify_and_of_const !and_ref.rhs1 !and_ref.rhs0;
      (* simplify both arguments *)
      !and_ref.rhs0 <- simplify_lit !and_ref.rhs0;
      simplify_and_of_const !and_ref.rhs0 !and_ref.rhs1;
      !and_ref.rhs1 <- simplify_lit !and_ref.rhs1;
      simplify_and_of_const !and_ref.rhs1 !and_ref.rhs0;
      substitute_non_growing and_ref;
      find_same_and and_ref;
      (* report if something change *)
      if not ((old_0 = !and_ref.rhs0) && (old_1 = !and_ref.rhs1))
      then dbg D_simp_and (lazy ((indent())^(string_of_int !and_ref.lhs)^" became "^(and_as_string !and_ref)));
    with Simplified_And lit ->
      (* mark it a simplified *)
      !and_ref.simplified <- true;
      (* update synonyms *)
      set_synonym !and_ref.lhs lit;
      (* debug print *)
      dbg D_simp_and (lazy ((indent())^(string_of_int !and_ref.lhs)^" became "^(and_as_string !and_ref)));
      (* keep the actual AND only *)
      !and_ref.in_use <- false
  end;
  (* debug out *)
  dec_indent ();
  (* get the representation of the and *)
  let ret =
    if !and_ref.simplified
    (* return the synonym of an AND *)
    then resolve_synonym !and_ref.lhs
    else !and_ref.lhs
  in
  (* return the representative *)
  ret

(* perform non-growing AND substitution together with synonyms removal in-place *)
let non_growing_substitution_aig problem =
  (* simplify given value with debug info *)
  let simplify_value lit name =
    (* debug out *)
    dbg D_simplify_value (lazy (name^" "^(string_of_int lit)));
    (* perform simplification *)
    let out = simplify_lit lit in
    (* debug out *)
    if out <> lit
    then
      dbg D_simplify_value (lazy (name^" "^(string_of_int lit)^" became "^(string_of_int out)));
    (* return new value *)
    out
  in
  (* simplify the value of an output *)
  let simplify_output symbol =
    if symbol.used
    then symbol.lit <- simplify_value symbol.lit "output"
  in
  (* simplify the value of a constraint *)
  let simplify_constraint symbol =
    if symbol.used
    then symbol.lit <- simplify_value symbol.lit "constraint"
  in
  (* simplify outputs *)
  List.iter simplify_output problem.outputs;
  (* simplify bads *)
  List.iter simplify_output problem.bad;
  (* simplify constraints *)
  List.iter simplify_constraint problem.constraints

(* run all the optimisations *)
(* TODO other optimisations *)
let run_optimisations problem =
  (* run the non-growing inlining *)
  non_growing_substitution_aig problem

(*----------------------------------------------------------------*)
(* post-optimisation actions  *)
(*----------------------------------------------------------------*)

(* clear all usage flags *)
let clear_usage problem =
  (* clear known ANDs and latches *)
  and_syn_map := OrdIntMap.empty;
  latch_syn_map := OrdIntMap.empty;

  (* clear in_use attribute from an AND *)
  let clear_in_use_and conj = conj.in_use <- false in
  List.iter clear_in_use_and problem.ands;
  (* clear used attribute for latches, as outputs/constraints are used *)
  let clear_used_symbol symbol = symbol.used <- false in
  List.iter clear_used_symbol problem.latches

(*----------------------------------------------------------------*)
(* cone-based methods *)
(*----------------------------------------------------------------*)

(* apply f to the cone started from cone_var and contained EXTRA *)
let apply_to_cone f cone_var extra =
  (* put all vars for the cone into a given set *)
  let rec gather_cone lit set =
    (* check whether var is an AND *)
    try
      let conj = VarMap.find (lit2var lit) !and_map_ref in
      (* check that conj is actual *)
      if !conj.simplified
      then failwith "Simplified AND found in the actual cone";

      (* check that we already tested that one *)
      let var = !conj.lhs in
      if (IntSet.mem var set)
      then (* checked that one -- do nothing *)
        set
      else (
        (* add AND bit to the set *)
        let set_l = IntSet.add var set in
        (* go further *)
        let set_0 = gather_cone !conj.rhs0 set_l in
        let set_1 = gather_cone !conj.rhs1 set_0 in
        (* return the last set *)
        set_1
      )
    with (* not an AND -> stop here *)
    | Not_found -> set
  in
  (* gather the cone starting from a given var *)
  let cone' = gather_cone cone_var IntSet.empty in
  (* add extra bit *)
  let cone = IntSet.add extra cone' in
  (* apply functor to all gathered literals *)
  IntSet.iter f cone

(* keeps the full depth of the problem *)
let full_depth_ref = ref false

(* go through all the outputs and latches from the set latches_in_use *)
(* gathering all vars (AND/latch) passed through. Bound is unused at the moment *)
let create_cone outs latches_in_use bound =
  (* collected set of vars *)
  let found_vars_ref = ref IntSet.empty in
  (* latches to be processed on the next depth *)
  let next_depth_ref = ref [] in
  (* all latches succesfully passed *)
  let latches_collected_ref = ref [] in

  (* mark cone started from a given lit and bound *)
  let rec mark_cone lit =
    (* check whether var is an AND *)
    try
      let conj = VarMap.find (lit2var lit) !and_map_ref in
      (* check that conj is actual *)
      if !conj.simplified
      then failwith "Simplified AND found in the actual cone";
      if not !conj.in_use
      then failwith "AND not in use found in the actual cone";

      (* check that we already tested that one *)
      let var = !conj.lhs in

      dbg D_cone_process (lazy ("PROCESSING: const v_"^(string_of_int (var/2))));
      if (IntSet.mem var !found_vars_ref)
      then (* checked that one -- do nothing *)
        ()
      else (
        (* add AND bit to the set *)
        found_vars_ref := IntSet.add var !found_vars_ref;

        dbg D_cone_process (lazy ("PROCESSING: +v_"^(string_of_int (var/2))));
        (* go further *)
        mark_cone !conj.rhs0;
        mark_cone !conj.rhs1;
      )
    with (* not an AND -> try latch *)
    | Not_found -> try
      let latch = VarMap.find (lit2var lit) !latch_map in
      (* check that latch is actual *)
      if !latch.removed
      then failwith "Removed latch found in the actual cone";
      if not !latch.used
      then failwith "Latch not in use found in the actual cone";

      (* check that we already tested that one *)
      let var = !latch.lit in

      dbg D_cone_process (lazy ("PROCESSING: latch v_"^(string_of_int (var/2))));
      if (IntSet.mem var !found_vars_ref)
      then (* checked that one -- do nothing *)
        ()
      else (
        (* add the latch var to the set *)
        found_vars_ref := IntSet.add var !found_vars_ref;
        dbg D_cone_process (lazy ("PROCESSING: +v_"^(string_of_int (var/2))));
        (* we continue if we're building full set (depth >= 0) *)
        (* OR if we're if we have the latch enable *)
        if (bound >= 0) || (IntSet.mem var latches_in_use)
        then ( (* go further *)
          (* schedule to gather the cone for the definition *)
          next_depth_ref := !latch.next::!next_depth_ref
        )
        else
          dbg D_cone_process (lazy ("PROCESSING: skip latch v_"^(string_of_int (var/2))));
      )
    with (* neither AND nor latch -- stop here *)
    | Not_found ->
      ()
  in

  (* process the next level of latches *)
  let process_next_level () =
    let vars_to_go = !next_depth_ref in
    next_depth_ref := [];
    List.iter mark_cone vars_to_go
  in

  (* main method *)

  let rec collect_cones_to_depth depth =
    let d = pred depth in
    (* we need to collect at least once *)
    process_next_level ();
    (* stop if remaining depth is 0 *)
    match d with
    | 0 -> () (* stop with 0 *)
    | _ ->
      (* collect latches gathered to the moment *)
      latches_collected_ref := List.rev_append !next_depth_ref !latches_collected_ref;
      if list_non_empty !next_depth_ref
      then collect_cones_to_depth d
      else full_depth_ref := true
  in

  (* prepare outputs to be processed *)
  next_depth_ref := outs;
  full_depth_ref := false;
  latches_collected_ref := [];
  (* find cones *)
  collect_cones_to_depth bound;
  (* return collected set *)
  !found_vars_ref, !latches_collected_ref

(* return true if depth is larger than the problem depth *)
let pass_problem_depth depth =
  dbg D_stat_depth (lazy ("test depth "^(string_of_int depth)^", diameter "^(if !full_depth_ref then "reached" else "NOT reached")));
  (depth < 0) || !full_depth_ref

(*----------------------------------------------------------------*)
(* cleanup problem: resolve synonyms for ANDs and LATCHes arguments *)
(*----------------------------------------------------------------*)
let cleanup problem =
  (* replace AND args with synonyms *)
  let cleanup_and and_ref =
    if and_ref.in_use
    then (
      and_ref.rhs0 <- resolve_synonym and_ref.rhs0;
      and_ref.rhs1 <- resolve_synonym and_ref.rhs1;
    )
  in
  (* replace LATCH args with synonyms *)
  let cleanup_latch latch_ref =
    if latch_ref.used
    then
      latch_ref.next <- resolve_synonym latch_ref.next
  in
  (* cleanup ANDs *)
  List.iter cleanup_and problem.ands;
  (* cleanup LATCHes *)
  List.iter cleanup_latch problem.latches

(*----------------------------------------------------------------*)
(* prepare witness structures *)
(*----------------------------------------------------------------*)

(* (* fill in latch data *)                                                                                *)
(* let fill_in_latches problem =                                                                           *)
(*   (* initialise the latches *)                                                                          *)
(*   AigWitness.set_state_size (List.length problem.latches);                                              *)
(*   (* init latch with a const value; return true if it was not a const *)                                *)
(*   let init_const i value =                                                                              *)
(*     if value < 2                                                                                        *)
(*     then (                                                                                              *)
(*       AigWitness.set_latch_value i value;                                                               *)
(*       false                                                                                             *)
(*     )                                                                                                   *)
(*     else                                                                                                *)
(*       true                                                                                              *)
(*   in                                                                                                    *)
(*   (* folder for the latch *)                                                                            *)
(*   let f i latch =                                                                                       *)
(*     (* if the latch is const-initialised, set this const *)                                             *)
(*     if (init_const i latch.reset)                                                                       *)
(*     then (                                                                                              *)
(*       out_str "UNEXPECTED!!";                                                                           *)
(*       (* make sure that the actual value of a latch *)                                                  *)
(*       let syn = resolve_synonym latch.lit in                                                            *)
(*       (* if latch is reduced to a const then so is the init *)                                          *)
(*       if (init_const i syn)                                                                             *)
(*       then (* it is not a constant, so it have to be another latch *)                                   *)
(*         try                                                                                             *)
(*           (* get latch *)                                                                               *)
(*           let latch_ref = VarMap.find (lit2var syn) !latch_map in                                       *)
(*           (* if the reset is not a constant... *)                                                       *)
(*           if (init_const i !latch_ref.reset)                                                            *)
(*           then (* then if is X, let's mark it accordingly *)                                            *)
(*             AigWitness.set_latch_index i                                                                *)
(*       with (* not a LATCH -> error, as we only replace latch with const/another latch *)                *)
(*       | Not_found -> failwith "Unexpected: latch could be simplified as another latch of constant only" *)
(*     )                                                                                                   *)
(*   in                                                                                                    *)
(*   List.iteri f problem.latches                                                                          *)

(* (* fill in input data *)                                                                                *)
(* let fill_in_inputs problem =                                                                            *)
(*   (* initialise the inputs *)                                                                           *)
(*   AigWitness.set_input_size (List.length problem.inputs);                                               *)
(*   (* process single input *)                                                                            *)
(*   let f i input =                                                                                       *)
(*     (* resolve synonym for the input *)                                                                 *)
(*     let syn = resolve_synonym input.lit in                                                              *)
(*     (* for consts we know the value *)                                                                  *)
(*     if syn < 2                                                                                          *)
(*     then AigWitness.set_input_value i syn                                                               *)
(*     else (* no *)                                                                                       *)
(*   (* that's it *)                                                                                       *)
(*   ()                                                                                                    *)

(* (* fill in both latch and input data *)                                                                 *)
(* let fill_in_witness_data problem =                                                                      *)
(*   fill_in_latches problem;                                                                              *)
(*   fill_in_inputs problem                                                                                *)

(*----------------------------------------------------------------*)
(* full optimisation loop *)
(*----------------------------------------------------------------*)

(* optimise AIG problem running optimisations n times *)
let optimise_aig_n problem n =
  (* init list of synonyms *)
  create_synonyms_array problem;
  (* init and map *)
  create_and_map problem.ands;
  (* init latch map *)
  create_latch_map problem.latches;
  (* problem is clean if no new optimisations were performed *)
  let clean = ref true in
  (* apply all optimisations to a problem *)
  let rec apply_optimisation old_stat i =
    (* while i is smaller than n *)
    if i < n
    then begin
      (* clear in_use attribute from ANDs *)
      clear_usage problem;
      (* run the optimisations *)
      run_optimisations problem;
      (* print the stat *)
      print_stat ();
      (* get the stat *)
      let new_stat = get_total_stat () in
      (* if some optimisations were applied *)
      if old_stat < new_stat
      then (* re-run the optimisations *) (
        (* not sure that problem is clean *)
        clean := false;
        apply_optimisation new_stat (succ i)
      )
      else
        clean := true
    end
  in
  (* apply common opt method n times *)
  apply_optimisation 0 0;
  if not !clean
  then cleanup problem;
  (* (* prepare witnesses *)       *)
  (* fill_in_witness_data problem; *)
(* TODO renumerate vars to have correct AIG *)
  (* that's it *)
  ()

(* optimise AIG problem *)
let optimise_aig problem = optimise_aig_n problem 100
