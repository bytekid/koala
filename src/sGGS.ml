module H = Hashtbl
open Clause
open Term
open Logic_interface
open Subst
open Finite_models

module T = Term
module L = List
module F = Format
module C = Clause
module S = Subst
module DiscTree = UnifIndexDiscrTree
module Sym = Symbol
module SSet = Clause.SSet
module LL = LazyList
module O = Options 
module FM = Finite_models

type result = Satisfiable | Unsatisfiable | Unknown

let (<.>) f g x = f (g x)

let (<!>) l k = L.nth l k

let zip xs ys = L.fold_right2 (fun x y l -> (x,y) :: l) xs ys []

let term_db_ref = SystemDBs.term_db_ref

let add_term t = TermDB.add_ref t term_db_ref

let compl_lit l = add_term (Term.compl_lit l)

let pcmp = Pervasives.compare

let start_time = ref 0.0

(* utilities *)
let index ?(from=0) l =
  snd (L.fold_left (fun (i, xs) y -> (i + 1, xs @ [y,i])) (from,[]) l)
;;

(* exclusive i *)
let rec until i l = 
  if i == 0 then []
  else match l with
    | [] -> failwith "SGGS.until failed"
    | x :: xs -> x :: (until (i - 1) xs)
;;

let from n ll = 
  let rec from i l = 
    if i == 0 then l
    else match l with
      | [] -> [] (*Format.printf "from failed %d %d\n%!" n (L.length ll); failwith "from: failed"*)
      | _ :: xs -> from (i - 1) xs
in from n ll
;;

let from_to i j l = until (j - i) (from i l)

(* exclusive i *)
let rec range i j = if i >= j then [] else i :: (range (i+1) j) 

(* remove first *)
let rec remove eq x = function
  | [] -> failwith "remove: failed"
  | y :: ys -> if eq x y then ys else y :: (remove eq x ys)
;;

let remove_term = remove (fun s t -> T.compare_key s t = 0)

let rec unique ?(c = pcmp) = function
  | [] -> []
  | x :: xs -> x :: unique ~c:c (L.filter (fun y -> c x y <> 0) xs)
;;

let list_opt_fold f o = L.fold_left (fun o x -> if o<>None then o else f x) None 

(* FIXME unused *)
let add_compose x t sigma =
  let sub = Subst.apply_subst_term term_db_ref (S.add x t (S.create ())) in
  let sigma' =S.fold (fun x t tau -> S.add x (sub t) tau) sigma (S.create ()) in
  if not (S.mem x sigma') then S.add x t sigma'
  else
    let u = S.find x sigma' in
    if t = u then sigma' else failwith "SGGS.add_compose: double binding"
;;

let variables t = L.map fst (T.get_var_ass_list t)

let rec unify_aux subst = function
  | [] -> subst
  | (s, t) :: eqs when s = t -> unify_aux subst eqs
  | (T.Var (x, _), t) :: eqs when not (L.mem x (variables t)) ->
    let sub = S.add x t (S.create ()) in
    let apply_subst = Subst.apply_subst_term term_db_ref sub in
    let eqs' = L.map (fun (l, r) -> apply_subst l, apply_subst r) eqs in
    unify_aux (add_compose x t subst) eqs'
  | (t, T.Var (x, _)) :: eqs when not (L.mem x (variables t)) ->
    let sub = S.add x t (S.create ()) in
    let apply_subst = Subst.apply_subst_term term_db_ref sub in
    let eqs' = L.map (fun (l, r) -> apply_subst l, apply_subst r) eqs in
    unify_aux (add_compose x t subst) eqs'
  | (T.Fun (f, ss, _), T.Fun (g, ts, _)) :: eqs when f = g ->
    unify_aux subst ((L.combine ss ts) @ eqs)
  | (s,t) :: _ -> raise Unif.Unification_failed
;;

let mgu_list eqs = unify_aux (S.create ()) eqs

let mgu_exists s t = try let _ = mgu_list [(s, t)] in true with _ -> false

let mgu ?(away=[]) l r =
  let away = if away = [] then variables r else away in
  let l = add_term (L.hd (snd (rename_term_list term_db_ref away [l]))) in
  mgu_list [(l, r)]
;;

let pp_lits ppf lits =
  F.fprintf ppf "{%a}" (Lib.pp_any_list Term.pp_term "; ") lits
;;

(* first argument is pattern *)
let matches l t =
  try let _ = Unif.matches l t in true with Unif.Matching_failed -> false
;;

let ensure_match l t =
  if not (matches l t) then (
    F.printf "does not match: %a for pattern %a\n%!" T.pp_term t T.pp_term l;
    failwith "SGGS.ensure_match" );
  Unif.matches l t
;;

let modify_clause c lits =
  let tstp_src = C.tstp_source_global_subsumption 0 c in
  C.create_clause term_db_ref tstp_src lits
;;

let fun_cmp (f,a) (g,b) = let c = pcmp a b in if c=0 then Sym.compare f g else c

let term_size t = T.get_num_of_symb t + T.get_num_of_var t

let clause_size c = L.fold_left (+) 0 (L.map term_size (C.get_lits c))

let ground_size_table : (Symbol.t * int, T.term list) H.t = H.create 128
let ground_upto_size_table : (Symbol.t * int, T.term list) H.t = H.create 128

let all_ground_terms sort funs =
  let val_type f = snd (Symbol.get_stype_args_val_def f) in
  let arg_types f = fst (Symbol.get_stype_args_val_def f) in
  (* sort first by arity, the symbol *)
  let funs = L.sort fun_cmp funs in
  let consts = L.filter (fun (c, a) -> a = 0 && val_type c = sort) funs in
  let nonconsts = L.filter (fun (f, a) -> a > 0 && val_type f = sort) funs in
  let tconsts = L.map (fun (c,_) -> add_term (T.create_fun_term c [])) consts in
  let rec sized sort size =
    try H.find ground_size_table (sort, size)
    with Not_found ->
      let rec tuples = function
        | [] -> [[]]
        | s :: ss ->
          let ts = upto_size s (size - 1) in
          L.concat (L.map (fun a -> L.map (fun t -> t :: a) ts) (tuples ss))
      in
      let gen_args (f, a) =
        let args = if a > size then [] else tuples (arg_types f) in
        L.map (fun ts -> add_term (T.create_fun_term f ts)) args 
      in
      let funs_of_sort = L.filter (fun (f, a) -> val_type f = sort && a < size) funs in
      let all = L.concat (L.map gen_args funs_of_sort) in
      let res = L.filter (fun t -> term_size t = size) all in
      H.add ground_size_table (sort, size) res;
      res
  and upto_size sort size =
    try H.find ground_upto_size_table (sort, size)
    with Not_found ->
      let res =
        if size <= 1 then tconsts
        else (upto_size sort (size - 1)) @ (sized sort size)
      in
      H.add ground_upto_size_table (sort, size) res;
      res
  in
  (* if there are only constant terms, term set is finite *)
  if nonconsts = [] then LL.of_list tconsts
  else 
    LL.concat (LL.of_function (fun i -> Some (LL.of_list (sized sort (i + 1)))))
;;

let rec fresh_vars away_var_list x n =
  let rec vars away_var_list x n =
    if n = 0 then []
    else
      let fresh_vars_env = Var.init_fresh_vars_env_away away_var_list in
      let y = Var.get_next_fresh_var fresh_vars_env (Var.get_type x) in 
      y :: (vars (y :: away_var_list) y (n-1))
  in
  vars away_var_list x n
;;

module Constraint = struct

  exception Is_unsat

  type atomic =
    | DiffVars of Var.var * Var.var
    | DiffTop of Var.var * Symbol.symbol 
  
  type t = atomic list list (* disjunction of conjunctions *)

  let empty = [[]]

  let atom a = [[a]]

  let pp_constraint ppf cs =
    let pp_atom (c, i) =
      if i > 0 then F.fprintf ppf " & ";
      match c with
      | DiffVars (x, y) -> F.fprintf ppf "%a != %a" Var.pp_var x Var.pp_var y
      | DiffTop (x, f) -> F.fprintf ppf "top(%a) != %a"
        Var.pp_var x Symbol.pp_symbol f
    in
    let pp_conj (c, i) =
      if i > 0 then F.fprintf ppf " | ";
      F.fprintf ppf "( ";
      List.iter pp_atom (index c);
      F.fprintf ppf " )"
    in
    match cs with
    | [[]] -> ()
    | [[a]] -> pp_atom (a, 0)
    | _ -> List.iter pp_conj (index cs)
  ;;

  let pp_clit ppf (l, constr) =
    F.fprintf ppf "%a | %a" pp_constraint constr T.pp_term l
  ;;

  let cmp_atomic s t =
    let cmp = function 
    | DiffVars(x,y), DiffVars(x',y') ->
      if (x = x' && y = y') || (x = y' && y = x') then 0 else pcmp (x,y) (x',y')
    | DiffTop(x, f), DiffTop(x', f') -> pcmp (x, f) (x', f')
    | DiffTop _, DiffVars _ -> 1
    | DiffVars _, DiffTop _ -> -1
    in cmp (s,t)
  ;;

  let atomic_equal s t = cmp_atomic s t = 0

  let eq_conj c1 c2 =
    let imp c c' = L.for_all (fun a -> L.exists (atomic_equal a) c') c in
    imp c1 c2 && imp c2 c1
  ;;

  let equal ct1 ct2 =
    let conj_subset c c' = L.for_all (fun a-> L.exists (atomic_equal a) c') c in
    let conj_equal c c' = conj_subset c c' && conj_subset c' c in
    let disj_subset ct = L.for_all (fun c -> L.exists (conj_equal c) ct) in
    disj_subset ct1 ct2 && disj_subset ct2 ct1
  ;;

  let cons a cs = if L.exists (atomic_equal a) cs then cs else a :: cs

  let conj1 c ct = List.map ((@) c) ct

  let conj ct1 ct2 = L.fold_right conj1 ct2 ct1

  let disj ct1 ct2 = ct1 @ ct2
    (*let disj1 d ds = if L.exists (eq_conj d) ds then ds else d :: ds in
    List.fold_right disj1 ct1 ct2*)
  ;;

  let substituted_satisfiable ct theta =
    let sat = function
      | DiffVars (x, y) -> (
        let tx = try Some (SubstM.find x theta) with _ -> None in
        let ty = try Some (SubstM.find y theta) with _ -> None in
        match tx, ty with
          | Some tx, Some ty -> tx <> ty
          | None, Some u -> (try x <> T.get_var u with _ -> true)
          | Some u, None -> (try y <> T.get_var u with _ -> true)
          | _ -> x <> y)
      | DiffTop (x, f) ->
        try T.get_top_symb (SubstM.find x theta) <> f with _ -> true
    in
    L.exists (fun c -> L.for_all sat c) ct
  ;;

  let substitute theta ct =
    (* Extend the constraint ct to include difference of terms s and t *)
    let rec add_terms_diff ct = function (* constrain two terms different *)
    | T.Var (z,_), T.Var (w,_) -> if w = z then [] else conj1 [DiffVars(z,w)] ct
    | (T.Fun (f, ts, _) as t), T.Var (x, _)
    | T.Var (x,_), (T.Fun (f, ts, _) as t) ->
      if L.mem x (T.get_vars t) then ct (* satisfied by occurs check *)
      else if L.for_all T.is_var ts then conj1 [DiffTop(x, f)] ct
      else
        let add_var x t acc = x :: (T.get_vars t) @ acc in
        let used_vars = add_var x t (Subst.fold add_var theta []) in
        let vs_new = fresh_vars used_vars x (L.length ts) in
        let vs_new' = L.map T.create_var_term vs_new in
        let diff_top = atom (DiffTop(x, f)) in
        let diff_arg = L.map (add_terms_diff ct) (zip vs_new' ts) in
        L.fold_left disj diff_top diff_arg (* difference on top or in arg *)
    | T.Fun (f, ss, _), T.Fun (g, ts, _) ->
      if f <> g then ct
      else L.fold_left disj [] (L.map (add_terms_diff ct) (zip ss ts))
    in
    let subst_atom = function
    | DiffVars (x, y) ->
      let tx = try (SubstM.find x theta) with _ -> T.create_var_term x in
      let ty = try (SubstM.find y theta) with _ -> T.create_var_term y in
      add_terms_diff [[]] (tx, ty)
    | DiffTop (x, f) ->
      match (try (SubstM.find x theta) with _ -> T.create_var_term x) with
      | T.Var (z, _) -> atom (DiffTop(z, f))
      | t -> add_terms_diff [[]] (t, T.create_var_term x)
    in
    let subst_conj = L.fold_left (fun ct a -> conj ct (subst_atom a)) empty in
    L.fold_left (fun ct' c -> disj ct' (subst_conj c)) [] ct
  ;;

  let rename rho =
    let app_rho = Var.apply_renaming rho in
    let ren = function
    | DiffVars (x, y) -> DiffVars (app_rho x, app_rho y)
    | DiffTop (x, f) -> DiffTop (app_rho x, f)
    in
    L.map (L.map ren)
  ;;

  let vars ct=
    let vars acc = function
    | DiffVars (x, y) ->
      let acc' =  if L.mem x acc then acc else x :: acc in
      if L.mem y acc' then acc' else y :: acc'
    | DiffTop (x, f) -> if L.mem x acc then acc else x :: acc
    in
    unique (L.fold_left (fun vs c -> L.fold_left vars vs c) [] ct)
  ;;

  let unsat funs cs =
    let val_type f = snd (Symbol.get_stype_args_val_def f) in
    let var_type_exhausted c x =
      let t = try Var.get_type x with _ -> failwith "var has no type" in
      let tfuns = L.filter (fun (f, _) -> val_type f = t) funs in
      assert (tfuns <> []);
      let rem = L.filter (fun (f, _) -> not (L.mem (DiffTop(x, f)) c)) tfuns in
      if rem <> [] && L.exists (fun (_,a) -> a > 0) rem then false
      else (* only constants remain for x, count if enough to satisfy diffvar *)
        let diff_x = function DiffVars (x',_) when x'=x -> true | _ -> false in
        L.length (unique (L.filter diff_x c)) >= L.length rem
    in
    let unsat = function DiffVars (x, y) ->  x = y | _ -> false in
    let vs = vars cs in
    let unsatc c = L.exists unsat c || L.exists (var_type_exhausted c) vs in
    L.for_all unsatc cs
  ;;

  (* project constraint to variable list *)
  let project vars =
    let project conj = function
      | DiffVars (x, y) as c ->
        if L.mem x vars && L.mem y vars then cons c conj else conj
      | DiffTop (x, f) ->
        if L.mem x vars then cons (DiffTop (x, f)) conj else conj
    in
    L.map (fun c -> L.fold_left project [] c)
  ;;

  let implies ct ct_implied =
    let impl_by c2 c1 = L.for_all (fun a-> L.exists (atomic_equal a) c1) c2 in
    L.for_all (fun c_implied -> L.exists (impl_by c_implied) ct) ct_implied
  ;;

  (* returns list of substitutions *)
  let negate away_vars ct =
    let neg = function
    | DiffVars (x, y) -> Subst.singleton x (T.create_var_term y)
    | DiffTop (x,f) ->
      let a = Sym.get_arity f in
      let xs = L.map T.create_var_term (fresh_vars away_vars x a) in
      Subst.singleton x (T.create_fun_term f xs)
    in
    let negate_conj c = L.map neg c in
    let option_add x t = function
      | Some s -> (try Some (Subst.add x t s) with _ -> None)
      | _ -> None
    in
    let union s1 s2 = Subst.fold option_add s1 (Some s2) in
    let add s ss s' = match union s s' with Some s1 -> s1 :: ss | _ -> ss in
    let add1 ss_ok s = L.fold_left (add s) [] ss_ok in
    let add_all ss_ok ss =
      L.fold_left (fun ss_ok2 s -> add1 ss_ok s @ ss_ok2) [] ss
    in
    L.fold_left add_all [Subst.create ()] (L.map negate_conj ct)
  ;;

end

module Ct = Constraint

(* Computes smallest ground instance of the given constraint literal.
  Raises Ct.Is_unsat if no such instance exists.
*)
let smallest_gnd_instance syms (lit, constr) =
  (*Format.printf "smallest ground instance %a?\n%!" Ct.pp_clit (lit, constr);*)
  let product xss =
    let cons_check ys acc (x, t) =
      if Ct.implies constr [[Ct.DiffTop(x, T.get_top_symb t)]] then acc
      else
        let clash (y,u) = Ct.implies constr [[Ct.DiffVars(x,y)]] && t=u in 
        if L.exists clash ys then acc
        else ((x, t) :: ys) :: acc
    in
    let cross xs = L.rev_map (fun ys -> L.fold_left (cons_check ys) [] xs) in
    let cross_conc xs yss = L.concat (cross xs yss) in
    let prod xss = LL.of_list (L.fold_right cross_conc xss [[]]) in
    let cutat i xs = LL.to_list (LL.take i xs) in
    LL.concat (LL.of_function (fun i -> Some (prod (L.map (cutat i) xss))))
  in
  let rec smallest argss =
    let args = try LL.hd argss with LazyList.Is_empty -> raise Ct.Is_unsat in
    let sub_empty = Subst.create () in
    let sigma = L.fold_left (fun s (x,u) -> Subst.add x u s) sub_empty args in
    let pred = Ct.substituted_satisfiable constr in
    (*F.printf "smallest? %a %B\n%!" T.pp_term
      (Subst.apply_subst_term term_db_ref sigma lit) (pred sigma);*)
    if pred sigma then Subst.apply_subst_term term_db_ref sigma lit
    else smallest (LL.tl argss)
  in 
  if T.is_ground lit then lit
  else if Ct.unsat syms constr then raise Ct.Is_unsat
  else
    let terms v = LL.map (fun t -> (v, t)) (all_ground_terms (Var.get_type v) syms) in
    smallest (product (L.map terms (T.get_vars lit)))
;;

(* SGGS stuff *)
type initial_interpretation = AllNegative | AllPositive

type constr_literal = Term.literal * Ct.t

module ConstrainedClause = struct
  type constr_clause = {
    clause: Clause.clause;
    selected: Term.literal;
    constr: Ct.t
  }

  let to_clit c = (c.selected, c.constr)

  let clause c = c.clause
  let selected c = c.selected
  let constr c = c.constr

  let get_vars c = unique (C.get_var_list c.clause @ (Ct.vars c.constr))

  let make c sel constr = { clause = c; selected = sel; constr = constr }

  let mk_singleton tstp_src lit constr =
    let _, rho = normalise_lit_list_renaming term_db_ref [lit] in
    let c = C.create_clause term_db_ref tstp_src [lit] in
    make c (L.hd (C.get_lits c)) (Ct.rename rho constr)
  ;;

  let pp_cclause ppf cc =
    if C.get_lits cc.clause == [] then F.fprintf ppf "[]"
    else
      if cc.constr <> [] then
        F.fprintf ppf "%a | " Ct.pp_constraint cc.constr;
      L.iter (fun (l, i) ->
        if i > 0 then F.fprintf ppf ", ";
        F.fprintf ppf (if l == cc.selected then "[%a]" else "%a") T.pp_term l;
      ) (index (C.get_lits cc.clause))
  ;;

  let equal cc cc' =
    (* FIXME: hash comparison may be partial *)
    let cls_cmp x y = pcmp (C.hash_bc x) (C.hash_bc y) in
    let term_cmp = T.hash cc.selected = T.hash cc'.selected in
    let constr_cmp = Ct.equal cc.constr cc'.constr in
    cls_cmp cc.clause cc'.clause = 0 && term_cmp && constr_cmp
  ;;

  let eq_upto_select cc cc' =
    if equal cc cc' then true
    else 
      let cls_cmp x y = pcmp (C.hash_bc x) (C.hash_bc y) in
      cls_cmp cc.clause cc'.clause = 0 && Ct.equal cc.constr cc'.constr
  ;;

  let substitute theta cc =
    let (lit, constr, clause) = cc.selected, cc.constr, cc.clause in
    let apply = Subst.apply_subst_term term_db_ref in
    let subst_lits = L.map (apply theta) (C.get_lits clause) in
    let _, rho = normalise_lit_list_renaming term_db_ref subst_lits in
    let c' = modify_clause clause subst_lits in
    let constr_subst = Ct.rename rho (Ct.substitute theta constr) in
    let constr_proj = Ct.project (C.get_var_list cc.clause) constr_subst in
    let rho' = Subst.var_renaming_to_subst term_db_ref rho in
    make c' (apply rho' (apply theta lit)) constr_proj
  ;;

end

module CC = ConstrainedClause

open CC

let pp_lits ppf ls =
  L.iter (fun (l, i) ->
    if i > 0 then F.fprintf ppf ", ";
    F.fprintf ppf "%a" T.pp_term l;
  ) (index ls)
;;

let pp_clause ppf cc = pp_lits ppf (C.get_lits cc)

let pp_clauses ppf ccs = L.iter (fun l -> F.fprintf ppf "%a\n" pp_clause l) ccs

let subst_str sub =
  let add x t l = 
    let k,v = x in
    (string_of_int k) ^ (Var.to_string v) ^ " -> " ^ (Term.to_string t) ^ l
  in
  SubstBound.SubstM.fold add sub ""
;;

let unifies t u =
  try let _ =  Unif.unify_bterms (1, t) (2, u) in true
  with Unif.Unification_failed -> false
;;

let unify clauselit traillit =
  let mgu = Unif.unify_bterms (1, clauselit) (2, traillit) in
  let add x t l = if fst x = 2 then Subst.add (snd x) (snd t) l else l in
  let sigma = SubstBound.SubstM.fold add mgu (Subst.create ()) in
  sigma
;;

(* Unif.unify_bterms is wrong *)
let unify_var_disj clauselit traillit = mgu_list [(clauselit, traillit)]
(*  let mgu = Unif.unify_bterms (1, clauselit) (2, traillit) in
  let add x t l = Subst.add (snd x) (snd t) l in
  let sigma = SubstBound.SubstM.fold add mgu (Subst.create ()) in
  sigma, mgu
;;*)

let rename_term vars t = 
  let rho, ts = rename_term_list term_db_ref vars [t] in
  rho, L.hd ts
;;

exception Split_undefined

(* second argument is representative, in particular, an instance of first clause
   with stronger constraint. *)
let diff cc by_cc sigma =
  (* representative never changes in recursion *)
  let r, constr_r = CC.selected by_cc, CC.constr by_cc in
  let vars_r = T.get_vars r in

  let rec diff acc i cc =
    let (s, constr_s, clause_s) = CC.selected cc, CC.constr cc, CC.clause cc in
    (* DiffSim *)
    let sigma = ensure_match s r in
    let vars_s = T.get_vars s in
    let away = vars_s @ vars_r in
    let osubst x = try Some (x, SubstM.find x sigma) with _ -> None in
    let map_to p o x =
      match osubst x with Some y when p (snd y) -> Some y | _ -> o
    in
    (* check if some var is mapped to functional term *)
    match L.fold_left (map_to (not <.> T.is_var)) None vars_s with
    | Some (x, T.Fun(f, ts, _)) ->
      let xs = L.map T.create_var_term (fresh_vars away x (L.length ts)) in
      let tau = Subst.singleton x (T.create_fun_term f xs) in
      let cc_sub = CC.substitute tau cc in
      let constr_s' = Ct.conj (Ct.atom (Ct.DiffTop(x, f))) constr_s in
      diff ((CC.make clause_s s constr_s') :: acc) i cc_sub
    | _ -> 
      let also_mapped_to x z y =
        x <> y && (match osubst y with Some (_, Var(x',_)) -> z=x' | _ -> false)
      in
      let check x =
        let xt = T.create_var_term x in
        let t = Subst.apply_subst_term term_db_ref sigma (add_term xt) in
        if not (T.is_var t) then None
        else if L.exists (also_mapped_to x (T.get_var t)) vars_s then
          let y = L.find (also_mapped_to x (T.get_var t)) vars_s in
          Some(x,y)
        else None
      in
      let to_same_var = list_opt_fold check None vars_s in
      match to_same_var with
      | Some (x, y) ->
      (* DiffVar: two variables x, y are mapped to same var z  *)
        let tau = Subst.singleton x (T.create_var_term y) in
        let cc_subst = CC.substitute tau cc in
        let constr_s' = Ct.conj (Ct.atom (Ct.DiffVars(x,y))) constr_s in
        diff (CC.make clause_s s constr_s' :: acc) i cc_subst
      | _ ->  (* remaining cases *)
      (* apply DiffId: since the second clause is an instance of the first, but
        no variable in vars_s is mapped to a functional term and no two 
        variables in vars_s are mapped to the same term, (s, constr_s, clause_s)
        must be a variant of (r, constr_r, clause_r) *)
        if i > 50 then failwith "FIXME: looping split";
        let cc_sigma = CC.substitute sigma cc in
        (* DiffElim *)
        if CC.equal cc cc_sigma then
          if s = r && not (Ct.implies constr_s constr_r) then (
            (*let cs = L.fold_right (remove Ct.eq_conj) constr_s constr_r in*)
            let subs = Ct.negate (CC.get_vars cc) constr_r in
            let subs' = L.filter (Ct.substituted_satisfiable constr_s) subs in
            let ccs = L.map (fun sigma -> CC.substitute sigma cc) subs' @ acc in
            ccs
          ) else acc
        else diff acc (i+1) cc_sigma
  in diff [] 0 cc
;;

(* Implementation of term comparison \succ in SGGS paper.
  Assumes that l and l' are ground.
  Implements KBO where every symbol has weight 1 (hence the created ordering
  extends the size ordering), and the precedence is given by fun_cmp, which
  first compares first by arity and then by Sym.compare.
*)
let sggs_cmp l l' =
  let rec kbo (s,t) =
    let sz_s, sz_t = term_size s, term_size t in
    if  sz_s <> sz_t then pcmp sz_s sz_t
    else
      let f, ss = T.get_top_symb s, T.get_args s in
      let g, ts = T.get_top_symb t, T.get_args t in
      if f <> g then fun_cmp (f, L.length ss) (g, L.length ts) 
      else L.fold_left2 (fun c si ti -> if c<>0 then c else kbo (si,ti)) 0 ss ts
  in
  assert (T.is_ground l && T.is_ground l');
  kbo (T.get_atom l, T.get_atom l')
;;

(* split s clause by t clause, rep is optional representative *)
let split_clauses ?(rep=None) syms cc by_cc =
  let by_lit = by_cc.selected in
  let by_constr = Ct.project (T.get_vars by_lit) by_cc.constr in
  let s, t = T.get_atom (CC.selected cc), T.get_atom by_lit in
  let constr_s, clause_s = CC.constr cc, CC.clause cc in
  (* If no representative is given: the representative of D in split(C,D) is 
  Aσ ∧ Bσ | C[L]σ, where σ is the mgu of at(L) and at(M) and (A∧B)σ is 
  satisfiable.*)
  let rho, t' = rename_term (CC.get_vars cc) t in
  (*if !O.current_options.dbg_backtrace then
    Format.printf "SPLIT %a by %a, renamed %a\n" CC.pp_cclause cc Ct.pp_clit 
      (by_lit, by_constr) T.pp_term t';*)
  try
    let sigma = unify_var_disj s t' in
    let constr = Ct.conj (Ct.substitute rho by_constr) constr_s in
    if not (Ct.substituted_satisfiable constr sigma) then raise Split_undefined
    else (
      (* compute the representative, if not given *)
      (* FIXME: following substitution needed? *)
      let cc' = { cc with CC.constr = Ct.substitute sigma constr } in 
      let rep = match rep with Some r -> r | None -> CC.substitute sigma cc' in
      (* the difference *)
      let diff = diff cc rep sigma in
      assert (L.for_all (fun cc -> cc.constr <> []) diff);
      (*if !O.current_options.dbg_backtrace then (
        Format.printf "  representative %a \n" CC.pp_cclause rep;
        Format.printf "  difference:\n");*)
      let small_inst cc = smallest_gnd_instance syms (cc.selected, cc.constr) in
      (* add flag for representative *)
      let partition = rep :: diff in
      let instance cs c = try (c,small_inst c)::cs with Ct.Is_unsat -> cs in
      let partition = L.fold_left instance [] partition in
      let partition = L.sort (fun (_, s) (_, t) -> sggs_cmp s t) partition in
      (*F.printf "sorted:\n";
      L.iter (fun (cc, l) ->
        F.printf "  %a (for %a)\n%!" pp_cclause cc T.pp_term l
      ) partition;*)
      L.map fst partition, rep, diff)
  with Unif.Unification_failed -> raise Split_undefined
;;

(* whether Gr(t_constr | t) is contained in  Gr(p_constr | p) *)
let gnd_instance_subset (t, constr_t) (p, constr_p) =
  let constr_t = Ct.project (T.get_vars t) constr_t in
  let constr_p = Ct.project (T.get_vars p) constr_p in
  try 
    let theta = Unif.matches p t in
    if not (Ct.substituted_satisfiable constr_p theta) then false
    else Ct.implies constr_t (Ct.substitute theta constr_p)
  with Unif.Matching_failed -> false
;;

let covers pat_clit clit = gnd_instance_subset clit pat_clit

(* Whether Gr(t_constr | t) and  Gr(p_constr | p), considering sign. *)
let gnd_instance_inter (t, constr_t) (s, constr_s) =
  let constr_t = Ct.project (T.get_vars t) constr_t in
  let constr_s = Ct.project (T.get_vars s) constr_s in
  let vars = unique (Ct.vars constr_s @ variables s) in
  let rho, t' = rename_term vars t in
  let constr_t' = Ct.substitute rho constr_t in
  try 
    (*F.printf "intersect: %a (is %a) vs %a\n%!"
    Ct.pp_clit (t,constr_t) Ct.pp_clit (t',constr_t') Ct.pp_clit (s,constr_s);*)
    let theta = mgu_list [s,t'] in
    let constr = Ct.conj constr_t' constr_s in
    Ct.substituted_satisfiable constr theta
  with Unif.Unification_failed -> false
;;

let at_gnd_instance_inter (t, ct) (s, cs) =
  gnd_instance_inter (T.get_atom t, ct) (T.get_atom s, cs)
;;

module PartialInterpretation = struct
  type t = {
    default: initial_interpretation;
    constr_lits: constr_literal list 
  }

  let get_constr_lits i = i.constr_lits
  let get_default i = i.default

  (* Whether constr_lits (presumably on the trail) satisfy l, where the latter
     may be constrained by lconstr.
     Assumption: interpretation is not contradictory, i.e. dp(Gamma) = Gamma *)
  let trail_sat_lit ?(lconstr = Ct.empty) constr_lits l =
    let sl = Term.get_sign_lit l in
    (* search from back of trail for some matching literal *)
    let update_val ((lp_lit, lp_constr) as lp) = function
    | None ->
      let slp = Term.get_sign_lit lp_lit in
      if covers lp (l, lconstr) then Some true
      else if sl <> slp && covers lp (compl_lit l, lconstr) then Some false
      else None
    | some_val -> some_val
    in 
    L.fold_right update_val constr_lits None
  ;;

  let satisfies_lit ?(constr = Ct.empty) interp l =
    let sl = T.get_sign_lit l in
    let initial_val l = function AllPositive -> sl | AllNegative -> not sl in
    match trail_sat_lit ~lconstr:constr interp.constr_lits l with
    | Some v -> v
    | None -> initial_val l interp.default
  ;;
  
  let from_trail init trail =
    let ls = L.map (fun cc -> (CC.selected cc, CC.constr cc)) trail in
    { default = init; constr_lits = ls}
  ;;

  let is_init_all_true init l =
    (init = AllPositive && Term.get_sign_lit l) ||
    (init = AllNegative && not (Term.get_sign_lit l))
  ;;
end

module I = PartialInterpretation

module Trail = struct
  type t = CC.constr_clause list
end

exception No_dependence of constr_literal

type state = {
  conflicts: int ref;
  deleted_clauses: int ref;
  extensions: int ref;
  generated_clauses: int ref;
  initial: initial_interpretation;
  max_trail_len: int ref;
  trail: Trail.t;
  trail_idx: CC.constr_clause DiscTree.t;
  steps: int ref;
  ground_preserving: bool;
  signature : (Sym.t * int) list;
  finite_base: bool;
  extension_queue: (C.clause * Ct.t) list option
}

let mk_initial_state init gp syms = 
  let funas = L.map (fun f -> (f,Sym.get_arity f)) (L.filter Sym.is_fun syms) in
  let epr = L.for_all (fun (_,a) -> a = 0) funas in
  {
  conflicts = ref 0;
  deleted_clauses = ref 0;
  extensions = ref 0;
  generated_clauses = ref 0;
  initial = init;
  max_trail_len = ref 0;
  trail = [];
  trail_idx = DiscTree.create ();
  steps = ref 0;
  ground_preserving = gp;
  signature = funas;
  finite_base = epr;
  extension_queue = None
}

let is_I_all_true state l = (state.initial = AllPositive) = (T.get_sign_lit l)

let is_I_all_false state l = (state.initial = AllPositive) <> (T.get_sign_lit l)

let is_I_all_true_clause state c =L.for_all (is_I_all_true state) (C.get_lits c)

let pp_trail ppf state =
  L.iter (fun (c, i) -> F.fprintf ppf "  %d: %a\n" i CC.pp_cclause c)
    (index state.trail);
;;

let log_step state step_name =
  if !O.current_options.dbg_backtrace then (
    F.printf "\nGamma_%d: (%s)\n%a" !(state.steps) step_name pp_trail state;
    F.printf "\n%!");
  state.steps := !(state.steps) + 1;
  state.max_trail_len := max !(state.max_trail_len) (L.length state.trail)
;;

let print_stats state =
  F.printf "\n# steps:             %d\n" !(state.steps);
  F.printf "# extensions:        %d\n" !(state.extensions);
  F.printf "# conflicts:         %d\n" !(state.conflicts);
  F.printf "# generated clauses: %d\n" !(state.generated_clauses);
  F.printf "# deleted clauses:   %d\n" !(state.deleted_clauses);
  F.printf "max trail length:    %d\n" !(state.max_trail_len);
  F.printf "time:                %.2f\n" (Unix.gettimeofday () -. !start_time)
;;

let log_step_if b state step_name = if b then log_step state step_name else ()

let inc_clauses state = state.generated_clauses := !(state.generated_clauses) +1

let inc_clauses_and_extensions state =
  state.extensions := !(state.extensions) + 1;
  inc_clauses state
;;

let insert x ys pos = 
  let l = until pos ys @ [x] @ (from pos ys) in
  assert (L.length l == L.length ys + 1);
  l
;;

let empty_cache state = {state with extension_queue = None} 

let is_disposable cc state =
  if C.get_lits cc.clause = [] then false
  else (
    let b = L.exists (fun lt -> 
    covers (CC.to_clit lt) (CC.to_clit cc)
    ) state.trail in
    (*if b then
      F.printf "dispose %a because of %a\n%!" pp_cclause cc pp_cclause
        (L.find (fun l -> covers (CC.to_clit l) (CC.to_clit cc)) state.trail));*)
    b)
;;

let delete_idx idx l cc =
  if DiscTree.in_unif_index idx l then DiscTree.elim_elem_from_lit idx l cc
;;

let reorder_state state trail_new = { state with trail = trail_new }

(* 
Walks back along the trail in state to find a literal which l depends on, i.e.,
a selected literal (l')^d such that l is an instance of l'.
Fails if no dependence found.
FIXME: this differs from the paper definition of dependence, where only
       contributing instances are counted 
*)
let find_dependence trail (l, l_constr) maybe_split =
  let lc = compl_lit l, l_constr in
  let check_dep (tl_cls, i) = function
    | None ->
      let lc_trail = (tl_cls.selected, tl_cls.constr) in
      if gnd_instance_subset lc lc_trail then Some (l, fst lc_trail,i) else None
    | some_r -> some_r
  in
  match L.fold_right check_dep (index trail) None with
  | None -> 
    (*F.printf "%a has no dependence\n%!" Ct.pp_clit (l, l_constr);*)
    raise (No_dependence (l, l_constr))
  | Some r -> r
;;

(* l_ind is the independent (left) literal, l_dep is the dependent (right) one*)
let depends_only_on state (l_ind, c_ind, pos) ((l_dep, c_dep) as cl_dep) =
  let bef = until pos state.trail in
  let nodep l = (* try to find other dependence before*)
    try let _ = find_dependence bef cl_dep false in false with _ -> true
  in
  covers (l_ind, c_ind) (compl_lit l_dep, c_dep)
  && is_I_all_true state l_dep && nodep l_dep
;;

(*
Remove all clauses in cs whose selected literal is assigned to l (used after
resolve), and do so recursively also for deleted clauses.
pos is one past position of last inserted partition element in case of split.
*)
let remove_assigned_to (l, lcnstr, pos) state is_split =
  let aft = from (if is_split then pos else pos + 1) state.trail in
  (* the literal l here may not be l above due to recursive removal *)
  let assigned_to_l (l, lc) c =
    let ls = C.get_lits c.clause in
    (* pass position pos to depends_only_on: search only for dependences before
       pos; at most too many clauses are thrown out - should not be a problem *)
    L.exists (fun t -> depends_only_on state (l, lc, pos) (t, c.constr)) ls 
  in
  let rec remove lc = function
    | [] -> []
    | c :: cs ->
      if not (assigned_to_l lc c) then c :: (remove lc cs)
      else (
        ignore (delete_idx state.trail_idx c.selected c);
        state.deleted_clauses := !(state.deleted_clauses) + 1;
        (*Format.printf "  delete assigned %a\n%!" pp_clause c.clause;*)
        remove lc (remove (CC.to_clit c) cs))
  in remove (l, lcnstr) aft
;;

exception Invariant_invalid

let has_dependence state (l,constr) = 
  try let _ = find_dependence state.trail (l, constr) false in true
  with No_dependence _ -> false
;;

let is_conflicting state cc =
  let compl_cc = (compl_lit cc.selected, cc.constr) in
  let inter c = gnd_instance_inter compl_cc (CC.to_clit c) && c <> cc in
  let is_conf = L.exists inter state.trail in 
  if is_conf then
    state.conflicts := !(state.conflicts) + 1;
  is_conf
;;

let check_invariants state =
  (* 1. Check that there are no conflicts*)
  let check_clause (c, i) trail_until_c =
    let state_c = {state with trail = trail_until_c} in
    let ls = C.get_lits c.clause in
    (* if a clause has I-false literals then one is selected *)
    (*let fls = L.filter (fun l -> is_I_all_false l state) ls in
    if (fls <> []) && not (is_I_all_false c.selected state) then (
      F.printf "\n  no I-false literal selected in %a\n%!" pp_clause c.clause;
      raise Invariant_invalid);*)
    (* conflict exists *)
    let check_conflict trl cc =
      L.iter (fun cc' ->
        if gnd_instance_inter (CC.to_clit cc) (CC.to_clit cc') then (
          F.printf "%a and %a are intersecting\n%!" Ct.pp_clit (CC.to_clit cc) 
            Ct.pp_clit (CC.to_clit cc');
          raise Invariant_invalid)
      ) trl;
      trl @ [cc]
    in ignore (L.fold_left check_conflict [] state.trail);
    (* 2. Check that selected literals are in index *)
    L.iter (fun cc -> 
      let in_idx = DiscTree.in_unif_index state.trail_idx cc.selected in
      if not in_idx then F.printf "%a is not indexed\n%!" CC.pp_cclause cc;
      assert (in_idx);
    ) state.trail;
    (* 3. Non-selected I-true literals must be assigned *)
    let tls = L.filter (fun l -> is_I_all_true state l) ls in
    let unsel_tls = L.filter (fun l -> l <> c.selected) tls in
    let check l =
      if not (has_dependence state_c (l, c.constr)) then (
        F.printf "\n  %d: %a | %a in %a has no dependence\n%!" i
          Ct.pp_constraint c.constr T.pp_term l pp_clause c.clause;
        raise Invariant_invalid)
    in L.iter check unsel_tls
  in
  let rec check i = function
    | [] -> ()
    | c :: bef_rev -> check_clause (c, i) (L.rev bef_rev); check (i - 1) bef_rev
  in check (L.length state.trail - 1) (L.rev state.trail);
;;

(*
For a conflict clause conflict_lits, find last literal in trail that a literal
in conflict_lits depends on.
Returns a (conflict_literal, literal, position) triple.
*)
let find_last_dependence state (conflict_clause, constr) =
  let cls = C.get_lits conflict_clause in
  let deps = L.map (fun l -> find_dependence state.trail (l,constr) true) cls in
  let cmp (cm, lm, m) (ci, li, i) = if m > i then (cm,lm,m) else (ci,li,i) in
  L.fold_left cmp (L.hd deps) (L.tl deps)
;;

let mk_cclause c l constr = 
  let ls = C.get_lits c in
  if ls = [] then
    { clause = c; selected = l; constr = constr}
  else (
    assert (ls = [] || L.mem l ls);
    { clause = c; selected = l; constr = constr })
;;

(* Check for I-true constrained clauses in state occurring after from_pos
whether the selected literal is still the one assigned to rightmost index. *)
let update_selection_from from_opt (state, from_pos) =
  let comes_from = match from_opt with
  | Some (l, c) -> fun cc -> covers (compl_lit l, c) (CC.to_clit cc)
  | _ -> fun _ -> true
  in
  let update cc =
    if not (comes_from cc && is_I_all_true_clause state cc.clause) then cc, false
    else (
      try
        let sel, _, i = find_last_dependence state (cc.clause, cc.constr) in
        let cc' = {cc with selected = sel} in
        if sel <> cc.selected then (
          (*F.printf "update %a to %a dep on %d\n%!" CC.pp_cclause cc
            T.pp_term sel i;*)
          DiscTree.elim_elem_from_lit state.trail_idx cc.selected cc;
          DiscTree.add_elem_to_lit state.trail_idx sel cc'
        );
        cc', true
      with No_dependence _ -> (* selected literal may have no dependence*)
        cc, false
      )
  in
  let bef = until from_pos state.trail in
  let aft = L.map update (from from_pos state.trail) in
  let changed = L.exists snd aft in
  let state' = {state with trail = bef @ L.map fst aft} in
  if changed then empty_cache state' else state'
;;
  
  let add_clause_to_trail cc state pos =
    let bef, aft = until pos state.trail, from pos state.trail in
    if is_disposable cc {state with trail = bef} then state, false
    else (
      let covered lt = covers (CC.to_clit cc) (lt.selected, lt.constr) in
      let aft', del = L.partition (fun c -> not (covered c)) aft in
      let idx = state.trail_idx in
      L.iter (fun cc' -> ignore (delete_idx idx cc'.selected cc')) del;
      let state = if del <> [] then empty_cache state else state in
      DiscTree.add_elem_to_lit idx cc.selected cc;
      let state' = { state with trail = bef @ [cc] @ aft'; trail_idx = idx } in
      update_selection_from None (state', pos + 1), true)
  ;;
  
  let remove_from_trail state pos =
    let cc_old = state.trail <!> pos in
    let idx = state.trail_idx in
    DiscTree.elim_elem_from_lit idx cc_old.selected cc_old;
    let bef, aft = until pos state.trail, from (pos + 1) state.trail in
    empty_cache {state with trail = bef @ aft}
  ;;

let variant s t = matches s t && matches t s

(* return the substituted clause and the substituted constraints.
  Note that to constr0 (the original constraints) the substitution is applied,
  while to constr1, the new splitting consraints only the renaming.  *)
let subst_clause theta c (constr0, constr1) =
  let apply_theta = Subst.apply_subst_term term_db_ref theta in
  let subst_lits = L.map apply_theta (C.get_lits c) in
  let _, rho = normalise_lit_list_renaming term_db_ref subst_lits in
  (* normalizing substitution also needs to be applied to constraints *)
  let c' = modify_clause c subst_lits in
  (*F.printf "subst %a to %a: now constraint %a\n%!" C.pp_clause c C.pp_clause c'
    Ct.pp_constraint constr0;*)
  let constr0' = Ct.substitute theta constr0 in
  let constr' = Ct.rename rho (Ct.conj constr0' constr1) in
  c', constr'
;;

let find_splitting_opportunity trail_lits cs =
  (* return substitution useful for split *)
  let check_lit (trail_lit, i) l =
    try
      let theta = unify (compl_lit l) trail_lit in
      if matches (compl_lit l) trail_lit then None
      else
        Some (i, theta)
    with Unif.Matching_failed | Unif.Unification_failed -> None
  in
  let check_trail_lit acc tl = 
    if acc <> None then acc
    else
      let check_clause acc c = 
        if acc <> None then acc
        else
          let ls = C.get_lits c in
          L.fold_left (fun a l -> if a=None then check_lit tl l else a) None ls
      in
    L.fold_left check_clause None cs
  in
  L.fold_left check_trail_lit None (index trail_lits)
;;

(*
Repeatedly extend the set of clauses cs by instances C.theta of a clause C in cs
such that l.theta occurs in interp (the trail).
The returned set of clauses are candidates for conflict clauses.
*)
let add_intersecting_instances state cs =
  match state.extension_queue with
  | Some q -> q, false
  | None -> (
  let ground_pres = state.ground_preserving in
  let vars_lits = L.fold_left (fun acc l -> T.get_vars l @ acc) [] in
  (* Instantiations of literal linst to (negation of) trail literal. Returns
     list of satisfiable (substitution, constraint) pairs. 
     vars are variables used in clause instance, to be renamed away from *)
  let inst_lit linst vars = 
    let clinst = compl_lit linst in
    let check_cclause acc cc =
        try
          let trail_lit, trail_constr = cc.selected, cc.constr in
          let rho, trail_lit' = rename_term vars trail_lit in
          (* unify does not work: f(X, f(Y, X)) vs f(U, f(U, V)), so use mgu *)
          let theta = mgu_list [trail_lit', clinst] in
          let trail_constr' = Ct.substitute rho trail_constr in
          if not (Ct.substituted_satisfiable trail_constr' theta) then acc
          else (theta, Ct.substitute theta trail_constr') :: acc
        with _ -> acc
    in
    let unif_tlits = DiscTree.get_unif_candidates state.trail_idx clinst in
    L.fold_left check_cclause [] (L.fold_left (@) [] (L.rev_map snd unif_tlits))
  in
  let ext_clause c = (* c is in given clause set S *)
    let rec ext (unsubsted, substed, constrs) =
      match unsubsted with
      | [] ->
        let c' = modify_clause c substed in
        let _, rho = normalise_lit_list_renaming term_db_ref substed in
        let constrs' = Ct.project (C.get_var_list c') (Ct.rename rho constrs) in
        if ground_pres && not (C.is_ground c') then [] else [c', constrs']
      | u :: us ->
        let app acc (theta, trail_constr) =
          let apply_theta = Subst.apply_subst_term term_db_ref theta in
          if not (Ct.substituted_satisfiable constrs theta) then acc
          else
            let constrs' = Ct.conj trail_constr (Ct.substitute theta constrs) in
            let substed' = apply_theta u :: (L.map apply_theta substed) in
            let inst = (L.map apply_theta us, substed', constrs') in
            inst :: acc
        in
        let vars = vars_lits (unsubsted @ substed) in
        let insts = L.fold_left app [] (inst_lit u vars) in
        let insts' =
          if is_I_all_true state u then insts
          (* I-all-false literals do no have to be instantiated *)
          else insts @ [(us, u :: substed, constrs)]
        in
        L.concat (L.map ext insts')
    in
    (* instantiate both I-all-true literals (see SGGS extension scheme) and
    I-all-false ones, to reflect extension substitution in extension 2. But
    I-all-false ones do not have to be instantiated. *)
    ext (C.get_lits c, [], Ct.empty)
  in
  let csx = L.concat (L.map ext_clause cs) in
  let cls_cmp x y = pcmp (C.hash_bc x) (C.hash_bc y) in
  let csx = unique ~c:(fun (c,_) (c',_) -> cls_cmp c c') csx in
  (*if !O.current_options.dbg_backtrace then (
    F.printf "potential extension instances:\n";
      L.iter (fun (c,constr) -> F.printf "  %a | %a\n%!"
        Ct.pp_constraint constr pp_clause c) csx);*)
  let csx_sizes = L.map (fun c -> c, clause_size (fst c)) csx in
  L.map fst (L.sort (fun (_, s) (_, s') -> pcmp s s') csx_sizes), true)
;;

(* pcgi(A|L, Γ A|C[L]) = 0  *)
let rec pcgi_empty state (lit, constr) =
  let covers c = covers c (lit, constr) || covers c (compl_lit lit, constr) in
  if L.exists (fun c -> covers (CC.to_clit c)) state.trail then
    true
  else
    let gmatch (l,c) =
      let l, lit = T.get_atom l, T.get_atom lit in
      not (matches l lit) && gnd_instance_inter (lit, constr) (l,c)
    in
    try 
      let by_cc = L.find (fun c -> gmatch (CC.to_clit c)) state.trail in
      let tstp_src = C.tstp_source_global_subsumption 0 by_cc.clause in
      (* variables not occurring in literal cause problems with renaming *)
      let constr' = Ct.project (T.get_vars lit) constr in
      let by_cc = {by_cc with constr = Ct.project (T.get_vars by_cc.selected) by_cc.constr} in
      let cc = mk_singleton tstp_src lit constr' in
      let parts, _, _ = split_clauses state.signature cc by_cc in
      let chk_pt cc = pcgi_empty state (T.get_atom cc.selected, cc.constr) in
      L.for_all chk_pt parts
    with Not_found -> 
    if state.finite_base then (
      try let _ = smallest_gnd_instance state.signature (lit, constr) in false
      with Ct.Is_unsat -> true)
    else false
;;

(* at(Gr(lit_constr|lit)) subset at(pcgi(tlit_constr|tlit, Γ)) where 
   (tlit, tlit_constr) is  Γ|_i. *)
let at_gnd_instance_subset_pcgi (state, i) (lit, constr)  =
  let lit = T.get_atom lit in
  let c = state.trail <!> i in
  let tlconstr = (T.get_atom c.selected, c.constr) in
  if not (covers tlconstr (lit, constr)) then false
  else
    let no_intersect j = 
      let cc = state.trail <!> j in
      (* assume that at_gnd_instance_subset_pcgi j state is checked separately.
      So either the ith clause does not intersect with the jth, or if it does,
      want that (lit,constr) does not, so that the relevant pcgis are produced*)
      not (gnd_instance_inter tlconstr (T.get_atom cc.selected, cc.constr)) ||
      not (gnd_instance_inter tlconstr (lit, constr))
    in
    L.for_all no_intersect (range 0 i)
;;

let gnd_instance_subset_pcgi (state, i) (lit, constr)  =
  let c = state.trail <!> i in
  let tlconstr = (c.selected, c.constr) in
  if not (covers tlconstr (lit, constr)) then false
  else
    let no_intersect j = 
      let cc = state.trail <!> j in
      not (gnd_instance_inter tlconstr (T.get_atom cc.selected, cc.constr)) ||
      not (gnd_instance_inter tlconstr (lit, constr))
    in
    L.for_all no_intersect (range 0 i)
;;

(* Given state and candidate clause with constraint, checks whether SGGS can
   extend with this clause.
   Returns (conflict,l) option: None means no extension is possible; otherwise,
   return a boolean saying whether the extension is conflicting, and a literal
   to be selected.
*)
let check_valid_extension state (c, constr) =
  let ip = I.from_trail state.initial state.trail in
  let sat = L.exists (I.satisfies_lit ~constr:constr ip) (C.get_lits c) in
  (* FIXME: avoid generating satisfied extension clauses in the first place *)
  if Ct.unsat state.signature constr || sat then None
  else (
  (* 1. SGGS-extension with I-all-true conflict clause. Select literal assigned
     to largest index *)
  if is_I_all_true_clause state c then (
    (*F.printf "EXTENSION 1: %a %a\n%!" Ct.pp_constraint constr C.pp_clause c;*)
    let dep_lit, _, _ = find_last_dependence state (c, constr) in
    Some((c, constr), true, dep_lit))
  else (
  (* 2. SGGS-extension with non-I-all-true conflict clause: c is not I-all-true,
  substitution has already been applied. *) 
  let ls = C.get_lits c in
  let flits =L.map (fun l -> (l,constr)) (L.filter (is_I_all_false state) ls) in
  let is_dependent = has_dependence state in
  let all_dep = L.for_all is_dependent flits in
  if all_dep then (
    (*F.printf "EXTENSION 2: %a %a\n%!" Ct.pp_constraint constr C.pp_clause c;*)
    Some ((c, constr), true, fst (L.find is_dependent flits)))
  (* 3. Non-conflicting non-critical SGGS-extension *)
  else (
    let sellits = if flits <> [] then L.map fst flits else ls in
    let selectable l =
      if pcgi_empty state (l, constr) then false
      else (
        (*F.printf "pcgis exist\n%!";*)
        let unc i = not (at_gnd_instance_subset_pcgi (state, i) (l,constr)) in
        L.for_all unc (range 0 (L.length state.trail)))
    in
    try
      let sel = L.find selectable sellits in
      (* non-selected I-true literals must be assigned *)
      let truerest = L.filter (fun l -> l <> sel && is_I_all_true state l) ls in
      if not (L.for_all (fun l -> is_dependent (l, constr)) truerest) then None
      else (
        (*F.printf "EXTENSION 3: %a %a\n%!" Ct.pp_constraint constr C.pp_clause c;*)
        Some((c, constr), false, sel))
    (* 4. FIXME critical SGGS-extension *)
    with Not_found -> None
  )
))
;;

exception Disposable

(* Used to obtain selected literal in clause resulting from SGGS-resolve.
   pos is position of insertion, state does not contain c.
   Returns pair (conflict, lit) of selected literal and whether its insertion
   causes a conflict.
   Raises Disposable if clause c is satisfied.
*)
let find_selected (state, pos) (c, constr) =
  let ip = I.from_trail state.initial state.trail in
  let sat = L.exists (I.satisfies_lit ~constr:constr ip) (C.get_lits c) in
  if sat then raise Disposable;

  let stater = { state with trail = until pos state.trail} in
  let ls = C.get_lits c in
  (* 1. I-all-true: Select unassigned or literal assigned to largest index *)
  if is_I_all_true_clause stater c then (
    try (false, L.find (fun l -> not (has_dependence stater (l, constr))) ls)
    with Not_found -> (* all literals have dependence: take assigned rightmost*)
      let dep_lit, _, _ = find_last_dependence stater (c, constr) in
      (true, dep_lit)
    )
  else (
  (* 2. non-I-all-true conflict clause: select I-false literal *) 
  let flits=L.map (fun l -> (l,constr)) (L.filter (is_I_all_false stater) ls) in
  let all_dep = L.for_all (has_dependence stater) flits in
  if all_dep then (true, fst (L.find (has_dependence stater) flits))
  (* 3. not necessarily non-conflicting *)
  else (
    let sellits = L.map fst flits in (* there are I-false lits, select one *)
    let preferred_selected l = 
      let gnd_ss i = at_gnd_instance_subset_pcgi (stater,i) (l,constr) in
      if pcgi_empty stater (l, constr) then false
      else L.for_all (fun (_, i) -> not (gnd_ss i)) (index stater.trail)
    in
    (* this selection may result in a disposable clause *)
    let sel = try L.find preferred_selected sellits with _ -> L.hd sellits in
    let intersecting cl = gnd_instance_inter (compl_lit sel, constr) cl in
    let conflict = L.exists intersecting (L.map CC.to_clit state.trail) in
    (conflict, sel)
    )
  )
;;

let has_dependent state pos =
  let dep_on_pos cc =
    let ls = L.filter (fun l -> is_I_all_true state l) (C.get_lits cc.clause) in
    let dep_lit l = 
      try let _,_,i = find_dependence state.trail (l,cc.constr) false in i = pos
      with _ -> false
    in
    L.exists dep_lit ls
  in
  L.exists dep_on_pos (from (pos + 1) state.trail)
;;

(* Assumes that the selected literal in state[pos] depends on state[dep_pos];
   checks whether there is another literal in the clause state[pos] which
   has the same dependency. Used to trigger factorization or left splitting. *)
let shares_dependency state dep_pos pos =
  let ccd = state.trail <!> dep_pos in (* dependee *)
  let cc = state.trail <!> pos in (* dependent *)
  let atd, at = T.get_atom ccd.selected, T.get_atom cc.selected in
  if not (covers (atd, ccd.constr) (at, cc.constr)) then None
  else (
    let ls = C.get_lits cc.clause in
    assert (L.exists (fun l -> cc.selected == l) ls);
    let lcp = (ccd.selected, ccd.constr,dep_pos) in
    let depends_only l = depends_only_on state lcp (l, cc.constr) in
    try Some (L.find (fun l -> not (l == cc.selected) && depends_only l) ls)
    with _ -> None
  )
;;

let factorizable state dep_pos pos =
  match shares_dependency state dep_pos pos with
  (* unification check is done without renaming: ok? *)
  | Some l when mgu_exists l (state.trail <!> pos).selected -> Some l
  | _ -> None
;;

exception Clause_is_not_in_trail of CC.constr_clause

let get_trail_pos state cc =
  try
    snd (L.find (fun (c, _) -> c == cc) (index state.trail))
  with Not_found -> 
    F.printf "not in trail: %a\n%!" CC.pp_cclause cc;
    raise (Clause_is_not_in_trail cc)
;;


(******************************** SPLITTING ***********************************)
type split_location = Left | Right

let location_str = function Left -> "left" | _ -> "right"

(* returns partition and representative; the latter can be given as argument *)
let sggs_split ?(rep=None) where state pos by_cc =
  let cc = state.trail <!> pos in
  let partition, rep, diff = split_clauses ~rep:rep state.signature cc by_cc in
  let bef, aft = until pos state.trail, from (pos + 1) state.trail in
  let state = empty_cache { state with trail =  bef @ aft } in

  ignore (delete_idx state.trail_idx cc.selected cc);
  let add (state, i) cc =
    let state', added = add_clause_to_trail cc state (pos + i) in
    state', if added then i + 1 else i
  in
  let state', num_added = L.fold_left add (state,0) partition in
  let state'' = (* left splitting may require selection update to rightmost *)
    if where = Right then state'
    else update_selection_from (Some (CC.to_clit cc)) (state', pos + num_added)
  in

  let split_lit = (cc.selected, cc.constr, pos + num_added) in
  let aft' = remove_assigned_to split_lit state'' true in
  let until_part = until (pos + num_added) state''.trail in
  let state = { state with trail = until_part @ aft' } in

  log_step state (location_str where ^ "-split");
  state, rep, diff
;;

(* Recursive left-split used before SGGS move.
  Let c1, c2 be the constrained clauses at p1 and p2, where p1 < p2.
  Assumes that c2 depends on c1 and we want to move c2 to below c1, but besides
  the selected literal in clause c2 there are also others that depend on c1. 
  Thus c1 gets split by c2, and this process is repeated until only the selected
  literal in c2 depends on c1. By this time the selected literal in c2 may have
  changed. Returns updated state and positions p1 < p2. *)
let rec dependence_share_split state p1 p2 =
  match shares_dependency state p1 p2 with
  | Some l when not (mgu_exists l (state.trail <!> p2).selected) -> (
    let ccr = state.trail <!> p2 in
    let state, _, _ = sggs_split Left state p1 ccr in
    (* find split-by clause in trail: selection may have changed *)
    try
      let ccr', p2' = L.find (eq_upto_select ccr <.> fst) (index state.trail) in
      let _, _, p1' = find_last_dependence state (ccr'.clause, ccr'.constr) in
      dependence_share_split state p1' p2'
    (* If the split-by clause had other literals assigned to split clause, it
       was deleted. In this case, this conflict is no longer relevant. *)
    with Not_found -> state, None
  )
  | _ -> state, Some (p1, p2)
;;

let rec factor_split state p1 p2 =
  let cc = state.trail <!> p2 in
  let is_I_true = is_I_all_true_clause state cc.clause in 
  match factorizable state p1 p2 with
  | Some l when is_I_true ->
    assert (unifies l cc.selected);
    let sigma = mgu_list [l, cc.selected] in
    let factor = CC.substitute sigma cc in
    (*F.printf "factor before move\nto factor %a\nfactor is %a\n%a%!"
      CC.pp_cclause cc CC.pp_cclause factor pp_trail state;*)
    let state, _, _ = sggs_split ~rep:(Some factor) Right state p2 factor in
    (* selection in ccr may have changed, get modified factor *)
    let factor' (cc,_) = cc.clause=factor.clause && cc.constr = factor.constr in
    assert (L.exists factor' (index state.trail));
    factor_split state p1 (snd (L.find factor' (index state.trail)))
  | _ -> state, p1, p2
;;

(* Recursive right-split used after non-conflicting insertion, until the
  inserted clause cc does not intersect with any other clause.
  Returns updated state. *)
let rec complete_split state cc =
  let cl = (cc.selected, cc.constr) in
  let intersects cl' = cl <> cl' && at_gnd_instance_inter cl cl' in
  try
    let by_cc = L.find (fun c -> intersects (CC.to_clit c)) state.trail in
    try 
      let cc_pos = get_trail_pos state cc in
      let split_state, _, diff = sggs_split Right state cc_pos by_cc in
      let r = L.fold_left complete_split split_state diff in
      r
    with Clause_is_not_in_trail _ -> state (* cc may have been disposed *)
  with Not_found -> state
;;

(***************************** MAIN SGGS LOOP *********************************)
(* 
SGGS function assuming that the state is consistent, i.e. dp(Gamma) = Gamma.
This is also the entry point for the procedure, where clauses are the set of
input clauses.
*)
let rec sggs_no_conflict state clauses =
  try
    let ix_state = index state.trail in
    let cc, pos = L.find (is_conflicting state <.> fst) ix_state in
    if !O.current_options.dbg_backtrace then
      F.printf "resolve remaining conflict before extension\n%!";
    sggs_extend ~in_trail:true state clauses cc true pos
  with Not_found -> 
    (*check_invariants state;*)
    let clausesx, computed = add_intersecting_instances state clauses in
    let rec findext = function
    | [] -> None, []
    | c :: cs ->
      let o = check_valid_extension state c in
      if o = None then findext cs else o, cs
    in
    (*F.printf "%s\n%!" (if computed then "computed" else "reused");*)
    match findext clausesx with
    | None, _ ->
      if computed then (
        F.printf "model:\n%a\n" pp_trail state; 
        state, Satisfiable
      ) else 
        sggs_no_conflict (empty_cache state) clauses
    | Some ((c, constr), conflict, select), rest ->
      assert (not state.ground_preserving || C.is_ground (c));
      let cc = mk_cclause c select constr in
      inc_clauses_and_extensions state;
      let state' = {state with extension_queue = Some rest} in
      sggs_extend state' clauses cc conflict (L.length state.trail)

(* 
Extend the state by adding clause c at position pos in the trail.
Checks whether a literal in c exists which does not conflict with the current
trail, in this case a non-conflicting extension is performed. Otherwise, 
conflict-handling is triggered.
*)
and sggs_extend ?(print=true) ?(in_trail=false) state clauses cc conflict pos =
  (*F.printf "extend with %a, conflict %B\n%!" CC.pp_cclause cc conflict;*)
  let state', added =
    if in_trail then state, true else add_clause_to_trail cc state pos
  in
  if not added then sggs_no_conflict state' clauses
  else (
    let conflict = is_conflicting state' cc in
    let has_dep =
      try let _ = find_dependence state'.trail (CC.to_clit cc) false in true
      with _ -> false
    in
    if conflict && has_dep then
      sggs_conflict print state' clauses cc pos
    else if conflict then (
      let compl_cc = (compl_lit cc.selected, cc.constr) in
      let inter c = gnd_instance_inter compl_cc (CC.to_clit c) && c <> cc in
      let cc' = L.find inter state'.trail in
      let ps, _, _ = split_clauses state.signature cc cc' in
      sggs_extend ~print:false (remove_from_trail state' pos) clauses (L.hd ps) false pos)
    else (
      log_step_if print state' "extend-no-conflict";
      (* split recursively by similar or dissimilar literal *)
      sggs_no_conflict (complete_split state' cc) clauses))
      
(* 
Handle conflict which emerges because conflict_clause was added to state at
position pos, i.e., do resolve possibly preceded by move possibly preceded by
splitting/factoring.
Precondition: cc depends on a clause in the trail.
*)
and sggs_conflict do_print statex clauses cc pos =
  let conf_lit, constr = cc.selected, cc.constr in
  let _,dep_lit,dep_pos = find_dependence statex.trail (conf_lit,constr) true in
  (*Format.printf "sggs_conflict: %a at %d %!" CC.pp_cclause cc pos;
  Format.printf "(depending on %d)\n%!" dep_pos;*)
  let trailx = statex.trail in
  log_step_if do_print statex "extend-conflict";
  let lpos, rpos = min dep_pos pos, max dep_pos pos in
  (* check if move is necessary: if conf_lit I-true and to be inserted above *)
  if (is_I_all_true statex conf_lit && pos >= dep_pos) || 
    (is_I_all_true statex dep_lit && pos < dep_pos) then (
    (* prior to move, splitting the left (independent) clause is necessary if
      in the right clause, apart from the selected literal there is another
      literal that depends on the left clause.
      If the two unify this is a factoring step, otherwise left split. *)
    let statex1, lpos, rpos = factor_split statex lpos rpos in
    let statex2, poss = dependence_share_split statex1 lpos rpos in
    match poss with
    | Some (lpos, rpos) ->
      let statex3, lcls, rcls, lpos, rpos = sggs_move statex2 lpos rpos in
      sggs_resolve statex3 clauses lcls rcls lpos rpos
    (* This case happens after the split the right clause was deleted. The
        conflict thus no longer needs to be considered. *)
    | None -> sggs_no_conflict statex2 clauses
  ) else (* no move *)
    sggs_resolve statex clauses (trailx <!> lpos) (trailx <!> rpos) lpos rpos

(* 
Move cc in state from pos to below dep_pos.
*)
and sggs_resolve state clauses left_res_cls right_res_cls left_pos right_pos =
  let left_lit, right_lit = left_res_cls.selected, right_res_cls.selected in
  (*F.printf "resolve \n %d: %a in %a\n %d: %a in %a) \n%!" 
    left_pos T.pp_term left_lit pp_clause left_res_cls.clause 
    right_pos T.pp_term right_lit pp_clause right_res_cls.clause;*)
  assert (left_pos < right_pos);
  assert (is_I_all_true state left_lit);
  let state, right_pos =
    let right_clit = CC.to_clit right_res_cls in
    if covers (compl_lit left_lit, left_res_cls.constr) right_clit then
      state, right_pos
    else (
      (*F.printf "split %d before resolve: %a by %a\n%!" right_pos T.pp_term
        (compl_lit right_lit) T.pp_term left_lit;*)
      let state', rep, _ = sggs_split Right state right_pos left_res_cls in
      state', get_trail_pos state' rep)
  in
  let right_res_cls = state.trail <!> right_pos in
  let right_lit, right_constr = right_res_cls.selected, right_res_cls.constr in
  let theta = ensure_match (compl_lit left_lit) right_lit in
  let apply_theta = Subst.apply_subst_term term_db_ref theta in
  let del_lit l c = remove_term l (C.get_lits c.clause) in
  let left_part = L.map apply_theta (del_lit left_lit left_res_cls) in
  let resolvent = del_lit right_lit right_res_cls @ left_part in
  let res_clause = modify_clause right_res_cls.clause resolvent in
  let bef, aft = until right_pos state.trail, from (right_pos +1) state.trail in
  let right = (right_lit, right_constr, right_pos) in
  let aft' = remove_assigned_to right state false in
  ignore (delete_idx state.trail_idx right_lit right_res_cls);

  if resolvent = [] then (
    let cc = mk_cclause res_clause left_lit right_constr in (* dummy select *)
    inc_clauses state;
    let state' = { state with trail = bef @ [cc] @ aft'} in
    log_step state' "resolve";
    state', Unsatisfiable)
  else (
    let state' = empty_cache { state with trail = bef @ aft'} in
    try 
      let constr = Ct.project (C.get_var_list res_clause) right_constr in
      let conf,sel = find_selected (state', right_pos) (res_clause, constr) in
      let cc = mk_cclause res_clause sel constr in
      inc_clauses state;
      (* FIXME use add_to_trail *)
      DiscTree.add_elem_to_lit state'.trail_idx sel cc;
      log_step { state with trail = bef @ [cc] @ aft'} "resolve";
      sggs_extend ~print:false state' clauses cc conf right_pos
    with Disposable ->
      log_step state' "resolve+delete";
      sggs_no_conflict state' clauses
  )

(* 
Move clause in state from p2 (on the right) to just before p1 (further left).
*)
and sggs_move state p1 p2 =
  assert (p2 >= p1);
  let trail = state.trail in
  let bef, mid, aft = until p1 trail, from_to p1 p2 trail,from (p2 + 1) trail in  
  let trail' = bef @ [trail <!> p2] @ mid @ aft in
  (* index does not change because set of literals remains the same *)
  let state_moved = reorder_state state trail' in
  log_step state_moved "move";
  let cleft, cright = trail' <!> p1, trail' <!> (p1 + 1) in
  let state', cright = state_moved, cright (* FIXME: split? *) in
  state', cleft, cright, p1, p1 + 1
;;


(**************************** PREPROCESSING ***********************************)
let ground_preserving clauses =
  let get_vars t = L.map fst (T.get_var_ass_list t) in
  let pos_lits c = L.filter (fun l -> T.get_sign_lit l) (C.get_lits c) in
  let neg_lits c = L.filter (fun l -> not (T.get_sign_lit l)) (C.get_lits c) in
  let posvars c = L.fold_left (fun acc t -> get_vars t @ acc) [] (pos_lits c) in
  let negvars c = L.fold_left (fun acc t -> get_vars t @ acc) [] (neg_lits c) in
  let subset xs ys = L.for_all (fun x -> L.mem x ys) xs in
  let pgp_clause c = subset (posvars c) (negvars c) in
  let ngp_clause c = subset (negvars c) (posvars c) in
  L.for_all pgp_clause clauses, L.for_all ngp_clause clauses
;;

let pos_neg_sizes cs = 
  let mixed c = 
    L.exists T.get_sign_lit (C.get_lits c) &&
    L.exists (fun l -> not (T.get_sign_lit l)) (C.get_lits c)
  in
  let pos_lits c = L.filter (fun l -> T.get_sign_lit l) (C.get_lits c) in
  let neg_lits c = L.filter (fun l -> not (T.get_sign_lit l)) (C.get_lits c) in
  let size = L.fold_left (fun s l -> s + T.get_num_of_symb l) 0 in
  let psize c = size (pos_lits c) and nsize c = size (neg_lits c) in
  let mcs = L.filter mixed cs in
  L.fold_left (fun (p, n) c -> (p + psize c, n + nsize c)) (0,0) mcs
;;

let pos_ground_preserving cs = fst (ground_preserving cs)

let neg_ground_preserving cs = snd (ground_preserving cs)

let flip_to_pg cs =
  let at_top l = T.get_top_symb (T.get_atom l) in
  let ps = L.concat (L.map (fun c -> L.map at_top (C.get_lits c)) cs) in
  let flip_lit p l = if at_top l = p then compl_lit l else l in
  let flip_cls p c = modify_clause c (L.map (flip_lit p) (C.get_lits c)) in
  let flip p = L.map (flip_cls p) cs in
  let check_flip p = function
  | Some _ as res -> res
  | None ->
    let cs' = flip p in
    if pos_ground_preserving cs' || neg_ground_preserving cs' then (
      if !O.current_options.dbg_backtrace then
        F.printf "flip all literals with predicate %a\n%!" Symbol.pp_symbol p;
      Some cs'
    ) else None
  in
  match L.fold_right check_flip ps None with Some cs' -> cs' | _ -> cs
;;

let pick_init_interpretation clauses =
  let pg = pos_ground_preserving clauses in
  let ng = neg_ground_preserving clauses in
  let ps, ns = pos_neg_sizes clauses in
  let clauses =
    if (ng && ps >= ns) || (pg && ns >= ps) || L.length clauses > 100 then clauses
    else flip_to_pg clauses
  in
  let pg = pos_ground_preserving clauses in
  let ng = neg_ground_preserving clauses in
  if ng && not pg then (
    AllPositive, true, clauses
  ) else (
    if not pg then F.printf "The problem is not ground preserving.\n%!";
    AllNegative, pg, clauses
  )
;;

let fix_signature clauses fms =
  let sign = C.clause_list_signature clauses in
  let syms = SSet.fold (fun y xs -> y :: xs) sign.sig_fun_preds [] in
  let types = SSet.union (FM.cyclic_types fms) (FM.non_cyclic_types fms) in
  let val_type f = snd (Sym.get_stype_args_val_def f) in
  let ensure_const t syms =
    if L.exists (fun f -> Sym.get_arity f = 0 && val_type f = t) syms then syms
    else
      let stype = Sym.create_stype [] t in
      let sym = SymbolDB.create_new_split_symb SystemDBs.symbol_db_ref stype in
      sym :: syms
  in
  let syms = SSet.fold ensure_const types syms in
  if !O.current_options.dbg_backtrace then (
    F.printf "signature:\n";
    L.iter (fun s ->
      if Sym.is_fun s then (
        F.printf " %s has arity %d: " (Sym.get_name s) (Sym.get_arity s);
        let args, value = Sym.get_stype_args_val_def s in
        let a = L.fold_left (fun s a -> s ^ " " ^ (Sym.get_name a)) "" args in
        F.printf "args %s val %s\n%!" a (Sym.get_name value);
    )) syms);
  syms
;;

let do_something_smart clauses =
  start_time := Unix.gettimeofday ();
  L.iter (fun c -> L.iter (fun l -> ignore (add_term l)) (C.get_lits c)) clauses;
  let clauses = Type_inf.sub_type_inf clauses in
  let fms = FM.init_fm_state clauses in
  if !O.current_options.dbg_backtrace then (
    F.printf "%d input clauses\n" (L.length clauses);
    if L.length clauses < 100 then
      L.iter (F.printf "  %a\n%!" C.pp_clause) clauses;
    Format.printf "The problem %s stratified.\n%!" 
      (if SSet.is_empty (FM.cyclic_types fms) then "is" else "is not"));

  let initial, gnd_preserving, clauses = 
    match !O.current_options.fix_init_inter with
    | None -> pick_init_interpretation clauses 
    | Some b -> (if b then AllPositive else AllNegative), false, clauses
  in
  let init_inter_str = if initial = AllPositive then "I+" else "I-" in
  if !O.current_options.dbg_backtrace then
    Format.printf "use %s\n%!" init_inter_str;
  let syms = fix_signature clauses fms in
  let state = mk_initial_state initial gnd_preserving syms in
  try
    let state, res = sggs_no_conflict state clauses in
    print_stats state;
    res
  with e -> 
    let msg = Printexc.to_string e in
    let stack = Printexc.get_backtrace () in
    Printf.eprintf "%s\n%s\n" msg stack;
    Unknown
;;

let print_empty_clause_result _ =
  start_time := Unix.gettimeofday ();
  Format.printf "\nSZS status Unsatisfiable\n%!";
  let state = mk_initial_state AllNegative false [] in
  print_stats state;
;;

let () = Printexc.record_backtrace true
