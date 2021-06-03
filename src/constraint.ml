module T = Term
module L = List
module F = Format
module SubstM = Subst.SubstM

exception Is_unsat

type atomic =
  | DiffVars of Var.var * Var.var
  | DiffTop of Var.var * Symbol.symbol

type conjunct = atomic list
  
type t = conjunct list (* disjunction of conjunctions *)

let top = [[]]

let bot = []

let atom a = [[a]]

let is_diff_top = function DiffTop(_,_) -> true | _ -> false

let is_diff_var c = not (is_diff_top c)

let pp_constraint ppf cs =
  let pp_atom ?(no_sep = false) c =
    if not no_sep then F.fprintf ppf " & ";
    match c with
    | DiffVars (x, y) -> F.fprintf ppf "%a != %a" Var.pp_var x Var.pp_var y
    | DiffTop (x, f) -> F.fprintf ppf "top(%a) != %a"
      Var.pp_var x Symbol.pp_symbol f
  in
  let pp_conj ?(no_sep = false) c =
    if not no_sep then F.fprintf ppf " | ";
    F.fprintf ppf "( ";
    match c with
    | [] -> ()
    | a :: ats -> pp_atom ~no_sep:true a; List.iter pp_atom ats;
    F.fprintf ppf " )"
  in
  match cs with
  | []
  | [[]] -> ()
  | a :: ats -> pp_conj ~no_sep:true a; List.iter pp_conj ats
;;

let cmp_atomic s t =
  let pcmp = Pervasives.compare in
  let cmp = function 
  | DiffVars(x,y), DiffVars(x',y') ->
    if (x = x' && y = y') || (x = y' && y = x') then 0 else pcmp (x,y) (x',y')
  | DiffTop(x, f), DiffTop(x', f') -> pcmp (x, f) (x', f')
  | DiffTop _, DiffVars _
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

let conj1 c ct = List.map (List.fold_right cons c) ct

let conj ct1 ct2 = L.fold_right conj1 ct2 ct1

let disj ct1 ct2 = (*ct1 @ ct2*)
  let disj1 d ds = if L.exists (eq_conj d) ds then ds else d :: ds in
  List.fold_right disj1 ct1 ct2
;;

let substituted_sat theta ct =
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

let add_term t = TermDB.add_ref t SystemDBs.term_db_ref

let mk_var_term x = add_term (Term.create_var_term x)

let mk_fun_term f ts = add_term (Term.create_fun_term f ts)

let zip xs ys = L.fold_right2 (fun x y l -> (x,y) :: l) xs ys []

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
      let vs_new' = L.map mk_var_term vs_new in
      let diff_top = atom (DiffTop(x, f)) in
      let diff_arg = L.map (add_terms_diff ct) (zip vs_new' ts) in
      L.fold_left disj diff_top diff_arg (* difference on top or in arg *)
  | T.Fun (f, ss, _), T.Fun (g, ts, _) ->
    if f <> g then ct
    else L.fold_left disj [] (L.map (add_terms_diff ct) (zip ss ts))
  in
  let subst_atom = function
  | DiffVars (x, y) ->
    let tx = try (SubstM.find x theta) with _ -> mk_var_term x in
    let ty = try (SubstM.find y theta) with _ -> mk_var_term y in
    add_terms_diff [[]] (tx, ty)
  | DiffTop (x, f) ->
    match (try (SubstM.find x theta) with _ -> mk_var_term x) with
    | T.Var (z, _) -> atom (DiffTop(z, f))
    | t ->
      let g = T.get_top_symb t in
      if g <> f then [[]] 
      else if g == f then raise Is_unsat
      else add_terms_diff [[]] (t, mk_var_term x)
  in
  try
    let subst_conj = L.fold_left (fun ct a -> conj ct (subst_atom a)) top in
    L.fold_left (fun ct' c -> disj ct' (subst_conj c)) [] ct
  with Is_unsat -> bot
;;

let rename rho =
  let app_rho = Var.apply_renaming rho in
  let ren = function
  | DiffVars (x, y) -> DiffVars (app_rho x, app_rho y)
  | DiffTop (x, f) -> DiffTop (app_rho x, f)
  in
  L.map (L.map ren)
;;

let vars ct =
  let vars acc = function
  | DiffVars (x, y) ->
    let acc' =  if L.mem x acc then acc else x :: acc in
    if L.mem y acc' then acc' else y :: acc'
  | DiffTop (x, f) -> if L.mem x acc then acc else x :: acc
  in
  let vs = L.fold_left (fun vs c -> L.fold_left vars vs c) [] ct in
  Lib.unique ~c:Var.compare vs
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
      L.length (Lib.unique (L.filter diff_x c)) >= L.length rem
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
  | DiffVars (x, y) -> Subst.singleton x (mk_var_term y)
  | DiffTop (x,f) ->
    let a = Symbol.get_arity f in
    let xs = L.map mk_var_term (fresh_vars away_vars x a) in
    Subst.singleton x (mk_fun_term f xs)
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
