open Logic_interface
open Options

(*----- debug modifiable part-----*)
let dbg_flag = false

type dbg_gr =
  |D_trace
  |D_sig

let dbg_gr_to_str = function
  |D_trace -> "trace"
  |D_sig -> "Sig"

let dbg_groups =
  [
   D_trace;
  ]

let module_name = "abstr_ref"

(*----- debug fixed part --------*)
let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(* ****************************** *)

type ar_symb = symbol * int

module ARS_Key =
struct
  type t = ar_symb
  let compare (f1,args1) (f2,args2) =
    if (f1 == f2)
    then
      Pervasives.compare args1 args2
    else
      Symbol.compare f1 f2
end

module ARS_Map = Map.Make(ARS_Key)
module ARS_Set = Set.Make(ARS_Key)

type bool_sig = bool list (* [b_1;..;b_n] if true then the argument present and is not otherwise *)
type symb_filter = symbol * bool_sig (* symbol and signature containing both true and false *)

module SF_Key =
struct
  type t = symb_filter
  let compare (f1,bs1) (f2,bs2) =
    if (f1 == f2)
    then
      Lib.list_compare_lex Pervasives.compare bs1 bs2
    else
      Symbol.compare f1 f2
end

module SF_Map = Map.Make(SF_Key)

module TLMap = Term.MapList
module TLSet = Term.SetList

(* ARS_Trivial is concretising all symbols in unsat core; ARS_Single is flip first false arg *)
type refine_bsig_param =  ARS_Trivial | ARS_Single

type abstr_cl_wrap = (* aclw *)
  {
    aclw_orig_cls    : CSet.t;
    aclw_lits        : lit list; (* without the switch pred *)
    aclw_switch_pred : term; (* switch_pred -- prop pred *)
    aclw_acl         : clause; (* acl: aclw_lits \/ ~switch_pred *)
  }

type sig_env = (* environment containing abstraction of signature *)
  {
    ars_to_as     : symbol ARS_Map.t; (* (f,no_args) -> abstr_symb *)
    as_to_ars     : ARS_Set.t SMap.t; (* abstr_symb -> (f,no_args) *)

    sf_to_as      : symbol SF_Map.t; (* (f,bool_sig) -> abstr_symb *)
    as_to_sf      : symb_filter SMap.t; (* abstr_symb -> (f,bool_sig) *)
    symb_to_asymb : symbol SMap.t; (* symb -> abstr_symb *)
  }

type cl_env = (* environment containing abstraction of clauses *)
  {
    swp_to_aclw       : abstr_cl_wrap TMap.t;
    abstr_lits_to_swp : term TLMap.t;
    acl_set           : CSet.t;
    concretised_set   : CSet.t;
    cl_assumptions    : TSet.t;
  }

type uc_env =
  {
    swp_uc : TSet.t
  }

type particular_state =
  {
    sig_env     : sig_env;
    cl_env      : cl_env;
    aux_cl_env  : cl_env;
    uc_env      : uc_env;
    abstraction : Options.abstr_ref_type;
    input_cls   : CSet.t;
  }

type ar_state =
  {
    orig_clause_set : CSet.t;
    partic_st       : particular_state;
    swp_cnt         : int;
  }

(* ************** Printing functions ************** *)

let bool_list_to_str bool_list =
  let str_bool_list = String.concat "," (List.map string_of_bool bool_list) in
  String.concat "" ["[";str_bool_list;"]"]

let costume_symb_to_str fun_to_str symbol =
  let (sym, signature) = symbol in
  (Symbol.to_string sym) ^ ":" ^ (fun_to_str signature)

let ars_list_to_str ars_lst =
  let ars_strs = List.map (costume_symb_to_str string_of_int) ars_lst in
  String.concat "," ars_strs

let ars_set_to_str ars_set =
  let ars_lst = ARS_Set.elements ars_set in
  ars_list_to_str ars_lst

let costume_symb_map_to_str bindings k_to_str e_to_str map =
  let f (k,e) =
    (costume_symb_to_str k_to_str k) ^ " -> " ^ (e_to_str e)
  in
  String.concat "\n" (List.map f bindings)

let ars_map_to_str e_to_str map =
  let bindings = ARS_Map.bindings map in
  costume_symb_map_to_str bindings string_of_int e_to_str map

let sf_map_to_str e_to_str map =
  let bindings = SF_Map.bindings map in
  costume_symb_map_to_str bindings bool_list_to_str e_to_str map

let abstr_cl_wrap_to_str clw =
  Clause.to_string clw.aclw_acl

let smap_to_str e_to_str map =
  let bindings = SMap.bindings map in
  let f (k,e) =
    (Symbol.to_string k) ^ " -> " ^ (e_to_str e)
  in
  String.concat "\n" (List.map f bindings)

let tmap_to_str e_to_str map =
  let bindings = TMap.bindings map in
  let f (k,e) =
    (Term.to_string k) ^ " -> " ^ (e_to_str e)
  in
  String.concat "\n" (List.map f bindings)

let tlmap_to_str e_to_str map =
  let bindings = TLMap.bindings map in
  let f (k,e) =
    (Term.term_list_to_string k) ^ " -> " ^ (e_to_str e)
  in
  String.concat "\n" (List.map f bindings)

let cset_to_str set = Clause.clause_list_to_string (CSet.elements set)

let tset_to_str set = Term.term_list_to_string (TSet.elements set)

let sset_to_str set =
  String.concat ";" (List.map Symbol.to_string (SSet.elements set))

let sig_env_to_str sig_env =
  let str_ars_to_as =
    "ars_to_as:\n" ^ (ars_map_to_str Symbol.to_string sig_env.ars_to_as) in
  let str_as_to_ars =
    "\nas_to_ars:\n" ^ (smap_to_str ars_set_to_str sig_env.as_to_ars) in
  let str_sf_to_as =
    "\nsf_to_as:\n" ^ (sf_map_to_str Symbol.to_string sig_env.sf_to_as) in
  let str_as_to_sf =
    "\nas_to_sf:\n" ^ (smap_to_str (costume_symb_to_str bool_list_to_str) sig_env.as_to_sf) in
  let str_symb_to_asymb =
    "\nsymb_to_asymb:\n" ^ (smap_to_str Symbol.to_string sig_env.symb_to_asymb) in
  String.concat "\n***************\n"
    [str_as_to_ars; str_ars_to_as; str_sf_to_as; str_as_to_sf; str_symb_to_asymb]

let cl_env_to_str cl_env =
  let str_swp_to_aclw =
    "swp_to_aclw:\n" ^ tmap_to_str abstr_cl_wrap_to_str cl_env.swp_to_aclw in
  let str_abstr_lits_to_swp =
    "abstr_lits_to_swp:\n" ^ tlmap_to_str Term.to_string cl_env.abstr_lits_to_swp in
  let str_acl_set =
    "acl_set:\n" ^ cset_to_str cl_env.acl_set in
  let str_concretised_set =
    "concretised_set:\n" ^ cset_to_str cl_env.concretised_set in
  let str_cl_assumptions =
    "cl_assumptions:\n" ^ tset_to_str cl_env.cl_assumptions in
  String.concat "\n***************\n"
    [str_swp_to_aclw; str_abstr_lits_to_swp; str_acl_set;
     str_concretised_set; str_cl_assumptions]

let partic_st_to_str state =
  let str_cl_env =
    "cl_env:\n" ^ cl_env_to_str state.partic_st.cl_env in
  let str_sig_env =
    "sig_env:\n" ^ sig_env_to_str state.partic_st.sig_env in
  let str_uc_env =
    "uc_env:\n" ^ tset_to_str state.partic_st.uc_env.swp_uc in
  let str_input_cls =
    "input clauses:\n" ^ cset_to_str state.partic_st.input_cls in
  String.concat "\n***************\n" [str_cl_env; str_sig_env;
                                       str_uc_env; str_input_cls]

let state_to_str state =
  let str_orig_clause_set =
    "orig clauses:\n" ^ cset_to_str state.orig_clause_set in
  let str_partic_st =
    "Particular state:\n" ^ partic_st_to_str state in
  String.concat "\n***************\n" [str_orig_clause_set; str_partic_st]

let bsp_param_to_str bsp =
  match bsp with
  | ARS_Trivial -> "ARS_Trivial"
  | ARS_Single ->  "ARS_Single"


(* *********** Initialitation functions ************** *)

let create_sig_env () =
  {
    ars_to_as     = ARS_Map.empty;
    as_to_ars     = SMap.empty;

    sf_to_as      = SF_Map.empty;
    as_to_sf      = SMap.empty;
    symb_to_asymb = SMap.empty;
  }

let create_cl_env () =
  {
    swp_to_aclw        = TMap.empty;
    abstr_lits_to_swp  = TLMap.empty;
    acl_set            = CSet.empty;
    concretised_set    = CSet.empty;
    cl_assumptions     = TSet.empty;
  }

let create_uc_env () =
  {
    swp_uc = TSet.empty;
  }

let create_particular_state () =
  {
    sig_env     = create_sig_env ();
    cl_env      = create_cl_env ();
    aux_cl_env  = create_cl_env ();
    uc_env      = create_uc_env ();
    abstraction = Options.Abstr_ref_subs;
    input_cls   = CSet.empty;
  }


(* ******** Common functions ******** *)

let get_cl_switch_pred state lit_list =
  let create_switch_pred inside_state =
    let sw_pred_name = "$$iProver_ARSWP_"^(string_of_int inside_state.swp_cnt) in
    let switch_pred = add_pred_0 ~is_special:true sw_pred_name in
    let current_lists_to_swp =
      TLMap.add lit_list switch_pred inside_state.partic_st.cl_env.abstr_lits_to_swp in
    let current_partic_st =
      {
        inside_state.partic_st with
        cl_env =
          {
            inside_state.partic_st.cl_env with
            abstr_lits_to_swp = current_lists_to_swp
          }
      }
    in
    let current_state =
      {
        inside_state with
        swp_cnt = inside_state.swp_cnt + 1;
        partic_st = current_partic_st;
      }
    in
    (switch_pred, current_state)
  in
  let lit_list = Term.remove_duplicate_terms lit_list in
  try
    let switch_pred =
      TLMap.find lit_list state.partic_st.cl_env.abstr_lits_to_swp in
    (switch_pred, state)
  with
  | Not_found ->
    create_switch_pred state

let add_abstr_clause abstr_lits orig_clause state =
  let (switch_pred, current_state) = get_cl_switch_pred state abstr_lits in
  let abstr_cl_wrap =
    try
      let abstr_cl_wrap =
        TMap.find switch_pred current_state.partic_st.cl_env.swp_to_aclw in
      let current_aclw_orig_cls =
        CSet.add orig_clause abstr_cl_wrap.aclw_orig_cls
      in
      {abstr_cl_wrap with aclw_orig_cls = current_aclw_orig_cls}
    with
    | Not_found ->
      let compl_switch_pred = Logic_interface.add_neg_atom switch_pred in
      let tstp_source = Clause.tstp_source_arg_filter_abstr orig_clause in
      let abstr_clause =
        create_clause tstp_source (compl_switch_pred::abstr_lits) in
      Clause.inherit_conjecture orig_clause abstr_clause;
      {
        aclw_orig_cls = CSet.singleton orig_clause;
        aclw_lits = abstr_lits;         (* without the switch pred *)
        aclw_switch_pred = switch_pred; (* switch_pred -- prop pred *)
        aclw_acl = abstr_clause;        (* acl: ~aclw_lits \/ switch_pred *)
      }
  in
  let current_ar_swp_to_aclw =
    TMap.add abstr_cl_wrap.aclw_switch_pred abstr_cl_wrap
      current_state.partic_st.cl_env.swp_to_aclw
  in
  let current_cl_env =
    {
      current_state.partic_st.cl_env with
      swp_to_aclw = current_ar_swp_to_aclw;
      acl_set = CSet.add abstr_cl_wrap.aclw_acl
          current_state.partic_st.cl_env.acl_set;
      cl_assumptions = TSet.add abstr_cl_wrap.aclw_switch_pred
          current_state.partic_st.cl_env.cl_assumptions;
    }
  in
  {
    current_state with
    partic_st = {current_state.partic_st with cl_env = current_cl_env}
  }

let add_concr_cl concrete_cl state =
  let current_cl_env =
    {
      state.partic_st.cl_env with
      concretised_set = CSet.add concrete_cl state.partic_st.cl_env.concretised_set;
    }
  in
  {
    state with
    partic_st = {state.partic_st with cl_env = current_cl_env}
  }

let function_gamma state swp accum =
  try
    let abstr_cl_wrap = TMap.find swp state.partic_st.cl_env.swp_to_aclw in
    CSet.union abstr_cl_wrap.aclw_orig_cls accum
  with
    Not_found -> accum

let get_concrete_uc state =
  TSet.fold (function_gamma state) state.partic_st.uc_env.swp_uc CSet.empty


(* ******** Abstr-Ref helpers ******** *)
let get_abstr_symb state ars =
  let abstr_symb = ARS_Map.find ars state.partic_st.sig_env.ars_to_as in
  let ars_set = SMap.find abstr_symb state.partic_st.sig_env.as_to_ars in
  let (_, nargs) = ARS_Set.min_elt ars_set in
  (abstr_symb, nargs)

let rec abstr_term state t =
  match t with
  |Term.Fun (symb, args, _info) ->
    let args_ls = Term.arg_to_list args in
    let nargs = List.length args_ls in
    let (new_symb, new_args) =
      try
        let (new_symb, nargs) = get_abstr_symb state (symb, nargs) in
        let new_args =  List.map (abstr_term state) args_ls in
        (new_symb, new_args)
      with
      | Not_found ->
        let new_args = List.map (abstr_term state) args_ls in
        (symb, new_args)
    in
    add_fun_term new_symb new_args
  | Term.Var _ -> t

(* filters elements of list corresponding to b (true/false) positions in bsig *)
let bs_filter_list b bsig list =
  assert ((List.length bsig) = (List.length list));
  let f res current_b e =
    if (b = current_b)  then e::res else res
  in
  List.rev (List.fold_left2 f [] bsig list)

let bs_filter_positions b bsig =
  let f (cnt,res) e = if (e = b) then (cnt+1,cnt::res) else (cnt+1,res) in
  let (_cnt, res) = (List.fold_left f (1,[]) bsig) in
  List.rev res

let get_abstr_symb_af state symb =
  let abstr_symb  = SMap.find symb state.partic_st.sig_env.symb_to_asymb in
  let (_, bsig) = SMap.find abstr_symb state.partic_st.sig_env.as_to_sf in
  (abstr_symb, bsig)

(* should be applied to atoms or terms (not to negations) *)
(* we assume that sf is already filled-in in the ar_sig_env *)
let rec abstr_term_af state t =
  match t with
  |Term.Fun (orig_symb, args, _info) ->
      let args_list = Term.arg_to_list args in
      let (new_symb, new_args) =
        try
          let (new_symb,bsig) = get_abstr_symb_af state orig_symb in (*can raise Not_found *)
          let filtered_args = bs_filter_list true bsig args_list in
          let new_args =  List.map (abstr_term_af state) filtered_args in
          (new_symb,new_args)
        with
        | Not_found ->
          let new_args = List.map (abstr_term_af state) args_list in
          (orig_symb,new_args)
      in
      add_fun_term new_symb new_args
  | Term.Var _ -> t

let add_abstr_symb state orig_symb bsig =
  let symb_filter = (orig_symb, bsig) in
  try
    let abstr_symb = SF_Map.find symb_filter state.partic_st.sig_env.sf_to_as in
    (abstr_symb, state)
  with
  | Not_found ->
    let positions = bs_filter_positions true bsig in
    (* create abstr_symb *)
    let abstr_symb_name = (* TODO: add some $$ prefix ? *)
      String.concat "_"
        ((Symbol.to_string orig_symb)::
          ((string_of_int 0)::
          (List.map string_of_int positions)))
    in
    let (orig_arg_types, orig_val_type) = Symbol.get_stype_args_val_def orig_symb in
    let abstr_arg_types = bs_filter_list true bsig orig_arg_types in
    let abstr_symb_type = create_stype abstr_arg_types orig_val_type in
    let abstr_symb = create_symbol abstr_symb_name abstr_symb_type in
    let new_sf_to_as =
      SF_Map.add symb_filter abstr_symb state.partic_st.sig_env.sf_to_as in
    let new_as_to_sf =
      SMap.add abstr_symb symb_filter state.partic_st.sig_env.as_to_sf in
    let new_sig_env =
      {
        state.partic_st.sig_env with
        sf_to_as = new_sf_to_as;
        as_to_sf = new_as_to_sf;
      }
    in
    let new_state =
      {state with partic_st = {state.partic_st with sig_env = new_sig_env}}
    in
    (abstr_symb, new_state)

(* remove abstraction of the orig_symb from the current abstraction *)
let ar_sig_env_rm_abstr_symb state orig_symb =
  if (SMap.mem orig_symb state.partic_st.sig_env.symb_to_asymb)
  then
    let new_symb_to_asymb =
      SMap.remove orig_symb state.partic_st.sig_env.symb_to_asymb in
    {
      state with
      partic_st =
        {
          state.partic_st with
          sig_env =
            {
              state.partic_st.sig_env with
              symb_to_asymb = new_symb_to_asymb;
            }
        }
    }
  else
    state

let ar_sig_env_replace_abstr_symb orig_symb bsig state =
  let state_after_rm = ar_sig_env_rm_abstr_symb state orig_symb in
  let (abstr_symb, state_after_add) =
    add_abstr_symb state_after_rm orig_symb bsig in
  let new_symb_to_asymb =
    SMap.add orig_symb abstr_symb state_after_add.partic_st.sig_env.symb_to_asymb in
  {
    state_after_add with
    partic_st =
      {
        state_after_add.partic_st with
        sig_env =
          {
            state_after_add.partic_st.sig_env with
            symb_to_asymb = new_symb_to_asymb;
          }
      }
  }

let apply_sig_abstr_to_clause clause state =
  let abstr_term_func =
    match state.partic_st.abstraction with
    | Options.Abstr_ref_sig -> abstr_term
    | Options.Abstr_ref_arg_filter -> abstr_term_af
    | _ -> failwith "apply_sig_abstr_to_clause: Unknown abstraction"
  in
  let orig_lits = Clause.get_literals clause in
  let abstr_lit lit =
    add_term_db (Term.apply_to_atom (abstr_term_func state) lit) in
  let abstr_lits = List.map abstr_lit orig_lits in
  let non_trivial =
    List.exists2 (fun l1 l2 -> not (l1 == l2)) orig_lits abstr_lits in
  if non_trivial
  then add_abstr_clause abstr_lits clause state
  else add_concr_cl clause state

let swp_to_abstr_symbs state swp asymb_accum =
  try
    let abstr_cl_wrap = TMap.find swp state.partic_st.cl_env.swp_to_aclw in
    let acl_asymbs = Clause.find_all_sym
        ~is_relevant_symb:(fun _ -> true) abstr_cl_wrap.aclw_acl in
    SSet.union acl_asymbs asymb_accum
  with
    Not_found -> asymb_accum

let count_literals cls exclusions =
  let counting_lits_per_cl cl accum =
    let update_lit_count update_lit_cnt lit =
      if List.mem lit exclusions then
        update_lit_cnt
      else
        try
          let current_count = TMap.find lit update_lit_cnt in
          TMap.add lit (current_count + 1) update_lit_cnt
        with
        | Not_found ->
          TMap.add lit 1 update_lit_cnt
    in
    let lits = Clause.get_literals cl in
    List.fold_left update_lit_count accum lits
  in
  let count_map =
    CSet.fold counting_lits_per_cl cls TMap.empty in
  TMap.bindings count_map

let get_max_element lit_list =
  let ordering (l1, c1) (l2, c2) = Pervasives.compare c1 c2 in
  let sorted_list = List.rev (List.fast_sort ordering lit_list) in
  match sorted_list with
  | [] -> None
  | hd :: _ -> Some(hd)

let gather_cls_by_leading_lit cls leading_lit =
  let f cl =
    let lits = Clause.get_literals cl in
    List.mem leading_lit lits
  in
  CSet.filter f cls

let clean_clauses_sets state =
  {
    state with
    partic_st =
      {
        state.partic_st with
        cl_env = create_cl_env ();
      }
  }

(* ******** Abstractions ******** *)

let ar_alpha_signature cl state =
  let term_to_abstr_symb state term =
    match term with
    | Term.Fun(symb, args, _) ->
      let args_ls = Term.arg_to_list args in
      let nargs = List.length args_ls in
      if not (ARS_Map.mem (symb, nargs) state.partic_st.sig_env.ars_to_as)
      then
        let (arg_types, val_type) = Symbol.get_stype_args_val_def symb in
        let arg_types_str =
          String.concat "" (List.map Symbol.to_string arg_types) in
        let abstr_name = String.concat "_" [
            "ars"; string_of_int nargs; (Symbol.to_string val_type); arg_types_str
          ]
        in
        let stype = Symbol.get_type symb in
        let abstr_symb = create_symbol abstr_name stype in
        let new_ars_to_as =
          ARS_Map.add (symb, nargs) abstr_symb state.partic_st.sig_env.ars_to_as in
        let set_ars =
          try
            let current_set_ars = SMap.find abstr_symb state.partic_st.sig_env.as_to_ars in
            ARS_Set.add (symb, nargs) current_set_ars
          with
          | Not_found -> ARS_Set.singleton (symb, nargs)
        in
        let new_as_to_ars =
          SMap.add abstr_symb set_ars state.partic_st.sig_env.as_to_ars in
        let new_sig_env =
          {
            state.partic_st.sig_env with
            ars_to_as = new_ars_to_as;
            as_to_ars = new_as_to_ars;
          }
        in
        {state with partic_st = {state.partic_st with sig_env = new_sig_env}}
      else
        state
    | _ -> state
  in
  let rec abstr_terms_sig state t =
    match t with
    | Term.Fun(symb,args,_) when (Symbol.is_pred symb || Symbol.is_fun symb) &&
                                not (Term.is_const_term t) ->
      dbg D_sig (lazy ("\t[terms sig] Collapsed ===> " ^ Term.to_string t));
      let args_list = Term.arg_to_list args in
      let current_state = term_to_abstr_symb state t in
      List.fold_left abstr_terms_sig current_state args_list
    |_->
      dbg D_sig (lazy ("\t[terms sig] Non collapsed ===> " ^ Term.to_string t));
      state
  in
  let rec abstr_skolem_sig state t =
    match t with
    | Term.Fun(symb,args,_) when Term.is_skolem_const t || Term.is_skolem_lit t ||
                                (Symbol.is_constant symb &&
                                  Symbol.get_property symb = Symbol.Undef_Prop) ||
                                Symbol.get_property symb = Symbol.Split ->
      dbg D_sig (lazy ("\t[skolem sig] Collapsed ===> " ^ Term.to_string t));
      let args_list = Term.arg_to_list args in
      let current_state = term_to_abstr_symb state t in
      List.fold_left abstr_skolem_sig current_state args_list
    | Term.Fun(symb,args,_) when Symbol.is_pred symb || Symbol.is_fun symb ->
      let args_list = Term.arg_to_list args in
      List.fold_left abstr_skolem_sig state args_list
    |_->
      dbg D_sig (lazy ("\t[skolem sig] Non collapsed ===> " ^ Term.to_string t));
      state
  in
  let atoms = List.map Term.get_atom (Clause.get_lits cl) in
  let current_state =
    match !current_options.abstr_ref_sig_restrict with
    | Funpre -> List.fold_left abstr_terms_sig state atoms
    | Skc    -> List.fold_left abstr_skolem_sig state atoms
  in
  apply_sig_abstr_to_clause cl current_state

let ar_alpha_argument_filtering cls state =
  let bs_and_2 bs1 bs2 = List.map2 (&&) bs1 bs2 in
  let eligible_symbol symb =
    if !current_options.abstr_ref_af_restrict_to_split_sk
    then
      ((Symbol.get_property symb) = Symbol.Split) || (Symbol.is_skolem symb)
    else
      true
  in
  (* non-variable filter sig *)
  let non_var_bsig tlist = List.map (fun t -> not (Term.is_var t)) tlist in
  let rec ground_abstr_tsig symb_to_sf t =
    if (Term.is_ground t)
    then symb_to_sf
    else begin
      match t with
      |Term.Fun (symb, args, _info) ->
        if (eligible_symbol symb)
        then
          begin
            let args_list = Term.arg_to_list args in
            let non_var_bsig = non_var_bsig args_list in
            let non_var_args = bs_filter_list true non_var_bsig args_list in
            let exists_var_arg = (List.exists (fun e -> e = false) non_var_bsig) in
            let new_symb_to_sf =
              if exists_var_arg
              then
                try
                  let old_sf = SMap.find symb symb_to_sf in
                  let new_sf = bs_and_2 non_var_bsig old_sf in
                  SMap.add symb new_sf symb_to_sf
                with
                | Not_found -> SMap.add symb non_var_bsig symb_to_sf
              else
                symb_to_sf
            in
            List.fold_left ground_abstr_tsig new_symb_to_sf non_var_args
          end
        else
          symb_to_sf
      |_-> failwith "ground_abstr_tsig: t should be a non-variable term"
    end
  in
  let ground_abstr_clsig c symb_to_sf = List.fold_left ground_abstr_tsig symb_to_sf (Clause.get_literals c) in
  let ground_abstr_cl_list_sig cl_list = CSet.fold ground_abstr_clsig cls SMap.empty in
  let gr_abstr_sig_map = ground_abstr_cl_list_sig cls in
  let st_after_replace = SMap.fold ar_sig_env_replace_abstr_symb gr_abstr_sig_map state in
  CSet.fold apply_sig_abstr_to_clause cls st_after_replace

let rec ar_alpha_subsumption cls abstr_cl state =
  let lits_count_list = count_literals cls abstr_cl in
  match get_max_element lits_count_list with
  | Some(max_lit, count) when count > 1 ->
    let new_abstr_cl = max_lit :: abstr_cl in
    let gath_org_cls = gather_cls_by_leading_lit cls max_lit in
    let new_in_cls_set = CSet.diff cls gath_org_cls in
    let current_state =
      CSet.fold (add_abstr_clause new_abstr_cl) gath_org_cls state in
    ar_alpha_subsumption new_in_cls_set abstr_cl current_state
  | _ -> CSet.fold add_concr_cl cls state


(* ******** Refinements ******** *)

let ar_refine_signature state =
  let abstr_symbs_uc =
    TSet.fold (swp_to_abstr_symbs state) state.partic_st.uc_env.swp_uc SSet.empty in
  let refine_sig_env absym sig_env =
    try
      let ars_set = SMap.find absym sig_env.as_to_ars in
      let current_as_to_ars =
        SMap.remove absym sig_env.as_to_ars in
      let current_ars_to_as =
        ARS_Set.fold ARS_Map.remove ars_set sig_env.ars_to_as in
      {
        state.partic_st.sig_env with
        ars_to_as = current_ars_to_as;
        as_to_ars = current_as_to_ars;
      }
    with
    | Not_found -> sig_env
  in
  let current_sig_env = SSet.fold refine_sig_env abstr_symbs_uc state.partic_st.sig_env in
  {
    state with
    partic_st =
      {
        state.partic_st with
        sig_env = current_sig_env;
        cl_env = create_cl_env ();
      }
  }

let ar_refine_argument_filter state =
  let refine_bsig_param =  (*ARS_Trivial*)  ARS_Single in
  let abstr_sig_get_orig_symb abstr_symb =
    SMap.find abstr_symb state.partic_st.sig_env.as_to_sf in
  let flip_first_false bsig =
    let flipped_flag = ref false in
    let f rest b =
      if (!flipped_flag || b)
      then
        b::rest
      else (
        flipped_flag:=true;
        true::rest
      )
    in
    let rev_flipped = List.fold_left f [] bsig in
    List.rev rev_flipped
  in
  let refine_bsig bsig =
    match refine_bsig_param with
    | ARS_Trivial -> List.map (fun _ -> true) bsig
    | ARS_Single  -> flip_first_false bsig
  in
  let abstr_symbs_uc =
    TSet.fold (swp_to_abstr_symbs state) state.partic_st.uc_env.swp_uc SSet.empty in
  let orig_symbs_uc =
    let f abstr_symb symb_rest =
      try
        let (orig_symb,_) = abstr_sig_get_orig_symb abstr_symb in
        SSet.add orig_symb symb_rest
      with
      | Not_found -> symb_rest
    in
    SSet.fold f abstr_symbs_uc SSet.empty
  in
  let refine_symb_ar_sig_env orig_symb inner_state =
    try
      let (curr_abstr_symb, curr_bsig) = get_abstr_symb_af inner_state orig_symb in
      let new_bsig = refine_bsig curr_bsig in
      let non_trivial = List.exists (fun e -> e = false) new_bsig in
      if non_trivial
      then
        ar_sig_env_replace_abstr_symb orig_symb new_bsig inner_state
      else
        ar_sig_env_rm_abstr_symb inner_state orig_symb  (* concretise this symbol *)
    with
      Not_found -> inner_state
  in
  let new_state = SSet.fold refine_symb_ar_sig_env orig_symbs_uc state in
  {
    new_state with
    partic_st =
      {
        new_state.partic_st with
        sig_env = new_state.partic_st.sig_env;
        cl_env = create_cl_env ();
      }
  }

let ar_refine_subsumption state =
  let f swp accum_state =
    try
      let aclw = TMap.find swp state.partic_st.cl_env.swp_to_aclw in
      let inner_state =
        ar_alpha_subsumption aclw.aclw_orig_cls aclw.aclw_lits accum_state in
      {
        inner_state with
        partic_st =
          {
            inner_state.partic_st with
            cl_env =
              {
                inner_state.partic_st.cl_env with
                acl_set =
                  CSet.remove aclw.aclw_acl inner_state.partic_st.cl_env.acl_set;
                cl_assumptions =
                  TSet.remove swp inner_state.partic_st.cl_env.cl_assumptions;
              }
          }
      }
    with
      Not_found -> accum_state
  in
  TSet.fold f state.partic_st.uc_env.swp_uc state


(* ***************************** *)

let get_all_clauses state =
  let abstr_cls = state.partic_st.cl_env.acl_set in
  let conctr_cls = state.partic_st.cl_env.concretised_set in
  CSet.union abstr_cls conctr_cls

let get_all_assumptions state =
  state.partic_st.cl_env.cl_assumptions

let apply_abstraction abstr_ref_type state =
  let state_abstr_type =
    {
      state with
      partic_st =
        {
          state.partic_st with
          abstraction = abstr_ref_type
        }
    }
  in
  let clean_cl_env_state = clean_clauses_sets state_abstr_type in
  let all_cls = get_all_clauses state_abstr_type in
  let input_clauses =
    if CSet.is_empty all_cls
    then state_abstr_type.orig_clause_set
    else all_cls
  in
  let state_after_abstr =
    match abstr_ref_type with
    | Options.Abstr_ref_sig ->
      CSet.fold ar_alpha_signature input_clauses clean_cl_env_state
    | Options.Abstr_ref_subs ->
      let aux_state = ar_alpha_subsumption input_clauses [] clean_cl_env_state in
      {
        aux_state with
        partic_st =
          {
            aux_state.partic_st with
            aux_cl_env = aux_state.partic_st.cl_env
          }
      }
    | Options.Abstr_ref_arg_filter ->
      ar_alpha_argument_filtering input_clauses clean_cl_env_state
  in
  let all_assumptions = get_all_assumptions state_after_abstr in
  Prop_solver_exchange.add_solver_assumptions
    ~only_norm:true (TSet.elements all_assumptions);
  let current_partic_st =
    {
      state_after_abstr.partic_st with
      input_cls = input_clauses;
    }
  in
  {state_after_abstr with partic_st = current_partic_st}

let refine state swp_uc =
  let current_partic_st = {state.partic_st with uc_env = {swp_uc = swp_uc}} in
  let current_state = {state with partic_st = current_partic_st} in
  let state_after_refinement =
    match state.partic_st.abstraction with
    | Options.Abstr_ref_sig ->
      let inner_state = ar_refine_signature current_state in
      CSet.fold apply_sig_abstr_to_clause state.partic_st.input_cls inner_state
    | Options.Abstr_ref_subs ->
      ar_refine_subsumption current_state
    | Options.Abstr_ref_arg_filter ->
      let inner_state = ar_refine_argument_filter current_state in
      CSet.fold apply_sig_abstr_to_clause state.partic_st.input_cls inner_state
  in
  let all_assumptions = get_all_assumptions state_after_refinement in
  Prop_solver_exchange.add_solver_assumptions
    ~only_norm:true (TSet.elements all_assumptions);
  state_after_refinement

let refine_until_sat state swp_uc =
  let current_partic_st = {state.partic_st with uc_env = {swp_uc = swp_uc}} in
  let current_state = {state with partic_st = current_partic_st} in
  let state_after_refinement =
    match state.partic_st.abstraction with
    | Options.Abstr_ref_sig ->
      let inner_state = ar_refine_signature current_state in
      CSet.fold apply_sig_abstr_to_clause (get_concrete_uc current_state) inner_state
    | Options.Abstr_ref_subs ->
      let aux_state =
        {
          current_state with
          partic_st =
            {
              current_state.partic_st with
              cl_env = current_state.partic_st.aux_cl_env
            }
        }
      in
      let aux_state = ar_refine_subsumption aux_state in
      let aux_state =
        {
          aux_state with
          partic_st =
            {
              aux_state.partic_st with
              aux_cl_env = aux_state.partic_st.cl_env;
              cl_env =
                {
                  aux_state.partic_st.cl_env with
                  acl_set = CSet.empty;
                  concretised_set = CSet.empty;
                  cl_assumptions = TSet.empty;
                }
            }
        }
      in
      let current_state = ar_refine_subsumption aux_state in
      current_state
    | Options.Abstr_ref_arg_filter ->
      let inner_state = ar_refine_argument_filter current_state in
      CSet.fold apply_sig_abstr_to_clause (get_concrete_uc current_state) inner_state
  in
  let all_assumptions = get_all_assumptions state_after_refinement in
  Prop_solver_exchange.add_solver_assumptions
    ~only_norm:true (TSet.elements all_assumptions);
  state_after_refinement

let state_after_until_sat state =
  let state_after_refinement =
    match state.partic_st.abstraction with
    | Options.Abstr_ref_sig ->
      let current_state = CSet.fold apply_sig_abstr_to_clause state.partic_st.input_cls state in
      current_state
    | Options.Abstr_ref_subs ->
      let current_state =
        {
          state with
          partic_st =
            {
              state.partic_st with
              cl_env = state.partic_st.aux_cl_env
            }
        }
      in
      current_state
    | Options.Abstr_ref_arg_filter ->
      let current_state = CSet.fold apply_sig_abstr_to_clause state.partic_st.input_cls state in
      current_state
  in
  let all_assumptions = get_all_assumptions state_after_refinement in
  Prop_solver_exchange.add_solver_assumptions
    ~only_norm:true (TSet.elements all_assumptions);
  state_after_refinement

let init_ar_env input =
  {
    orig_clause_set = CSet.of_list input;
    partic_st       = create_particular_state ();
    swp_cnt         = 0;
  }
