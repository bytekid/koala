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
    
let module_name = "options"

(*----- debug fixed part --------*)

let () = dbg_flag_msg dbg_flag module_name

let dbg group str_lazy = 
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f = 
  Lib.dbg_env_set dbg_flag dbg_groups group f
    
(*----- debug -----*)

    

(* Option values with defaults and overrides from files or command-line *)

(* How to use these overrides: (assume an option named [opt])

 * Use type [ opt override ] for the type of the option

 * In the function set_new_current_options:
   [ opt = override o.opt !current_options.opt; ]

 * In op_fun:
   [ !current_options.opt <- override_cmd b !current_options.opt ]

 * In x_options_str_list:
   [ (opt_type_to_str (val_of_override opt.opt) ] ;

 * In the options:
   [ opt = ValueDefault 0; ]

 * When reading the options value:
   [ val_of_override !current_options.opt ]

 *)

(* An option set from different sources *)
type 'a override =

    (* Option has the default value *)
  | ValueDefault of 'a

	(* Default has been overridden by file argument *)
  | ValueFile of 'a

	(* Default has been overridden by command-line argument *)
  | ValueCmd of 'a

(* Get current value of option *)
let val_of_override = function
  | ValueDefault v -> v
  | ValueFile v -> v
  | ValueCmd v -> v

(* Override value with a new default value *)
let override_default v' = function

    (* Override previous default value *)
  | ValueDefault _ -> ValueDefault v'

	(* Do not override file or command line values *)
  | _ as v -> v

(* Override value with a new default value *)
let override_file v' = function

    (* Override previous default or file value *)
  | ValueDefault _
  | ValueFile _ -> ValueFile v'

	(* Do not override command line value *)
  | _ as v -> v

(* Override value with a new command-line value *)
let override_cmd v' = function

    (* Override previous default, file or command-line value  *)
  | ValueDefault _
  | ValueFile _
  | ValueCmd _ -> ValueCmd v'

(* Override one value with another *)
let override = function
  | ValueDefault v -> override_default v
  | ValueFile v -> override_file v
  | ValueCmd v -> override_cmd v

(* Change the value keeping its status *)
let override_value = function
  | ValueDefault _ -> (function v -> ValueDefault v)
  | ValueFile _ -> (function v -> ValueFile v)
  | ValueCmd _ -> (function v -> ValueCmd v)

(*--prase list options----*)
exception Parse_list_fail

let parse_list_opt str =
  let str_ln = String.length str in
  if (str.[0] = '[') && (str.[(str_ln -1)] = ']')
  then
    let new_str = String.sub str 1 (str_ln -2) in
    let str_list = Str.split (Str.regexp "[|;|]") new_str in
    str_list
  else
    (
     dbg D_trace (lazy ("Parse_list_fail: "^str));
    raise Parse_list_fail
    )

let parse_list_list_opt str =
  let str_ln = String.length str in
  if (str.[0] = '[') && (str.[(str_ln -1)] = ']')
  then
    (* get rid of ALL starting/finishing brackets *)
    let new_str = String.sub str 2 (str_ln -4) in
    let str_list = Str.split (Str.regexp "\\];\\[") new_str in
    (* put the outer brackets back *)
    let parse_opts str = parse_list_opt ("["^str^"]") in
    List.map parse_opts str_list
  else
    raise Parse_list_fail

(*--parse functional options of form "fun_name[arg1;arg2;...]"---*)
(*--returns ("fun_name",["arg1";"arg2";...]--*)
exception Parse_fun_fail
let parse_fun_opt str =
  let br_reg_exp = Str.regexp "\\[\\([0-9]\\|[a-z]\\|[A-Z]\\|;\\)+\\]" in
  try
    let list_start = Str.search_forward br_reg_exp str 0 in
    let fun_str = String.sub str 0 list_start in
    (* out_str ("fun_str"^fun_str^"\n"); *)
    let arg_str = Str.matched_string str in
    (fun_str, (parse_list_opt arg_str))
  with
  | Not_found | Parse_list_fail -> raise Parse_fun_fail

(*-----------------Option Types---------------------------*)

(*---------General----------*)
type out_options_type = Out_All_Opt | Out_Control_Opt | Out_No_Opt

let out_options_type_to_str opt =
  match opt with
  | Out_All_Opt -> "all"
  | Out_Control_Opt -> "control"
  | Out_No_Opt -> "none"

exception Unknown_out_options_type
let str_to_out_options_type str =
  match str with
  |"all" -> Out_All_Opt
  |"control" -> Out_Control_Opt
  |"none" -> Out_No_Opt
  | _ -> raise Unknown_out_options_type

(*--------*)
type splitting_mode_type = Split_Input | Split_Full | Split_None

let splitting_mode_type_to_str opt =
  match opt with
  | Split_Input -> "input"
  | Split_Full -> "full"
  | Split_None -> "none"

exception Unknown_splitting_mode_type

let str_to_splitting_mode_type str =
  match str with
  |"input" -> Split_Input
  |"full" -> Split_Full
  |"none" -> Split_None
  | _ -> raise Unknown_splitting_mode_type

let splitting_mode_type_str = "<none|input|full>"

(*--------*)
type prep_sem_filter_type =
    Sem_Filter_None | Sem_Filter_Pos | Sem_Filter_Neg | Sem_Filter_Exhaustive

let prep_sem_filter_type_to_str opt =
  match opt with
  | Sem_Filter_None -> "none"
  | Sem_Filter_Pos -> "pos"
  | Sem_Filter_Neg -> "neg"
  | Sem_Filter_Exhaustive -> "exhaustive"

exception Unknown_sem_filter_type
let str_to_prep_sem_filter_type str =
  match str with
  |"none" -> Sem_Filter_None
  |"pos" -> Sem_Filter_Pos
  |"neg" -> Sem_Filter_Neg
  |"exhaustive" -> Sem_Filter_Exhaustive
  | _ -> raise Unknown_sem_filter_type

let prep_sem_filter_type_str = "<none|pos|neg|exhaustive>"

(*--------*)

(* Output no statistics, statistics after every bound or only after
   the last bound in BMC1 *)
type bmc1_out_stat_type =
    BMC1_Out_Stat_None | BMC1_Out_Stat_Full | BMC1_Out_Stat_Last

let bmc1_out_stat_type_to_str = function
  | BMC1_Out_Stat_None -> "none"
  | BMC1_Out_Stat_Full -> "full"
  | BMC1_Out_Stat_Last -> "last"

exception Unknown_bmc1_out_stat_type
let str_to_bmc1_out_stat_type = function
  | "none" -> BMC1_Out_Stat_None
  | "full" -> BMC1_Out_Stat_Full
  | "last" -> BMC1_Out_Stat_Last
  | _ -> raise Unknown_bmc1_out_stat_type

let bmc1_out_stat_type_list_str = "<none|full|last>"

(*--------*)

type bmc1_axioms_type =
    BMC1_Axioms_Reachable_All | BMC1_Axioms_Reachable_Last

let bmc1_axioms_type_to_str = function
  | BMC1_Axioms_Reachable_All -> "reachable_all"
  | BMC1_Axioms_Reachable_Last -> "reachable_last"

exception Unknown_bmc1_axioms_type
let str_to_bmc1_axioms_type = function
  | "reachable_all" -> BMC1_Axioms_Reachable_All
  | "reachable_last" -> BMC1_Axioms_Reachable_Last
  | _ -> raise Unknown_bmc1_axioms_type

let bmc1_axioms_type_list_str = "<reachable_all|reachable_last>"

(*--------*)

type bmc1_add_unsat_core_type =
  | BMC1_Add_Unsat_Core_None
  | BMC1_Add_Unsat_Core_Clauses
  | BMC1_Add_Unsat_Core_Leaves
  | BMC1_Add_Unsat_Core_All

let bmc1_add_unsat_core_type_to_str = function
  | BMC1_Add_Unsat_Core_None -> "none"
  | BMC1_Add_Unsat_Core_Clauses -> "clauses"
  | BMC1_Add_Unsat_Core_Leaves -> "leaves"
  | BMC1_Add_Unsat_Core_All -> "all"

exception Unknown_bmc1_add_unsat_core_type
let str_to_bmc1_add_unsat_core_type = function
  | "none" -> BMC1_Add_Unsat_Core_None
  | "clauses" -> BMC1_Add_Unsat_Core_Clauses
  | "leaves" -> BMC1_Add_Unsat_Core_Leaves
  | "all" -> BMC1_Add_Unsat_Core_All
  | _ -> raise Unknown_bmc1_add_unsat_core_type

let bmc1_add_unsat_core_type_list_str = "<none|leaves|clauses|all>"

(*--------*)

type bmc1_ucm_cone_mode_type =
  | BMC1_Ucm_Cone_Mode_None
  | BMC1_Ucm_Cone_Mode_AIG
  | BMC1_Ucm_Cone_Mode_Symb
  | BMC1_Ucm_Cone_Mode_UC

let bmc1_ucm_cone_mode_type_to_str = function
  | BMC1_Ucm_Cone_Mode_None -> "none"
  | BMC1_Ucm_Cone_Mode_AIG -> "aig"
  | BMC1_Ucm_Cone_Mode_Symb -> "symb"
  | BMC1_Ucm_Cone_Mode_UC -> "uc"

exception Unknown_bmc1_ucm_cone_mode_type
let str_to_bmc1_ucm_cone_mode_type = function
  | "none" -> BMC1_Ucm_Cone_Mode_None
  | "aig" -> BMC1_Ucm_Cone_Mode_AIG
  | "symb" -> BMC1_Ucm_Cone_Mode_Symb
  | "uc" -> BMC1_Ucm_Cone_Mode_UC
  | _ -> raise Unknown_bmc1_ucm_cone_mode_type

let bmc1_ucm_cone_mode_type_list_str = "<none|aig|symb|uc>"

(*--------*)

type schedule_type =
  | Schedule_none
  | Schedule_default
  | Schedule_sat
  | Schedule_abstr_ref
  | Schedule_abstr_ref_sat
  | Schedule_verification_epr_old
  | Schedule_verification_epr_tables
  | Schedule_verification_epr
  | Schedule_smac_tmp

let schedule_type_to_str opt =
  match opt with
  | Schedule_none -> "none"
  | Schedule_default -> "default"
  | Schedule_sat -> "sat"
  | Schedule_abstr_ref -> "abstr_ref"
  | Schedule_abstr_ref_sat -> "abstr_ref_sat"
  | Schedule_verification_epr_old -> "verification_epr_old"
  | Schedule_verification_epr_tables -> "verification_epr_tables"
  | Schedule_verification_epr -> "verification_epr"
  | Schedule_smac_tmp -> "smac_tmp"

exception Unknown_schedule_type
let str_to_schedule_type str =
  match str with
  |"none" -> Schedule_none
  |"default" -> Schedule_default
  |"sat" -> Schedule_sat
  |"abstr_ref" -> Schedule_abstr_ref
  |"abstr_ref_sat" -> Schedule_abstr_ref_sat
  |"verification_epr_old" -> Schedule_verification_epr_old
  |"verification_epr_tables" -> Schedule_verification_epr_tables
  |"verification_epr" -> Schedule_verification_epr
  |"smac_tmp" -> Schedule_smac_tmp
  | _ -> raise Unknown_schedule_type

let schedule_type_list_str ="<none|default|sat|abstr_ref|abstr_ref_sat|verification_epr_old|verification_epr_tables|verification_epr|smac_tmp>"

(*-----Lit Params----------*)

type lit_cmp_type =
  | Lit_Sign of bool
  | Lit_Ground of bool
  | Lit_Prop of bool
  | Lit_Num_of_Var of bool
  | Lit_Num_of_Symb of bool
  | Lit_Atom_depth of bool
  | Lit_Split of bool
  | Lit_Id of bool
  | Lit_has_conj_symb of bool
  | Lit_has_bound_constant of bool
  | Lit_next_state of bool
  | Lit_reachable_state of bool
	(*  | Lit_reachable_state            of bool *)
  | Lit_has_non_prolific_conj_symb of bool
  | Lit_eq of bool
  | Lit_clock of bool
  | Lit_less of bool
  | Lit_range of bool

let lit_cmp_type_to_str par =
  match par with
  | Lit_Sign b -> if b then "+sign" else "-sign"
  | Lit_Ground b -> if b then "+ground" else "-ground"
  | Lit_Prop b ->  if b then "+prop" else "-prop"
  | Lit_Num_of_Var b -> if b then "+num_var" else "-num_var"
  | Lit_Num_of_Symb b -> if b then "+num_symb" else "-num_symb"
  | Lit_Atom_depth b -> if b then "+depth" else "-depth"
  | Lit_Split b -> if b then "+split" else "-split"
  | Lit_Id b -> if b then "+id" else "-id"
  | Lit_has_conj_symb b -> if b then "+conj_symb" else "-conj_symb"
  | Lit_has_bound_constant b -> if b then "+has_bound_constant" else "-has_bound_constant"
  | Lit_next_state b -> if b then "+next_state" else "-next_state"
  | Lit_reachable_state b -> if b then "+reachable_state" else "-reachable_state"
  | Lit_has_non_prolific_conj_symb b ->
      if b then "+non_prol_conj_symb" else "-non_prol_conj_symb"
  | Lit_eq b -> if b then "+eq" else "-eq"
  | Lit_clock b -> if b then "+clock" else "-clock"
  | Lit_less b -> if b then "+less" else "-less"
  | Lit_range b -> if b then "+range" else "-range"

exception Unknown_lit_cmp_type
let str_to_lit_cmp_type str =
  match str with
  | "+sign" -> Lit_Sign true
  | "-sign" -> Lit_Sign false
  | "+ground" -> Lit_Ground true
  | "-ground" -> Lit_Ground false
  | "+prop" -> Lit_Prop true
  | "-prop" -> Lit_Prop false
  | "+num_var" -> Lit_Num_of_Var true
  | "-num_var" -> Lit_Num_of_Var false
  | "+num_symb" -> Lit_Num_of_Symb true
  | "-num_symb" -> Lit_Num_of_Symb false
  | "+depth" -> Lit_Atom_depth true
  | "-depth" -> Lit_Atom_depth false
  | "+split" -> Lit_Split true
  | "-split" -> Lit_Split false
  | "+id" -> Lit_Id true
  | "-id" -> Lit_Id false
  | "+conj_symb" -> Lit_has_conj_symb true
  | "-conj_symb" -> Lit_has_conj_symb false
  | "+has_bound_constant" -> Lit_has_bound_constant true
  | "-has_bound_constant" -> Lit_has_bound_constant false
  | "+next_state" -> Lit_next_state true
  | "-next_state" -> Lit_next_state false
  | "+reachable_state" -> Lit_reachable_state true
  | "-reachable_state" -> Lit_reachable_state false
  | "+non_prol_conj_symb" -> Lit_has_non_prolific_conj_symb true
  | "-non_prol_conj_symb" -> Lit_has_non_prolific_conj_symb false
  | "+eq" -> Lit_eq true
  | "-eq" -> Lit_eq false
  | "+clock" -> Lit_clock true
  | "-clock" -> Lit_clock false
  | "+less" -> Lit_less true
  | "-less" -> Lit_less false
  | "+range" -> Lit_range true
  | "-range" -> Lit_range false
  | _ -> raise Unknown_lit_cmp_type

let lit_cmp_type_list_str = "<[((+|-)(sign|ground|prop|num_var|num_symb|depth|split|conj_symb|non_prol_conj_symb|eq|clock|less|range|has_bound_constant|next_state|reachable_state))^+]>"

(* if there is no conjectures then we can to remove corresponding comparisons*)

let strip_conj_lit_type_list lit_type_list =
  let rec strip' rest list =
    match list with
    | h:: tl ->
	(match h with
	| Lit_has_conj_symb _ -> strip' rest tl
	| Lit_has_non_prolific_conj_symb _ -> strip' rest tl
	| _ -> strip' (h:: rest) tl
	)
    |[] -> List.rev rest
  in
  strip' [] lit_type_list

(*-----*)
type inst_lit_sel_type = lit_cmp_type list

let inst_lit_sel_type_to_str t =
  ("["^(list_to_string lit_cmp_type_to_str t ";")^"]")

(*----------------------------- *)

type lit_bool_prop_type = 
  | Lit_bp_sign of bool
  | Lit_bp_epr of bool
  | Lit_bp_eq of bool 
  | Lit_bp_ground of bool 
  | Lit_bp_prop of bool 
  | Lit_bp_conj_symb of bool 


let lit_bool_prop_type_to_str par =
  match par with
  | Lit_bp_sign b           -> if b then "+sign" else "-sign"
  | Lit_bp_epr b            -> if b then "+epr" else "-epr"
  | Lit_bp_eq b             -> if b then "+eq" else "-eq"
  | Lit_bp_ground b         -> if b then "+ground" else "-ground"
  | Lit_bp_prop b           -> if b then "+prop" else "-prop"
  | Lit_bp_conj_symb b      -> if b then "+conj_symb" else "-conj_symb"
      
exception Unknown_lit_bool_prop_type
let str_to_lit_bool_prop_type str = 
  match str with 
  | "+sign"                 -> Lit_bp_sign true
  | "-sign"                 -> Lit_bp_sign false
  | "+epr"                  -> Lit_bp_epr true 
  | "-epr"                  -> Lit_bp_epr false 
  | "+eq"                   -> Lit_bp_eq true
  | "-eq"                   -> Lit_bp_eq false
  | "+ground"               -> Lit_bp_ground true
  | "-ground"               -> Lit_bp_ground false
  | "+prop"                 -> Lit_bp_prop true 
  | "-prop"                 -> Lit_bp_prop false
  | "+conj_symb"            -> Lit_bp_conj_symb true 
  | "-conj_symb"            -> Lit_bp_conj_symb false
  | _                       -> raise Unknown_lit_bool_prop_type

let lit_bool_prop_type_list_str = "<[((+|-)(sign|epr|eq|ground|prop|conj_symb))*]>"

(*----*)
type prop_impl_unit_type = lit_bool_prop_type list

let prop_impl_unit_type_to_str t =
  ("["^(list_to_string lit_bool_prop_type_to_str t ";")^"]")


(*----Clause Param---------*)
type cl_cmp_type =
  | Cl_Age of bool
  | Cl_Num_of_Var of bool
  | Cl_Num_of_Symb of bool
  | Cl_Num_of_Lits of bool
  | Cl_Ground of bool
  | Cl_Conj_Dist of bool
  | Cl_Has_Conj_Symb of bool
  | Cl_has_bound_constant of bool
  | Cl_has_next_state of bool
  | Cl_has_reachable_state of bool
  | Cl_Has_Non_Prolific_Conj_Symb of bool
  | Cl_Max_Atom_Input_Occur of bool
  | Cl_Horn of bool
  | Cl_EPR of bool
  | Cl_in_unsat_core of bool
  | Cl_Has_Eq_Lit of bool
	(* defined symbols as in father_of relatio (Intel) *)
  | Cl_min_defined_symb of bool
  | Cl_bc_imp_inh of bool

let cl_cmp_type_to_str par =
  match par with
  | Cl_Age b -> if b then "+age" else "-age"
  | Cl_Num_of_Var b -> if b then "+num_var" else "-num_var"
  | Cl_Num_of_Symb b -> if b then "+num_symb" else "-num_symb"
  | Cl_Num_of_Lits b -> if b then "+num_lits" else "-num_lits"
  | Cl_Ground b -> if b then "+ground" else "-ground"
  | Cl_Conj_Dist b -> if b then "+conj_dist" else "-conj_dist"
  | Cl_Has_Conj_Symb b -> if b then "+conj_symb" else "-conj_symb"
  | Cl_has_bound_constant b -> if b then "+has_bound_constant" else "-has_bound_constant"
  | Cl_has_next_state b -> if b then "+next_state" else "-next_state"
  | Cl_has_reachable_state b -> if b then "+reachable_state" else "-reachable_state"
  | Cl_Has_Non_Prolific_Conj_Symb b -> if b then "+conj_non_prolific_symb" else "-conj_non_prolific_symb"
  | Cl_Max_Atom_Input_Occur b -> if b then "+max_atom_input_occur" else
    "-max_atom_input_occur"
  | Cl_Horn b -> if b then "+horn" else "-horn"
  | Cl_EPR b -> if b then "+epr" else "-epr"
  | Cl_in_unsat_core b -> if b then "+uc" else "-uc"
  | Cl_Has_Eq_Lit b -> if b then "+has_eq" else "-has_eq"
  | Cl_min_defined_symb b -> if b then "+min_def_symb" else "-min_def_symb"
  | Cl_bc_imp_inh b ->  if b then "+bc_imp_inh" else "-bc_imp_inh"

exception Unknown_cl_cmp_type
let str_to_cl_cmp_type str =
  match str with
  |"+age" -> Cl_Age true
  |"-age" -> Cl_Age false
  |"+num_var" -> Cl_Num_of_Var true
  |"-num_var" -> Cl_Num_of_Var false
  |"+num_symb" -> Cl_Num_of_Symb true
  |"-num_symb" -> Cl_Num_of_Symb false
  |"+num_lits" -> Cl_Num_of_Lits true
  |"-num_lits" -> Cl_Num_of_Lits false
  |"+ground" -> Cl_Ground true
  |"-ground" -> Cl_Ground false
  |"+conj_dist" -> Cl_Conj_Dist true
  |"-conj_dist" -> Cl_Conj_Dist false
  |"+has_bound_constant" -> Cl_has_bound_constant true
  |"-has_bound_constant" -> Cl_has_bound_constant false
  |"+next_state" -> Cl_has_next_state true
  |"-next_state" -> Cl_has_next_state false
  |"+reachable_state" -> Cl_has_reachable_state true
  |"-reachable_state" -> Cl_has_reachable_state false
  |"+conj_symb" -> Cl_Has_Conj_Symb true
  |"-conj_symb" -> Cl_Has_Conj_Symb false
  |"+conj_non_prolific_symb" -> Cl_Has_Non_Prolific_Conj_Symb true
  |"-conj_non_prolific_symb" -> Cl_Has_Non_Prolific_Conj_Symb false
  |"+max_atom_input_occur" -> Cl_Max_Atom_Input_Occur true
  |"-max_atom_input_occur" -> Cl_Max_Atom_Input_Occur false
  |"+horn" -> Cl_Horn true
  |"-horn" -> Cl_Horn false
  |"+epr" -> Cl_EPR true
  |"-epr" -> Cl_EPR false
  |"+uc" -> Cl_in_unsat_core true
  |"-uc" -> Cl_in_unsat_core false
  |"+has_eq" -> Cl_Has_Eq_Lit true
  |"-has_eq" -> Cl_Has_Eq_Lit false
  |"+min_def_symb" -> Cl_min_defined_symb true
  |"-min_def_symb" -> Cl_min_defined_symb false
  |"+bc_imp_inh" -> Cl_bc_imp_inh true
  |"-bc_imp_inh" -> Cl_bc_imp_inh false
  | _ -> raise Unknown_cl_cmp_type

let cl_cmp_type_list_str = "<[((+|-)(age|num_var|num_symb|num_lits|ground|conj_dist|conj_symb|max_atom_input_occur|horn|epr|uc|has_eq|has_bound_constant|min_def_symb|next_state|reachable_state|bc_imp_inh))^+]>"

let strip_conj_clause_type_list clause_type_list =
  let rec strip' rest list =
    match list with
    | h:: tl ->
	(match h with
	| Cl_Conj_Dist _ -> strip' rest tl
	| Cl_Has_Conj_Symb _ -> strip' rest tl
	| Cl_Has_Non_Prolific_Conj_Symb _ -> strip' (h:: rest) tl
	| _ -> strip' (h:: rest) tl
	)
    |[] -> List.rev rest
  in
  strip' [] clause_type_list

let strip_conj_clause_type_list_list clause_type_list_list =
  List.map strip_conj_clause_type_list clause_type_list_list

(*----*)

type pass_queue_type = cl_cmp_type list

let pass_queue_type_to_str t =
  ("["^(list_to_string cl_cmp_type_to_str t ";")^"]")

type pass_queue_list_type = pass_queue_type list

let pass_queues_type_to_str t =
  let single_pass_queue_type_to_str l = ("["^(list_to_string cl_cmp_type_to_str l ";")^"]") in
  ("["^(list_to_string single_pass_queue_type_to_str t ";")^"]")



(*-------------------- *)

exception Unknown_extra_neg_conj
type extra_neg_conj_type = ENC_none | ENC_all_neg | ENC_all_pos | ENC_all_pos_neg

let extra_neg_conj_type_to_str par = 
  match par with 
  | ENC_none -> "none"
  | ENC_all_neg -> "all_eng"
  | ENC_all_pos -> "all_pos"
  | ENC_all_pos_neg -> "all_pos_neg"

let str_to_extra_neg_conj_type str = 
  match str with 
  |"none"        -> ENC_none 
  |"all_neg"     -> ENC_all_neg
  |"all_pos"     -> ENC_all_pos
  |"all_pos_neg" -> ENC_all_pos_neg
  | _ -> raise Unknown_extra_neg_conj
        
let extra_neg_conj_type_str = "<none|all_eng|all_pos|all_pos_neg>"
    
(*-------------------- bc_imp_inh: important basic clauses --------------*)

exception Unknown_bc_imp_inh_type

type bc_imp_inh_type = BCI_bmc1_lemma | BCI_conj_cone

let bc_imp_inh_type_to_str par =
  match par with
  |BCI_bmc1_lemma -> "bmc1_lemma"
  |BCI_conj_cone -> "conj_cone"

let str_to_bc_imp_inh_type str = 
  match str with
  |"bmc1_lemma" -> BCI_bmc1_lemma
  |"conj_cone" -> BCI_conj_cone
  | _-> raise Unknown_bc_imp_inh_type

type bc_imp_inh_list_type = bc_imp_inh_type list

let bc_imp_inh_list_type_str = "<[(bmc1_lemma|conj_cone)*]>"

let bc_imp_inh_list_type_to_str opt =
  ("["^(list_to_string bc_imp_inh_type_to_str opt ";")^"]")

let str_to_bc_imp_inh_list_type str = 
  let str_list = parse_list_opt str in
   List.map str_to_bc_imp_inh_type str_list 

(*-------------------- Abstr_ref type ----------------*)

exception Unknown_abstr_ref_type

type abstr_ref_type = 
  |Abstr_ref_subs 
  |Abstr_ref_sig  
  |Abstr_ref_arg_filter

let abstr_ref_type_to_str par = 
  match par with 
  |Abstr_ref_subs       -> "subs"
  |Abstr_ref_sig        -> "sig"
  |Abstr_ref_arg_filter -> "arg_filter"


let str_to_abstr_ref_type str =
  match str with  
  |"subs"       -> Abstr_ref_subs
  |"sig"        -> Abstr_ref_sig 
  |"arg_filter" -> Abstr_ref_arg_filter
  | _-> raise Unknown_abstr_ref_type

type abstr_ref_list_type = abstr_ref_type list 

let abstr_ref_list_type_str = "<[(subs|sig)*(arg_filter)?]>"

let abstr_ref_list_type_to_str opt = 
  ("["^(list_to_string abstr_ref_type_to_str opt ";")^"]")

let str_to_abstr_ref_list_type str = 
  let str_list = parse_list_opt str in
  List.map str_to_abstr_ref_type str_list 

(*-------------------- Abstr_ref signature abstraction restrict ----------------*)

exception Unknown_abstr_ref_sig_restrict_type

type abstr_ref_sig_restrict_type = Funpre | Skc

let abstr_ref_sig_restrict_type_to_str par =
  match par with
  | Funpre -> "funpre"
  | Skc    -> "skc"

let str_to_abstr_ref_sig_restrict_type str =
  match str with
  |"funpre"  -> Funpre
  |"skc"     -> Skc
  | _ -> raise Unknown_abstr_ref_sig_restrict_type

let abstr_ref_sig_restrict_type_str = "<funpre|skc>"

(*-------- qbf_dom_inst ---------------*)

exception Unknown_qbf_dom_inst_type

type qbf_dom_inst_type = 
  | QBF_dom_inst_none
  | QBF_dom_inst_single 
  | QBF_dom_inst_chain
      
let qbf_dom_inst_type_to_str par = 
  match par with 
  | QBF_dom_inst_none   -> "none"
  | QBF_dom_inst_single -> "single"
  | QBF_dom_inst_chain  -> "chain"
 
let str_to_qbf_dom_inst_type str  = 
  match str with 
  | "none"     -> QBF_dom_inst_none 
  | "single"   -> QBF_dom_inst_single
  | "chain"    -> QBF_dom_inst_chain
  |_           -> raise Unknown_qbf_dom_inst_type

let qbf_dom_inst_type_str = "<none|single|chain>"

(*--------------------- clause measure ----------------*)
type cl_measure_type = 
  |CM_num_lit
  |CM_num_var
  |CM_num_symb
  |CM_cnt
  |CM_none

let cl_measure_type_to_str par = 
  match par with 
  |CM_num_lit  -> "num_lit"
  |CM_num_var  -> "num_var"
  |CM_num_symb -> "num_symb"
  |CM_cnt      -> "cnt"
  |CM_none     -> "none"

exception Unknown_cl_measure_type
 
let str_to_cl_measure_type str = 
  match str with 
  |"num_lit"  -> CM_num_lit
  |"num_var"  -> CM_num_var
  |"num_symb" -> CM_num_symb
  |"cnt"      -> CM_cnt
  |"none"     -> CM_none
  | _-> raise Unknown_cl_measure_type

let cl_measure_type_list = "<num_lit|num_var|num_symb|cnt|none>"

(*--------------------Passive queue types--------------*)

type passive_queue_type = PQT_Queue | PQT_Stack | PQT_List | PQT_PriorityQueues

let passive_queue_type_to_str opt =
  match opt with
  | PQT_Queue -> "queue"
  | PQT_Stack -> "stack"
  | PQT_List -> "list"
  | PQT_PriorityQueues -> "priority_queues"

exception Unknown_passive_queue_type
let str_to_passive_queue_type str =
  match str with
  | "queue" -> PQT_Queue
  | "stack" -> PQT_Stack
  | "list" -> PQT_List
  | "priority_queues" -> PQT_PriorityQueues
  | _ -> raise Unknown_passive_queue_type

(*--------------------Passive queue frequencies--------------*)

type passive_queue_freqs = int list

let passive_queue_freqs_to_str opt =
  ("["^(list_to_string string_of_int opt ";")^"]")

(*--------------------Instantiation Option Types--------------*)

(*---Inst Lit Sel----*)

type inst_sel_renew_type = Inst_SR_Solver | Inst_SR_Model

let inst_sel_renew_type_to_str opt =
  match opt with
  | Inst_SR_Solver -> "solver"
  | Inst_SR_Model -> "model"

exception Unknown_inst_sel_renew_type
let str_to_inst_sel_renew_type str =
  match str with
  |"solver" -> Inst_SR_Solver
  |"model" -> Inst_SR_Model
  | _ -> raise Unknown_inst_sel_renew_type

(*---------------------sat_out_model option types-----------------------------------*)

type sat_out_model_type = Model_Small | Model_Pos | Model_Neg | Model_Implied | Model_Debug | Model_Intel | Model_None

let sat_out_model_type_to_str opt =
  match opt with
  | Model_Small -> "small"
  | Model_Pos -> "pos"
  | Model_Neg -> "neg"
  | Model_Implied -> "implied"
  | Model_Debug -> "debug"
  | Model_Intel -> "intel"
  | Model_None -> "none"

exception Unknown_sat_model_out_type
let str_to_sat_out_model_type str =
  match str with
  |"small" -> Model_Small
  |"pos" -> Model_Pos
  |"neg" -> Model_Neg
  |"implied" -> Model_Implied
  |"none" -> Model_None
  |"debug" -> Model_Debug
  |"intel" -> Model_Intel
  | _ -> raise Unknown_sat_model_out_type

let sat_out_model_type_str = "<small|pos|neg|implied|debug|intel|none>"

(*--------------------Resolution Option Types--------------*)

(*----Subsumption----*)
type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int

let res_subs_type_to_str t =
  match t with
  | Subs_Full -> "full"
  | Subs_Subset -> "subset_subsumption"
  | Subs_By_Length l ->
      ("length["^(string_of_int l)^"]")

exception Unknown_res_subs_type
let str_to_res_subs_type str =
  match str with
  |"full" -> Subs_Full
  |"subset_subsumption" -> Subs_Subset
  | str ->
      try
	let (fun_str, arg_list) = parse_fun_opt str in
	match fun_str with
	|"length" ->
	    (match arg_list with
	    |[num_str] -> Subs_By_Length (int_of_string num_str)
	    | _ -> failwith "str_to_res_subs_type wrong args"
	    )
	| _ -> raise Unknown_res_subs_type
      with
	Parse_fun_fail -> raise Unknown_res_subs_type

let res_subs_type_str = "<full | subset_subsumption | length[<int>]>"

(*---Selection Fun----*)

type res_lit_sel_type =
    Res_adaptive 
  | Res_adaptive_neg 
  | Res_adaptive_max  
  | Res_KBO_max 
  | Res_neg_sel_max 
  | Res_neg_sel_min 
  | Res_pos_sel_max 
  | Res_pos_sel_min 
  | Res_neg_sel_nrc

let res_lit_sel_type_to_str res_sel_type =
  match res_sel_type with
  | Res_adaptive -> "adaptive"
  | Res_adaptive_neg -> "adaptive_neg"
  | Res_adaptive_max -> "adaptive_max"
  | Res_KBO_max -> "kbo_max"
  | Res_neg_sel_max -> "neg_max"
  | Res_neg_sel_min -> "neg_min"
  | Res_pos_sel_max -> "pos_max"
  | Res_pos_sel_min -> "pos_min"
  | Res_neg_sel_nrc -> "neg_nrc"

exception Unknown_res_sel_fun_type
let str_to_sel_type str =
  match str with
  |"adaptive" -> Res_adaptive
  |"adaptive_neg" ->  Res_adaptive_neg
  |"adaptive_max" -> Res_adaptive_max
  |"kbo_max" -> Res_KBO_max
  |"neg_max" -> Res_neg_sel_max
  |"neg_min" -> Res_neg_sel_min
  |"pos_max" -> Res_pos_sel_max
  |"pos_min" -> Res_pos_sel_min
  |"neg_nrc" -> Res_neg_sel_nrc
  | _ -> raise Unknown_res_sel_fun_type

let res_lit_sel_type_str = "<adaptive | adaptive_neg | adaptive_max | kbo_max | neg_max | neg_min | pos_max | pos_min |  neg_nrc>"

(*-----*)
type res_ord_type =
  | Res_ord_kbo
  | Res_ord_kbo_pred

let res_ord_type_to_str res_ord_type = 
    match res_ord_type with
    | Res_ord_kbo -> "kbo"
    | Res_ord_kbo_pred -> "kbo_pred"
          
exception Unknown_res_ord_type
let str_to_res_ord_type str =
  match str with
  |"kbo" -> Res_ord_kbo
  |"kbo_pred" -> Res_ord_kbo_pred
  |_ -> raise Unknown_res_ord_type

let res_ord_type_str = "<kbo | kbo_pred>"

(*-----*)

type res_to_prop_solver_type =
    Res_to_Solver_Active | Res_to_Solver_Passive | Res_to_Solver_None

let res_to_prop_solver_type_to_str t =
  match t with
  | Res_to_Solver_Active -> "active"
  | Res_to_Solver_Passive -> "passive"
  | Res_to_Solver_None -> "none"

exception Unknown_res_to_prop_solver_type
let str_to_res_to_prop_solver_type str =
  match str with
  |"active" -> Res_to_Solver_Active
  |"passive" -> Res_to_Solver_Passive
  |"none" -> Res_to_Solver_None
  | _ -> raise Unknown_res_to_prop_solver_type

(*-----All options-----*)

type options = {
    mutable out_options : out_options_type override;
    mutable tptp_safe_out : bool;

    (*----Input-------*)
    mutable problem_path : string;
    mutable include_path : string;
    mutable problem_files : string list;
    mutable clausifier : string;
    mutable clausifier_options : string;
    mutable stdin : bool;
    mutable dbg_backtrace : bool;
    mutable dbg_more : bool;
    mutable dbg_dump_prop_clauses : bool;
    mutable dbg_dump_prop_clauses_file : string;
    mutable dbg_out_stat : bool;

    (*----General--------*)
    mutable fix_init_inter : bool option;
    mutable time_out_real : float;
    mutable time_out_prep_mult : float;
    mutable time_out_virtual : float;
    mutable schedule : schedule_type;
    mutable splitting_mode : splitting_mode_type;
    mutable splitting_grd : bool;
    mutable splitting_cvd : bool;
    mutable splitting_cvd_svl : bool;
    mutable splitting_nvd : int;
    mutable non_eq_to_eq : bool;
    mutable prep_gs_sim : bool;
    mutable prep_unflatten : bool;
    mutable prep_res_sim : bool;
    mutable prep_upred   : bool;
    mutable res_sim_input : bool;
    mutable clause_weak_htbl: bool;
    mutable gc_record_bc_elim: bool;
    mutable symbol_type_check : bool;
    mutable clausify_out : bool;
    mutable prep_sem_filter : prep_sem_filter_type;
    mutable prep_sem_filter_out : bool;
    mutable preprocessed_out   : bool;
    mutable preprocessed_stats : bool;
    mutable sub_typing : bool;
    mutable eq_ax_congr_red : bool;
    mutable brand_transform : bool;
    mutable pure_diseq_elim : bool;
    mutable min_unsat_core : bool;
    mutable pred_elim : bool;
    mutable add_important_lit : bool;
    mutable soft_assumptions : bool;
    mutable soft_lemma_size : int;
    mutable prop_impl_unit_size : int; 
    mutable prop_impl_unit      : prop_impl_unit_type;
    mutable share_sel_clauses   : bool;

    mutable reset_solvers : bool;
    mutable bc_imp_inh : bc_imp_inh_list_type;
    mutable conj_cone_tolerance : float;
    mutable extra_neg_conj  : extra_neg_conj_type;
    mutable abstr_ref : abstr_ref_list_type;
(*
    mutable abstr_ref_arg_filter : bool;
    mutable abstr_ref_sig  : bool;
    mutable abstr_ref_subs : bool;
*)
    mutable abstr_ref_prep : bool;
    mutable abstr_ref_until_sat : bool;
    (* mutable abstr_terms_sig  : bool;
     * mutable abstr_skolem_sig  : bool; *)
    mutable abstr_ref_sig_restrict : abstr_ref_sig_restrict_type;
    mutable abstr_ref_af_restrict_to_split_sk : bool;
    mutable prep_def_merge : bool;
    mutable prep_def_merge_prop_impl : bool;
    mutable prep_def_merge_mbd : bool;
    mutable prep_def_merge_tr_red : bool;
    mutable prep_def_merge_tr_cl : bool;

    (*---Large Theories---------------*)
    mutable large_theory_mode : bool;

    mutable prolific_symb_bound : int;
    mutable lt_threshold : int;

    (*----Sat Mode-----------*)
    mutable sat_mode : bool;
    mutable sat_fm_restart_options : string;
    mutable sat_gr_def : bool;
    mutable sat_epr_types : bool;
    mutable sat_non_cyclic_types : bool;
    mutable sat_finite_models : bool;
    mutable sat_fm_lemmas : bool;
    mutable sat_fm_prep   : bool;
    mutable sat_fm_uc_incr : bool;
    mutable sat_out_model : sat_out_model_type;
    mutable sat_out_clauses : bool;

    (*---- QBF Mode-----------*)
    mutable qbf_mode      : bool;
    mutable qbf_elim_univ : bool;
    mutable qbf_dom_inst  : qbf_dom_inst_type;
    mutable qbf_dom_pre_inst  : bool;
    mutable qbf_sk_in     : bool;
    mutable qbf_pred_elim : bool;
    mutable qbf_split     : int;


    (*----BMC1---------------*)
    mutable bmc1_incremental : bool override;
    mutable bmc1_axioms : bmc1_axioms_type override;
    mutable bmc1_min_bound : int override;
    mutable bmc1_max_bound : int override;
    mutable bmc1_max_bound_default : int override;
    mutable bmc1_symbol_reachability : bool;
    mutable bmc1_property_lemmas : bool;
    mutable bmc1_k_induction : bool;
    mutable bmc1_non_equiv_states : bool;
    mutable bmc1_deadlock : bool;
    mutable bmc1_ucm : bool;
    mutable bmc1_add_unsat_core : bmc1_add_unsat_core_type override;
    mutable bmc1_unsat_core_children : bool override;
    mutable bmc1_unsat_core_extrapolate_axioms : bool override;
    mutable bmc1_ground_init : bool;
    mutable bmc1_pre_inst_next_state : bool;
    mutable bmc1_pre_inst_state : bool;
    mutable bmc1_pre_inst_reach_state : bool;
    mutable bmc1_out_stat : bmc1_out_stat_type override;
    mutable bmc1_out_unsat_core : bool override;
    mutable bmc1_aig_witness_out : bool;
    mutable bmc1_verbose : bool override;
    mutable bmc1_dump_clauses_tptp : bool override;
    mutable bmc1_dump_unsat_core_tptp : bool override;
    mutable bmc1_dump_file : string option override;
    (*----BMC1 UCM --*)
    mutable bmc1_ucm_expand_uc_limit : int;
    mutable bmc1_ucm_n_expand_iterations : int;
    mutable bmc1_ucm_extend_mode : int;
    mutable bmc1_ucm_init_mode : int;
    mutable bmc1_ucm_cone_mode : bmc1_ucm_cone_mode_type;
    mutable bmc1_ucm_reduced_relation_type : int;
    mutable bmc1_ucm_relax_model : int;
    mutable bmc1_ucm_full_tr_after_sat : bool;
    mutable bmc1_ucm_expand_neg_assumptions : bool;
    mutable bmc1_ucm_layered_model : bmc1_ucm_cone_mode_type;
    (* lemmas *)
    mutable bmc1_ucm_max_lemma_size : int;

    (*----AIG----------------*)
    mutable aig_mode : bool;

    (*----Instantiation------*)
    mutable instantiation_flag : bool;
    mutable inst_lit_sel : inst_lit_sel_type;
    mutable inst_lit_sel_side : cl_measure_type;

    mutable inst_solver_per_active : int;
(*    mutable inst_solver_per_clauses : int;
*)
    mutable inst_solver_calls_frac : float;
    mutable inst_passive_queue_type : passive_queue_type;
    mutable inst_passive_queues : pass_queue_list_type;
    mutable inst_passive_queues_freq : passive_queue_freqs;
    mutable inst_dismatching : bool;
    mutable inst_eager_unprocessed_to_passive : bool;
    mutable inst_prop_sim_given : bool;
    mutable inst_prop_sim_new : bool;
    mutable inst_subs_given : bool;
    mutable inst_subs_new : bool;   
    mutable inst_eq_res_simp : bool;
    mutable inst_orphan_elimination : bool;
    mutable inst_learning_loop_flag : bool;
    mutable inst_learning_start : int;
    mutable inst_learning_factor : int;
    mutable inst_start_prop_sim_after_learn : int;
    mutable inst_sel_renew : inst_sel_renew_type;
    mutable inst_lit_activity_flag : bool;
    mutable inst_restr_to_given : bool;
    mutable inst_activity_threshold : int;
    mutable inst_out_proof : bool override;

    (*----Resolution---------*)
    mutable resolution_flag : bool;
    mutable res_lit_sel : res_lit_sel_type;
    mutable res_lit_sel_side : cl_measure_type;
    mutable res_ordering : res_ord_type;
    mutable res_to_prop_solver : res_to_prop_solver_type;
    mutable res_prop_simpl_new : bool;
    mutable res_prop_simpl_given : bool;

    mutable res_passive_queue_type : passive_queue_type;
    mutable res_passive_queues : pass_queue_list_type;
    mutable res_passive_queues_freq : passive_queue_freqs;

    mutable res_forward_subs : res_subs_type;
    mutable res_backward_subs : res_subs_type;
    mutable res_forward_subs_resolution : bool;
    mutable res_backward_subs_resolution : bool;
    mutable res_orphan_elimination : bool;
    mutable res_time_limit : float;
    mutable res_out_proof : bool;
    (*----Combination--------*)
    mutable comb_res_mult : int;
    mutable comb_inst_mult : int;
  }

let default_options () = {

  out_options = ValueDefault Out_All_Opt;
  tptp_safe_out = true; (* for CASC *)

(*
  tptp_safe_out = false;
*)
  (*----Input-------*)
  problem_path = "";
  include_path = "";
  problem_files = [];
  clausifier = "";
  clausifier_options = "";
  stdin = false;
  dbg_backtrace = false;
  dbg_more = false;
  dbg_dump_prop_clauses = false;
  dbg_dump_prop_clauses_file = "-";
  dbg_out_stat = false;

  (*----General--------*)
  fix_init_inter = None;
  time_out_real = -1.;
  time_out_prep_mult = 0.2;
  time_out_virtual = -1.;
  schedule = Schedule_default;
  splitting_mode = Split_Input;
  splitting_grd = false;
  splitting_cvd = true;
  splitting_cvd_svl = true;
  splitting_nvd = 16;
  non_eq_to_eq = false;
  prep_gs_sim = true;
  prep_unflatten = true;
  prep_res_sim = true;
  prep_upred   = true;
  res_sim_input = true;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
  prep_sem_filter = Sem_Filter_Exhaustive;
  prep_sem_filter_out = false;
  preprocessed_out = false;
  preprocessed_stats = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  =  true;
  add_important_lit = false;
  soft_assumptions = false;
  soft_lemma_size = 3;

(*
  prop_impl_unit_size = 20;
  prop_impl_unit = [Lit_bp_epr(true)];
*)
  prop_impl_unit_size = 0; (* for CASC; to preserve proofs *)
  prop_impl_unit = [];

  share_sel_clauses = true;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = []; 
  conj_cone_tolerance = 1.5;
  extra_neg_conj = ENC_none;

  abstr_ref = [];
(*
  abstr_ref_arg_filter = false;
  abstr_ref_sig = false;
  abstr_ref_subs = false;
*)
  abstr_ref_prep = false;
  abstr_ref_until_sat = false;
  (* abstr_terms_sig = false;
   * abstr_skolem_sig = false; *)
  abstr_ref_sig_restrict = Funpre;
  abstr_ref_af_restrict_to_split_sk = false;

  prep_def_merge = false;
  prep_def_merge_prop_impl = false;
  prep_def_merge_mbd = false;
  prep_def_merge_tr_red = false;
  prep_def_merge_tr_cl = false;

(*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*---Sat mode------------*)
  sat_mode = false;
  sat_fm_restart_options = "";
  sat_epr_types = true;
  sat_non_cyclic_types = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep   = false;
(*  sat_fm_uc_incr = false; *)
  sat_fm_uc_incr = true; 
  sat_out_model = Model_Small;
  sat_out_clauses = false;

(*---QBF mode------------*)
  qbf_mode = false;
  qbf_elim_univ = false;
  qbf_dom_inst = QBF_dom_inst_none; (* QBF_dom_inst_chain; *)
  qbf_dom_pre_inst = false;
  qbf_sk_in = false;
  qbf_pred_elim = true;
  qbf_split = 512;

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  (*bmc1_symbol_reachability should be modified only by input options and not by options in schedule since it is calculated before options in schedule become active *)
  bmc1_symbol_reachability = true;
  bmc1_property_lemmas = false;
  bmc1_k_induction = false;
  bmc1_non_equiv_states = false;
  bmc1_deadlock = false;
  bmc1_ucm = false;
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_ground_init = false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_aig_witness_out = false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;
  (*----BMC1 UCM --*)
  bmc1_ucm_expand_uc_limit = 128;
  bmc1_ucm_n_expand_iterations = 6;
  bmc1_ucm_extend_mode = 1;
  bmc1_ucm_init_mode = 2;
  bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_None;
  bmc1_ucm_reduced_relation_type = 0;
  bmc1_ucm_relax_model = 4; (* symbols/clear *)
  bmc1_ucm_full_tr_after_sat = true;
  bmc1_ucm_expand_neg_assumptions = false;
  bmc1_ucm_layered_model = BMC1_Ucm_Cone_Mode_None;
  (* lemmas *)
  bmc1_ucm_max_lemma_size = 10;


  (*----AIG----------------*)
  aig_mode = false;

  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [Lit_Prop true; Lit_Sign true; Lit_Ground true;
		  Lit_Num_of_Var false; Lit_Num_of_Symb false]; (*  CASC 2015*)

  inst_lit_sel_side = CM_num_symb;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 1.0; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 1400; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;2];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = true; 
  inst_prop_sim_new = false;
  inst_subs_given = false;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = true;
  inst_restr_to_given = false;
  inst_activity_threshold = 500;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_adaptive;
  res_lit_sel_side = CM_none;
  res_ordering = Res_ord_kbo;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Full;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = true;
  res_orphan_elimination = true;
  res_time_limit = 2.0;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 300;
  comb_inst_mult = 1000;
}

(*---------*)
let current_options = ref (default_options ())

let set_new_current_options o =
  current_options :=
    { o with

      (* Only override defaults *)
      out_options =
      override o.out_options !current_options.out_options;

      (* Only override defaults *)
      bmc1_incremental =
      override o.bmc1_incremental !current_options.bmc1_incremental;

      (* Only override defaults *)
      bmc1_axioms =
      override o.bmc1_axioms !current_options.bmc1_axioms;

      (* Only override defaults *)
      bmc1_min_bound =
      override o.bmc1_min_bound !current_options.bmc1_min_bound;

      (* Only override defaults *)
      bmc1_max_bound =
      override o.bmc1_max_bound !current_options.bmc1_max_bound;

      (* Only override defaults *)
      bmc1_max_bound_default =
      override
	o.bmc1_max_bound_default
	!current_options.bmc1_max_bound_default;

      (* Only override defaults *)
      bmc1_add_unsat_core =
      override o.bmc1_add_unsat_core !current_options.bmc1_add_unsat_core;

      (* Only override defaults *)
      bmc1_unsat_core_children =
      override
	o.bmc1_unsat_core_children
	!current_options.bmc1_unsat_core_children;

      (* Only override defaults *)
      bmc1_unsat_core_extrapolate_axioms =
      override
	o.bmc1_unsat_core_extrapolate_axioms
	!current_options.bmc1_unsat_core_extrapolate_axioms;

      (* Only override defaults *)
      bmc1_out_stat =
      override o.bmc1_out_stat !current_options.bmc1_out_stat;

      (* Only override defaults *)
      bmc1_out_unsat_core =
      override o.bmc1_out_unsat_core !current_options.bmc1_out_unsat_core;

      (* Only override defaults *)
      bmc1_verbose =
      override o.bmc1_verbose !current_options.bmc1_verbose;

      (* Only override defaults *)
      bmc1_dump_clauses_tptp =
      override
	o.bmc1_dump_clauses_tptp
	!current_options.bmc1_dump_clauses_tptp;

      (* Only override defaults *)
      bmc1_dump_unsat_core_tptp =
      override
	o.bmc1_dump_unsat_core_tptp
	!current_options.bmc1_dump_unsat_core_tptp;

      (* Only override defaults *)
      bmc1_dump_file =
      override o.bmc1_dump_file !current_options.bmc1_dump_file;

      (* Only override defaults *)
      inst_out_proof =
      override
	o.inst_out_proof
	!current_options.inst_out_proof;

    }

(*---------*)
let args_error_msg opt_name str =
  ("Input Options: "^opt_name^" unsupported value \'"^str^"\'")

let add_file_options file_name =
  !current_options.problem_files <- file_name:: (!current_options.problem_files)

let default_arg_fun = add_file_options

(*---------------------Preparing for Args:---------------*)
(* 1. option name  ---*)
(* 2. functions for assigning options------*)
(* 3. description  ---*)
(*-------------------------------*)
let bool_str = "<bool>"
let string_str = "<string>"
let int_str = "<int>"
let float_str = "<float>"
let inf_pref = "\n    "
let example_str = inf_pref^"Example: "

(*-----*)
let out_options_str = "--out_options"

let out_options_fun str =
  try
    !current_options.out_options <-
      override_cmd (str_to_out_options_type str) !current_options.out_options
  with
    Unknown_out_options_type ->
      failwith (args_error_msg out_options_str str)

let out_options_inf =
  "<all | control | none>"^
  inf_pref^"controls output of options \n"

(*--------*)
let tptp_safe_out_str = "--tptp_safe_out"

let tptp_safe_out_fun b =
  Lib.tptp_safe_out_ref:= b;
  !current_options.tptp_safe_out <- b

let tptp_safe_out_inf =
  bool_str^"output all info strings as tptp comments"

(*----Input-------*)

let problem_path_str = "--problem_path"

let problem_path_fun str =
  !current_options.problem_path <- str

let problem_path_inf =
  string_str^
  example_str^problem_path_str^" /home/TPTP/Problems/PUZ/\n"

(*--------*)
let include_path_str = "--include_path"

let include_path_fun str =
  !current_options.include_path <- str

let include_path_inf =
  string_str^
  example_str^include_path_str^" /home/TPTP/\n"

(*--------*)

let clausifier_str = "--clausifier"

let clausifier_fun str =
  !current_options.clausifier <- str

let clausifier_inf =
  string_str^
  inf_pref^"if the input is in cnf this option is ignored"^
  inf_pref^"clausifier is assumed to read fof formulas from stdin and output clauses into stdout"^
  inf_pref^"(see also --clausifier_options)."^
  example_str^"koala --clausifier eprover --clausifier_options \"--tstp-format \" problem.p"^
  inf_pref^"alternatevly, you can use environment variables CLAUSIFIER and CLAUSIFIER_OPTIONS\n"

(*--------*)

let clausifier_options_str = "--clausifier_options"

let clausifier_options_fun str =
  !current_options.clausifier_options <- str

let clausifier_options_inf =
  string_str^
  inf_pref^"options passed to clausifier (see --clausifier)\n"

(*--------*)
let stdin_str = "--stdin"

let stdin_fun bool =
  !current_options.stdin <- bool

let stdin_inf =
  bool_str^
  inf_pref^"read the problem from stdin,"^
  inf_pref^"if the problem is in fof then add \"--fof true\" flag \n"^
  (* ugly hack*)
  (dash_str "General Options")^"\n"

(*--------*)
let dbg_backtrace_str = "--dbg_backtrace"

let dbg_backtrace_fun b =
  (if b
  then
    Printexc.record_backtrace b
  else());
  !current_options.dbg_backtrace <- b

let dbg_backtrace_inf =
  bool_str^
  inf_pref^"debug: backtrace is recorderd and displayed, make iProver with \"make debug=true\" \n"

(*--------*)
let dbg_dump_prop_clauses_str = "--dbg_dump_prop_clauses"

let dbg_dump_prop_clauses_fun b =
  !current_options.dbg_dump_prop_clauses <- b

let dbg_dump_prop_clauses_inf =
  bool_str^
  inf_pref^"debug: dump propositional clauses into stderr\n"

(*--------*)
let dbg_dump_prop_clauses_file_str = "--dbg_dump_prop_clauses_file"

let dbg_dump_prop_clauses_file_fun b =
  !current_options.dbg_dump_prop_clauses_file <- b

let dbg_dump_prop_clauses_file_inf =
  bool_str^
  inf_pref^"debug: file to dump propositional clauses tp, use - for stdout\n"

(*--------*)
let dbg_out_stat_str = "--dbg_out_stat"

let dbg_out_stat_fun b =
  !current_options.dbg_out_stat <- b

let dbg_out_stat_inf =
  "debug: output statistics before proving \n"

(*----General--------*)

let fix_init_inter_str = "--init_inter"

let fix_init_inter_fun b =
  !current_options.fix_init_inter <- Some b

let fix_init_inter_inf =
  bool_str^
  inf_pref^"if false then I- is used, if true I+"

(*--------*)
let time_out_real_str = "--time_out_real"

let time_out_real_fun f =
  !current_options.time_out_real <- f

let time_out_real_inf =
  float_str^
  inf_pref^"time out in real time, if <0. then no time limit is imposed (in real time) \n"

(*--------*)
let time_out_prep_mult_str = "--time_out_prep_mult"

let time_out_prep_mult_fun f =
  !current_options.time_out_prep_mult <- f

let time_out_prep_mult_inf =
  float_str^
  inf_pref^"approx max time spent on preprocessing: time_out_real * time_out_prep_mult   \n"

(*--------*)
let time_out_virtual_str = "--time_out_virtual"

let time_out_virtual_fun f =
  !current_options.time_out_virtual <- f

let time_out_virtual_inf =
  float_str^
  inf_pref^"time out in virtual time, if <0. then no time limit is imposed (in virtual time) \n"

(*--------*)
let schedule_str = "--schedule"

let schedule_fun str =
  try
    !current_options.schedule <- str_to_schedule_type str
  with
    Unknown_schedule_type ->
      failwith (args_error_msg schedule_str str)

let schedule_inf =
  schedule_type_list_str^
  inf_pref^"run a specified strategy schedule:"^
  inf_pref^"\"default\" is the default schedule, works well over whole TPTP"^
  inf_pref^"\"none\" run just the input options, without a schedule"^
  inf_pref^"\"verification_epr\" a schedule which works well for verification problems encoded in the EPR fragment"^
  inf_pref^"in the future there will be an interface for the schedule to be read from an option file\n"

(*--------*)
let splitting_mode_str = "--splitting_mode"

let splitting_mode_fun str =
  try
    !current_options.splitting_mode <- (str_to_splitting_mode_type str)
  with
    Unknown_splitting_mode_type ->
      failwith (args_error_msg splitting_mode_str str)

let splitting_mode_inf =
  splitting_mode_type_str^
  inf_pref^"splitting of clauses on maximal variable-disjoint parts\n"

(*--------*)
let splitting_grd_str = "--splitting_grd"

let splitting_grd_fun b =
    !current_options.splitting_grd <- b

let splitting_grd_inf =
  bool_str^
  inf_pref^"splitting: variable-disjoint\n"

(*--------*)
let splitting_cvd_str = "--splitting_cvd"

let splitting_cvd_fun b =
    !current_options.splitting_cvd <- b

let splitting_cvd_inf =
  bool_str^
  inf_pref^"splitting: non-variable disjoint with non-trivial variable separation\n"

(*--------*)
let splitting_cvd_svl_str = "--splitting_cvd_svl"

let splitting_cvd_svl_fun b =
    !current_options.splitting_cvd_svl <- b

let splitting_cvd_svl_inf =
  bool_str^
  inf_pref^"splitting: a modification of cvd where literals adjoint to the current split if its vars are subset of vars  of the split; only active when --splitting_cvd true \n"


(*--------*)
let splitting_nvd_str = "--splitting_nvd"

let splitting_nvd_fun i =
    !current_options.splitting_nvd <- i

let splitting_nvd_inf =
  int_str^
  inf_pref^"splitting ignoring var separation of length 2*splitting_nvd into chuncks of size splitting_nvd; <=0 no splitting is applied\n"

(*--------*)

let non_eq_to_eq_str = "--non_eq_to_eq"

let non_eq_to_eq_fun b =
  !current_options.non_eq_to_eq <- b

let non_eq_to_eq_inf =
  bool_str^
  inf_pref^"replace all non-equational predicates with equational"^
  inf_pref^"e.g. p with f_p = top and  ~p with f_p != top\n"

(*--------*)
let prep_gs_sim_str = "--prep_gs_sim"

let prep_gs_sim_fun b =
  !current_options.prep_gs_sim <- b

let prep_gs_sim_inf =
  bool_str^
  inf_pref^"simplify input first-order clauses using propositional solver by global subsumption\n"

(*--------*)
let prep_unflatten_str = "--prep_unflatten"

let prep_unflatten_fun b =
  !current_options.prep_unflatten <- b

let prep_unflatten_inf =
  bool_str^
  inf_pref^"x!=t \\/ C[x] is simplified to C[t] where x is not in t \n"


(*--------*)
let prep_res_sim_str = "--prep_res_sim"

let prep_res_sim_fun b =
  !current_options.prep_res_sim <- b

let prep_res_sim_inf =
  bool_str^
  inf_pref^"preprocess simplification using resolution type simplifications such as subsumtion, subsumption resolution, etc.\n"

(*--------*)
let prep_upred_str = "--prep_upred"

let prep_upred_fun b =
  !current_options.prep_upred <- b

let prep_upred_inf =
  bool_str^
  inf_pref^"preprocess unary predicates \n"

 
(*--------*)
let clause_weak_htbl_str = "--clause_weak_htbl"

let clause_weak_htbl_fun b =
  !current_options.clause_weak_htbl <- b

let clause_weak_htbl_inf =
  bool_str^
  inf_pref^"use weak hash table to store all basic clauses; should not be switched in schedules\n"

(*--------*)
let gc_record_bc_elim_str = "--gc_record_bc_elim"

let gc_record_bc_elim_fun b =
  !current_options.gc_record_bc_elim <- b

let gc_record_bc_elim_inf =
  bool_str^
  inf_pref^"record the number of eliminated clauses by the garbage collector in gc_basic_clause_elim; only when --clause_weak_htbl true\n"

(*--------*)
let res_sim_input_str = "--res_sim_input"

let res_sim_input_fun b =
  !current_options.res_sim_input <- b

let res_sim_input_inf =
  bool_str^
  inf_pref^"after a reseolution run, simplify input clauses for the next iterations of inst/res\n"


(*--------*)
let symbol_type_check_str = "--symbol_type_check"

let symbol_type_check_fun b =
  !current_options.symbol_type_check <- b

let symbol_type_check_inf =
  bool_str^
  inf_pref^"if true then it is checked whether there is no symbols with the same name and different types\n"

(*-------*)
let clausify_out_str = "--clausify_out"

let clausify_out_fun b =
  !current_options.clausify_out <- b

let clausify_out_inf =
  bool_str^
  inf_pref^"output the clausifier output and exit\n"

(*-------*)
let prep_sem_filter_str = "--prep_sem_filter"

let prep_sem_filter_fun str =
  try
    !current_options.prep_sem_filter <- (str_to_prep_sem_filter_type str)
  with
    Unknown_sem_filter_type ->
      failwith (args_error_msg prep_sem_filter_str str)

let prep_sem_filter_inf =
  prep_sem_filter_type_str^
  inf_pref^"apply semantic filter to the input clauses \n"

(*-------*)
let prep_sem_filter_out_str = "--prep_sem_filter_out"

let prep_sem_filter_out_fun b =
  !current_options.prep_sem_filter_out <- b

let prep_sem_filter_out_inf =
  bool_str^
  inf_pref^"semantic preproscessing of the input set, output prepocessing result and exit\n"

(*-------*)

let preprocessed_out_str = "--preprocessed_out"

let preprocessed_out_fun b =
  !current_options.preprocessed_out <- b

let preprocessed_out_inf =
  bool_str^
  inf_pref^"output result of the prepocessing and exit\n"


(*-------*)

let preprocessed_stats_str = "--preprocessed_stats"

let preprocessed_stats_fun b =
  !current_options.preprocessed_stats <- b

let preprocessed_stats_inf =
  bool_str^
  inf_pref^"output statistics after prepocessing and exit\n"


(*-------*)
let sub_typing_str = "--sub_typing"

let sub_typing_fun b =
  !current_options.sub_typing <- b

let sub_typing_inf =
  bool_str^
  inf_pref^"sub-type signature"

(*-------*)
let eq_ax_congr_red_str = "--eq_ax_congr_red"

let eq_ax_congr_red_fun b = 
   !current_options.eq_ax_congr_red <-b 

let eq_ax_congr_red_inf = 
  bool_str^
  inf_pref^"reduction of congruence axioms based on flat arguments\n"^
  inf_pref^"should be set false when clauses are non-conservarivly extended e.g. in BMC \n"

(*-------*)
let brand_transform_str = "--brand_transform"

let brand_transform_fun b =
  !current_options.brand_transform <- b

let brand_transform_inf =
  bool_str^
  inf_pref^"apply Brand's transformation to remove equality monotonicity axioms by flattening clauses\n"

(*-------*)
let pure_diseq_elim_str = "--pure_diseq_elim"

let pure_diseq_elim_fun b = 
  !current_options.pure_diseq_elim <- b

let pure_diseq_elim_inf = 
  bool_str^
  inf_pref^"elimination of pure disequalities\n"

(*-------*)
let min_unsat_core_str = "--min_unsat_core"

let min_unsat_core_fun b =
  !current_options.min_unsat_core <- b

let min_unsat_core_inf =
  bool_str^
  inf_pref^"minimise unsat core whenever is used; can be expenisve but can lead to shorter proofs and current state: for proofs better true for bmc1 better false \n"

(*-------*)

let pred_elim_str = "--pred_elim"

let pred_elim_fun b = 
  !current_options.pred_elim <-b 

let pred_elim_inf = 
  bool_str^
  inf_pref^"predicate elimination"

(*-------*)

let add_important_lit_str = "--add_important_lit"

let add_important_lit_fun b =
  !current_options.add_important_lit <- b

let add_important_lit_inf =
  bool_str^
  inf_pref^"control the addition of important literals to a SAT solver that supports it\n"

(*-------*)

let soft_assumptions_str = "--soft_assumptions"

let soft_assumptions_fun b =
  !current_options.soft_assumptions <- b

let soft_assumptions_inf =
  bool_str^
  inf_pref^"control the usage of 'soft assumptions' in the SAT solver. If a soft assumption was the reason of UNSAT result, the latter is discarded\n"

(*-------*)

let soft_lemma_size_str = "--soft_lemma_size"

let soft_lemma_size_fun i =
  !current_options.soft_lemma_size <- i

let soft_lemma_size_inf =
  int_str^
  inf_pref^"bound on the lemma size when learning  based on uc from soft assumptions; active only when --soft_assumption true  \n"

(*-------*)

let prop_impl_unit_size_str = "--prop_impl_unit_size"

let prop_impl_unit_size_fun i =
  !current_options.prop_impl_unit_size <- i

let prop_impl_unit_size_inf =
  int_str^
  inf_pref^" add propositonally implied unit clauses if the size <= prop_impl_unit_size;"^
  inf_pref^" if prop_impl_unit_size=0 then impl. prop units are not added \n"


(*--------*)

let prop_impl_unit_str = "--prop_impl_unit"

let prop_impl_unit_fun str =
  try
    let str_list = parse_list_opt str in
    let prop_impl_unit = List.map str_to_lit_bool_prop_type str_list in
    !current_options.prop_impl_unit <- prop_impl_unit
  with
  | Parse_list_fail | Unknown_lit_bool_prop_type ->
      failwith (args_error_msg prop_impl_unit_str str)

let prop_impl_unit_inf =
  lit_bool_prop_type_list_str^
  inf_pref^"active when prop_impl_unit_size > 0"^
  inf_pref^"prop impl literals are added only if they satisfy conjunction of listed properties"^
  inf_pref^"[] -- there is no restriction on lit properties\n"

(*--------*)

let share_sel_clauses_str = "--share_sel_clauses"

let share_sel_clauses_fun b =
  !current_options.share_sel_clauses <-  b

let share_sel_clauses_inf =
  bool_str^
  inf_pref^"share selected implied clauses between proof_search runs; currently prop_impl_unit clauses \n"

(*--------*)

let reset_solvers_str = "--reset_solvers"

let reset_solvers_fun b =
  !current_options.reset_solvers <-  b

let reset_solvers_inf =
  bool_str^
  inf_pref^"reset SAT solvers during UCM\n"

(*--------*)
let bc_imp_inh_str = "--bc_imp_inh" 

let bc_imp_inh_fun str = 
  try
    !current_options.bc_imp_inh <- (str_to_bc_imp_inh_list_type str);    
  with
    Unknown_bc_imp_inh_type ->
      failwith (args_error_msg bc_imp_inh_str str)
 

let bc_imp_inh_inf = 
  bc_imp_inh_list_type_str^
  inf_pref^"improtant clauses in decreasing priority order; importance is inherited with main premise"^
  inf_pref^"use in conjunction with passive queues parameter: +/-bc_imp_inh in instantiation and resolution;"^
  inf_pref^"see --inst_passive_queues and --res_passive_queues"^
  inf_pref^"if [] then all clauses have the same importance \n"
	      

(* maps bc_imp_inh into integer priorities; *)
(* priority decreases with values highest priority is 0, lowest max_int *)
(* priorities are grouped in blocks by shifting by 8 bits;  *)   

let bc_imp_inh_default_val = max_int 

let bc_block_shift = 256

(* shift by which priority should be shifted (added to the priority; first element is 0) *)
let get_bc_imp_inh_shift options bc_imp_inh_type =
  let bc_imp_inh = options.bc_imp_inh in
  try    
    let position = list_find_pos bc_imp_inh (fun x -> x == bc_imp_inh_type) in
    assert(position < max_int/bc_block_shift);
    position*bc_block_shift
  with 
    Not_found -> 
      bc_imp_inh_default_val

let bc_imp_inh_exists options bc_imp_inh_type = 
  List.exists (fun x -> x == bc_imp_inh_type) options.bc_imp_inh


(*------------------------*)

let conj_cone_tolerance_str = "--conj_cone_tolerance"

let conj_cone_tolerance_fun f =
  !current_options.conj_cone_tolerance <- f
      
let conj_cone_tolerance_inf =
  float_str^
  inf_pref^"tolerance param for conj_cone; see --bc_imp_inh\n"

(*------------------------*)
  
let extra_neg_conj_str = "--extra_neg_conj"

let extra_neg_conj_fun str = 
  try
    !current_options.extra_neg_conj <- (str_to_extra_neg_conj_type str);    
  with
    Unknown_extra_neg_conj ->    
      failwith (args_error_msg extra_neg_conj_str str)

let extra_neg_conj_inf = 
  extra_neg_conj_type_str^
  inf_pref^" adds extra neg conjecture annotations to clauses with all neg/pos lits or both all neg all pos  in the case of all_pos_neg\n"

(*------------------------*)

let abstr_ref_str = "--abstr_ref"

let abstr_ref_fun str = 
  try
    !current_options.abstr_ref <- (str_to_abstr_ref_list_type str);
  with 
    Unknown_abstr_ref_type -> 
      failwith (args_error_msg abstr_ref_str str)

let abstr_ref_inf = 
  abstr_ref_list_type_str^
  inf_pref^" abstraction refinement types: subs -- subsumtion-based; sig -- signature merging; arg_filter -- argument filter; [] -- do not apply abstr_ref \n"
              
(*
(*------------------------*)

let abstr_ref_arg_filter_str = "--abstr_ref_arg_filter"

let abstr_ref_arg_filter_fun b =
  !current_options.abstr_ref_arg_filter <- b
      
let abstr_ref_arg_filter_inf =
  bool_str^
  inf_pref^" abstraction refinement using argument filter \n"
    
(*------------------------*)

let abstr_ref_sig_str = "--abstr_ref_sig"

let abstr_ref_sig_fun b =
  !current_options.abstr_ref_sig <- b

let abstr_ref_sig_inf =
  bool_str^
  inf_pref^" abstraction refinement using signature merging \n"

(*------------------------*)

let abstr_ref_subs_str = "--abstr_ref_subs"

let abstr_ref_subs_fun b =
  !current_options.abstr_ref_subs <- b

let abstr_ref_subs_inf =
  bool_str^
  inf_pref^" abstraction refinement using subsumption \n"

*)

(*------------------------*)

let abstr_ref_prep_str = "--abstr_ref_prep"

let abstr_ref_prep_fun b =
  !current_options.abstr_ref_prep <- b

let abstr_ref_prep_inf =
  bool_str^
  inf_pref^" abstraction refinement: prepocess before each cycle \n"


(*------------------------*)

let abstr_ref_until_sat_str = "--abstr_ref_until_sat"

let abstr_ref_until_sat_fun b =
  !current_options.abstr_ref_until_sat <- b

let abstr_ref_until_sat_inf =
  bool_str^
  inf_pref^" abstraction refinement using refinement until SAT \n"

(*------------------------*)

(* let abstr_terms_sig_str = "--abstr_terms_sig"
 * 
 * let abstr_terms_sig_fun b =
 *   !current_options.abstr_terms_sig <- b
 * 
 * let abstr_terms_sig_inf =
 *   bool_str^
 *   inf_pref^" abstraction of functions and predicates in the signature\n" *)

(*------------------------*)

(* let abstr_skolem_sig_str = "--abstr_skolem_sig"
 * 
 * let abstr_skolem_sig_fun b =
 *   !current_options.abstr_skolem_sig <- b
 * 
 * let abstr_skolem_sig_inf =
 *   bool_str^
 *   inf_pref^" abstraction of skolem terms in the signature\n" *)

(*------------------------*)

let abstr_ref_sig_restrict_str = "--abstr_ref_sig_restrict"

let abstr_ref_sig_restrict_fun str =
  try
    !current_options.abstr_ref_sig_restrict <- (str_to_abstr_ref_sig_restrict_type str);
  with
    Unknown_abstr_ref_sig_restrict_type ->
      failwith (args_error_msg abstr_ref_sig_restrict_str str)

let abstr_ref_sig_restrict_inf =
  abstr_ref_sig_restrict_str^
  inf_pref^" signature grouping abstraction restrict to: funpre -- functions and predicates; skc -- Skolem functions and constants\n"

(*------------------------*)

let abstr_ref_af_restrict_to_split_sk_str = "--abstr_ref_af_restrict_to_split_sk"

let abstr_ref_af_restrict_to_split_sk_fun b =
  !current_options.abstr_ref_af_restrict_to_split_sk <- b

let abstr_ref_af_restrict_to_split_sk_inf =
  bool_str^
  inf_pref^" argument filter abstraction restrict to spliting and Skolem symbols\n"

(*------------------------*)

let prep_def_merge_str = "--prep_def_merge"

let prep_def_merge_fun b = 
  !current_options.prep_def_merge <- b

let prep_def_merge_inf = 
  bool_str^ 
  inf_pref^"preprocessing merging definitions"

(*------------------------*)
let prep_def_merge_prop_impl_str = "--prep_def_merge_prop_impl"

let prep_def_merge_prop_impl_fun b = 
  !current_options.prep_def_merge_prop_impl <- b

let prep_def_merge_prop_impl_inf = 
  bool_str^ 
  inf_pref^"active only if --prep_def_merge true, if --prep_def_merge_prop_impl false then use binary clauses for def merge; otherwise also use prop impl definitions;\n"

(*------------------------*)
let prep_def_merge_mbd_str = "--prep_def_merge_mbd" 

let prep_def_merge_mbd_fun b = 
  !current_options.prep_def_merge_mbd <- b

let prep_def_merge_mbd_inf = 
  bool_str^
  inf_pref^"active when --prep_def_merge true"^
  inf_pref^"if true defintions are applied based on fof matching otherwise based on syntactic equality\n"
    
(*------------------------*)
let prep_def_merge_tr_red_str = "--prep_def_merge_tr_red"

let prep_def_merge_tr_red_fun b = 
  !current_options.prep_def_merge_tr_red <- b

let prep_def_merge_tr_red_inf = 
  bool_str^
  inf_pref^"active when --prep_def_merge true; assume --prep_def_merge_tr_cl false"^  
  inf_pref^"apply transitive reduction to merged definitions\n"
 
(*------------------------*)
let prep_def_merge_tr_cl_str = "--prep_def_merge_tr_cl"

let prep_def_merge_tr_cl_fun b = 
  !current_options.prep_def_merge_tr_cl <- b

let prep_def_merge_tr_cl_inf = 
  bool_str^
  inf_pref^"active when --prep_def_merge true; assume --prep_def_merge_tr_red false "^  
  inf_pref^"apply transitive closure to merged definitions\n"
  

(*-------Large Theories---------------*)

let large_theory_mode_str = "--large_theory_mode"

let large_theory_mode_fun b =
  !current_options.large_theory_mode <- b

let large_theory_mode_inf =
  bool_str^
  inf_pref^"Large theory mode\n"

(*--------*)

let prolific_symb_bound_str = "--prolific_symb_bound"

let prolific_symb_bound_fun int =
  !current_options.prolific_symb_bound <- int

let prolific_symb_bound_inf =
  int_str^
  inf_pref^"Large theory mode: if the number of occurrences of a symbol in the input is greater or equal to "^
  inf_pref^"prolific_symb_bound then the symbol is declared as prolific\n"

(*--------*)
let lt_threshold_str = "--lt_threshold"

let lt_threshold_fun int =
  !current_options.lt_threshold <- int

let lt_threshold_inf =
  int_str^
  inf_pref^"Large theory mode: if the number of input clauses >= threshold then the theory is considered to be large\n"^
  (dash_str "SAT Options")^"\n"

(*---Sat Mode-----*)
let sat_mode_str = "--sat_mode"

let sat_mode_fun b =
  !current_options.sat_mode <- b

let sat_mode_inf =
  bool_str^
  inf_pref^"Satisfiability mode \n"

(*--------*)

let sat_fm_restart_options_str = "--sat_fm_restart_options"

let sat_fm_restart_options_fun s = 
  !current_options.sat_fm_restart_options <- s

let sat_fm_restart_options_inf = 
  string_str^
  inf_pref^" This option is not supported yet. If the option is not not empty then, when sat schedule reaches finite models iprover is re-run with the new options \n"

(*--------*)
let sat_gr_def_str = "--sat_gr_def"

let sat_gr_def_fun b =
  !current_options.sat_gr_def <- b

let sat_gr_def_inf =
  bool_str^
  inf_pref^"Add definitions of ground terms in sat mode (!!do not use for now!!)\n"

(*--------*)
let sat_epr_types_str = "--sat_epr_types"

let sat_epr_types_fun b =
  !current_options.sat_epr_types <- b

let sat_epr_types_inf =
  bool_str^
  inf_pref^"using EPR types in sat mode\n"

(*--------*)
let sat_non_cyclic_types_str = "--sat_non_cyclic_types"

let sat_non_cyclic_types_fun b =
  !current_options.sat_non_cyclic_types <- b

let sat_non_cyclic_types_inf =
  bool_str^
  inf_pref^"using non cyclic types in sat mode\n"

(*--------*)
let sat_finite_models_str = "--sat_finite_models"

let sat_finite_models_fun b =
  !current_options.sat_finite_models <- b

let sat_finite_models_inf =
  bool_str^
  inf_pref^"Finite model finder, sat_mode should be true\n"


(*--------*)
let sat_fm_lemmas_str = "--sat_fm_lemmas"

let sat_fm_lemmas_fun b =
  !current_options.sat_fm_lemmas <- b

let sat_fm_lemmas_inf =
  bool_str^
  inf_pref^"finite model finder with lemmas; sat_mode should be true\n"

(*--------*)
let sat_fm_prep_str = "--sat_fm_prep"

let sat_fm_prep_fun b =
  !current_options.sat_fm_prep <- b

let sat_fm_prep_inf =
  bool_str^
  inf_pref^"finite model finder: preprocess at each cycle\n"

(*--------*)
let sat_fm_uc_incr_str = "--sat_fm_uc_incr"

let sat_fm_uc_incr_fun b =
  !current_options.sat_fm_uc_incr <- b

let sat_fm_uc_incr_inf =
  bool_str^
  inf_pref^"finite model finder: increments based on unsat cores\n"

(*--------*)
let sat_out_model_str = "--sat_out_model"

let sat_out_model_fun str =
  try
    !current_options.sat_out_model <- str_to_sat_out_model_type str
  with
    Unknown_sat_model_out_type ->
      failwith (args_error_msg sat_out_model_str str)

let sat_out_model_inf =
  sat_out_model_type_str^
  inf_pref^"Outputs model if the input is shown satisfiable by instantiation. "^
  inf_pref^"Models are defined over ground terms (initial term algebra) "^
  inf_pref^"Predicates are defined as (\\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\\phi(x_1,..,x_n)))) "^
  inf_pref^"where \\phi is a formula over the term algebra"^
  inf_pref^"If we have equality in the problem then it is also defined as a predicate above.\n"^
  inf_pref^"Using options we can output different models:"^
  inf_pref^"pos     -- using positive definitions (\\forall x_1,..,x_n  (P(x_1,..,x_n) <=> (\\phi(x_1,..,x_n))))"^
  inf_pref^"neg     -- using negative definitions (\\forall x_1,..,x_n  (~P(x_1,..,x_n) <=> (\\phi(x_1,..,x_n))))"^
  inf_pref^"small   -- choosing between positive and negative definitions according to the size "^
  inf_pref^"implied -- definitions of the form (\\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <= (\\phi(x_1,..,x_n)))) "^
  inf_pref^"           if for some arguments a value of a predicate is not implied by these definitions "^
  inf_pref^"           then we can complete the model by choosing an arbitrary value of this predicate on these arguments"^
  inf_pref^"debug   -- in addition outputs 1) clauses with selected literals in the form {|L|;L_1;...;L_n}"^
  inf_pref^"           where |L| is the selected literal and 2) constraints"^
  inf_pref^"           Using debug it is possible to recover the justification of why each clause is true in the model\n"^
  inf_pref^"none     -- no model output \n"

(*--------*)
let sat_out_clauses_str = "--sat_out_clauses"

let sat_out_clauses_fun b =
  !current_options.sat_out_clauses <- b

let sat_out_clauses_inf =
  bool_str^
  inf_pref^"Outputs all active clauses if the input is show satisfiable. \n"^
  (* ugly hack *)
  (dash_str "BMC1 Options")^"\n"

(*----------------QBF--------------*)

let qbf_mode_str = "--qbf_mode"

let qbf_mode_fun b =
  !current_options.qbf_mode <- b

let qbf_mode_inf =
  bool_str^
  inf_pref^"QBF mode;  QDIMACS input \n"

(*-----*)
let qbf_elim_univ_str = "--qbf_elim_univ"

let qbf_elim_univ_fun b =
  !current_options.qbf_elim_univ <- b

let qbf_elim_univ_inf =
  bool_str^
  inf_pref^"QBF eliminate predicates corresponding to the universally quantified variables\n"

(*-----*)
let qbf_dom_inst_str = "--qbf_dom_inst"

let qbf_dom_inst_fun str =
  try
    !current_options.qbf_dom_inst <- (str_to_qbf_dom_inst_type str)
  with 
    Unknown_qbf_dom_inst_type ->  failwith (args_error_msg qbf_dom_inst_type_str str)
      
let qbf_dom_inst_inf =
  qbf_dom_inst_type_str^
  inf_pref^"domain instantiate universal variables in proper instantiators during Inst-Gen loop\n"

(*-----*)

let qbf_dom_pre_inst_str = "--qbf_dom_pre_inst"

let qbf_dom_pre_inst_fun b =
  !current_options.qbf_dom_pre_inst <- b

let qbf_dom_pre_inst_inf =
  bool_str^
  inf_pref^"QBF: domain pre instantiation\n"


(*-----*)

let qbf_sk_in_str = "--qbf_sk_in"

let qbf_sk_in_fun b =
  !current_options.qbf_sk_in <- b

let qbf_sk_in_inf =
  bool_str^
  inf_pref^"QBF: inner Skolemization\n"

(*-----*)

let qbf_pred_elim_str = "--qbf_pred_elim"

let qbf_pred_elim_fun b =
  !current_options.qbf_pred_elim <- b

let qbf_pred_elim_inf =
  bool_str^
  inf_pref^"QBF: pred_elim at the qbf level\n"


(*-----*)

let qbf_split_str = "--qbf_split"

let qbf_split_fun i =
  !current_options.qbf_split <- i

let qbf_split_inf =
  bool_str^
  inf_pref^"QBF: split clauses of length 2*qbf_split into chuncks of size qbf_split \n"



(*----BMC1---------------*)

let bmc1_incremental_str = "--bmc1_incremental"

let bmc1_incremental_fun b =
  !current_options.bmc1_incremental <-
    override_cmd b !current_options.bmc1_incremental

let bmc1_incremental_inf =
  bool_str^
  inf_pref^"incrementally increase bounds in BMC1\n"

(*--------*)

let bmc1_axioms_str = "--bmc1_axioms"

let bmc1_axioms_fun str =
  try
    !current_options.bmc1_axioms <-
      (override_cmd
	 (str_to_bmc1_axioms_type str)
	 !current_options.bmc1_axioms)
  with
    Unknown_bmc1_axioms_type ->
      failwith (args_error_msg bmc1_axioms_str str)

let bmc1_axioms_inf =
  bmc1_axioms_type_list_str^
  inf_pref^"axioms for BMC1\n"

(*--------*)

let bmc1_min_bound_str = "--bmc1_min_bound"

let bmc1_min_bound_fun b =
  !current_options.bmc1_min_bound <-
    override_cmd b !current_options.bmc1_min_bound

let bmc1_min_bound_inf =
  int_str^
  inf_pref^"starting bound in BMC1\n"

(*--------*)

let bmc1_max_bound_str = "--bmc1_max_bound"

let bmc1_max_bound_fun b =
  !current_options.bmc1_max_bound <-
    override_cmd b !current_options.bmc1_max_bound

let bmc1_max_bound_inf =
  int_str^
  inf_pref^"maximal bound in BMC1, -1 for unlimited\n"

(*--------*)

let bmc1_max_bound_default_str = "--bmc1_max_bound_default"

let bmc1_max_bound_default_fun b =
  !current_options.bmc1_max_bound_default <-
    override_cmd b !current_options.bmc1_max_bound_default

let bmc1_max_bound_default_inf =
  int_str^
  inf_pref^"maximal bound in BMC1 unless higher bound from file\n"

(*--------*)

let bmc1_symbol_reachability_str = "--bmc1_symbol_reachability"

let bmc1_symbol_reachability_fun b =
  !current_options.bmc1_symbol_reachability <- b

let bmc1_symbol_reachability_inf =
  bool_str^
  inf_pref^"calculate symbol reachability for father/son relation in Intel BMC1; \n"


(*--------*)

let bmc1_property_lemmas_str = "--bmc1_property_lemmas"

let bmc1_property_lemmas_fun b =
  !current_options.bmc1_property_lemmas <- b

let bmc1_property_lemmas_inf =
  bool_str^
  inf_pref^"create property predicate \\psi(X)<->prop(X) in Intel BMC1; \n"

(*--------*)

let bmc1_k_induction_str = "--bmc1_k_induction"

let bmc1_k_induction_fun b =
  !current_options.bmc1_k_induction <- b

let bmc1_k_induction_inf =
  bool_str^
  inf_pref^"run unbounded model checking using k-induction in Intel BMC1; \n"

(*--------*)

let bmc1_non_equiv_states_str = "--bmc1_non_equiv_states"

let bmc1_non_equiv_states_fun b =
  !current_options.bmc1_non_equiv_states <- b

let bmc1_non_equiv_states_inf =
  bool_str^
  inf_pref^"in k-induction: postulate that all the states are different;\n"

(*--------*)

let bmc1_deadlock_str = "--bmc1_deadlock"

let bmc1_deadlock_fun b =
  !current_options.bmc1_deadlock <- b

let bmc1_deadlock_inf =
  bool_str^
  inf_pref^"introduce $$deadlock(S) predicate in Intel BMC1; \n"

(*--------*)

let bmc1_ucm_str = "--bmc1_ucm"

let bmc1_ucm_fun b =
  !current_options.bmc1_ucm <- b

let bmc1_ucm_inf =
  bool_str^
  inf_pref^"Use non-monolythic $$nextState(S,S') and $$init(S) predicates but rather $$nextState(i,S,S') and $$init(i,S)\n"

(*--------*)

let bmc1_add_unsat_core_str = "--bmc1_add_unsat_core"

let bmc1_add_unsat_core_fun str =
  try
    !current_options.bmc1_add_unsat_core <-
      override_cmd
	(str_to_bmc1_add_unsat_core_type str)
	!current_options.bmc1_add_unsat_core
  with
    Unknown_bmc1_add_unsat_core_type ->
      failwith (args_error_msg bmc1_add_unsat_core_str str)

let bmc1_add_unsat_core_inf =
  bmc1_add_unsat_core_type_list_str^
  inf_pref^"add clauses in unsatisfiable core to next bound in BMC1\n"

(*--------*)

let bmc1_unsat_core_children_str = "--bmc1_unsat_core_children"

let bmc1_unsat_core_children_fun b =
  !current_options.bmc1_unsat_core_children <-
    override_cmd b !current_options.bmc1_unsat_core_children

let bmc1_unsat_core_children_inf =
  bool_str^
  inf_pref^"children of unsat core clauses are considered in unsat core\n"

(*--------*)

let bmc1_unsat_core_extrapolate_axioms_str =
  "--bmc1_unsat_core_extrapolate_axioms"

let bmc1_unsat_core_extrapolate_axioms_fun b =
  !current_options.bmc1_unsat_core_extrapolate_axioms <-
    override_cmd b !current_options.bmc1_unsat_core_extrapolate_axioms

let bmc1_unsat_core_extrapolate_axioms_inf =
  bool_str^
  inf_pref^"extrapolate axioms to next bound in unsat core\n"

(*--------*)

let bmc1_out_stat_str = "--bmc1_out_stat"

let bmc1_out_stat_fun str =
  try
    !current_options.bmc1_out_stat <-
      (override_cmd
	 (str_to_bmc1_out_stat_type str)
	 !current_options.bmc1_out_stat)
  with
    Unknown_bmc1_out_stat_type ->
      failwith (args_error_msg bmc1_out_stat_str str)

let bmc1_out_stat_inf =
  bmc1_out_stat_type_list_str^
  inf_pref^"output no statistics, after the last bound only or after each bound (full)\n"

(*--------*)
let bmc1_ground_init_str = "--bmc1_ground_init"

let bmc1_ground_init_fun b =
  !current_options.bmc1_ground_init <- b

let bmc1_ground_init_inf =
  bool_str^
  inf_pref^"ground $$init axioms for every bound\n"

(*--------*)
let bmc1_pre_inst_next_state_str = "--bmc1_pre_inst_next_state"

let bmc1_pre_inst_next_state_fun b =
  !current_options.bmc1_pre_inst_next_state <- b

let bmc1_pre_inst_next_state_inf =
  bool_str^
  inf_pref^"pre-instantiate $$nextState(x,y) -> phi(x,y) axioms \n"

(*--------*)
let bmc1_pre_inst_state_str = "--bmc1_pre_inst_state"

let bmc1_pre_inst_state_fun b =
  !current_options.bmc1_pre_inst_state <- b

let bmc1_pre_inst_state_inf =
  bool_str^
  inf_pref^"pre-instantiate clauses with state variables by the current bound; \n"^
  inf_pref^"if \"--bmc1_pre_inst_state true\" then it  should be --bmc1_pre_inst_next_state true and --bmc1_pre_inst_reach_state true\n"

(*--------*)
let bmc1_pre_inst_reach_state_str = "--bmc1_pre_inst_reach_state"

let bmc1_pre_inst_reach_state_fun b =
  !current_options.bmc1_pre_inst_reach_state <- b

let bmc1_pre_inst_reach_state_inf =
  bool_str^
  inf_pref^"pre-instantiate $$reachableState(X) -> X = $$constB0 \\/...\\/X=$$constBn axioms \n"

(*--------*)

let bmc1_out_unsat_core_str = "--bmc1_out_unsat_core"

let bmc1_out_unsat_core_fun b =
  !current_options.bmc1_out_unsat_core <-
    override_cmd b !current_options.bmc1_out_unsat_core

let bmc1_out_unsat_core_inf =
  bool_str^
  inf_pref^"output unsat core for each bound in BMC1\n"

(*--------*)

let bmc1_aig_witness_out_str = "--bmc1_aig_witness_out"

let bmc1_aig_witness_out_fun b =
  !current_options.bmc1_aig_witness_out <- b

let bmc1_aig_witness_out_inf =
  bool_str^
  inf_pref^"output AIG witness for satisfiable fproblems in BMC1\n"

(*--------*)

let bmc1_dump_clauses_tptp_str = "--bmc1_dump_clauses_tptp"

let bmc1_dump_clauses_tptp_fun b =
  !current_options.bmc1_dump_clauses_tptp <-
    override_cmd b !current_options.bmc1_dump_clauses_tptp

let bmc1_dump_clauses_tptp_inf =
  bool_str^
  inf_pref^"dump clauses for each bound in BMC1 in TPTP format\n"

(*--------*)

let bmc1_dump_unsat_core_tptp_str = "--bmc1_dump_unsat_core_tptp"

let bmc1_dump_unsat_core_tptp_fun b =
  !current_options.bmc1_dump_unsat_core_tptp <-
    override_cmd b !current_options.bmc1_dump_unsat_core_tptp

let bmc1_dump_unsat_core_tptp_inf =
  bool_str^
  inf_pref^"dump unsat core for each bound in BMC1 in TPTP format\n"

(*--------*)

let bmc1_dump_file_str = "--bmc1_dump_file"

let bmc1_dump_file_fun b =
  !current_options.bmc1_dump_file <-
    override_cmd (Some b) !current_options.bmc1_dump_file

let bmc1_dump_file_inf =
  bool_str^
  inf_pref^"file to write clauses into\n"

(*--------*)

let bmc1_verbose_str = "--bmc1_verbose"

let bmc1_verbose_fun b =
  !current_options.bmc1_verbose <-
    override_cmd b !current_options.bmc1_verbose

let bmc1_verbose_inf =
  bool_str^
  inf_pref^"print detailed output during incremental BMC1\n"

(*----BMC1 UCM --*)

(*--------*)

let bmc1_ucm_expand_uc_limit_str = "--bmc1_ucm_expand_uc_limit"

let bmc1_ucm_expand_uc_limit_fun n =
  !current_options.bmc1_ucm_expand_uc_limit <- n

let bmc1_ucm_expand_uc_limit_inf =
  int_str^
  inf_pref^"maximal number of UCs generated in single EXPAND run during UCM (default: 128)\n"

(*--------*)

let bmc1_ucm_n_expand_iterations_str = "--bmc1_ucm_n_expand_iterations"

let bmc1_ucm_n_expand_iterations_fun i =
  !current_options.bmc1_ucm_n_expand_iterations <- i

let bmc1_ucm_n_expand_iterations_inf =
  int_str^
  inf_pref^"limit of continious UC collected during EXPAND\n"

(*--------*)

let bmc1_ucm_extend_mode_str = "--bmc1_ucm_extend_mode"

let bmc1_ucm_extend_mode_fun n =
  !current_options.bmc1_ucm_extend_mode <- n

let bmc1_ucm_extend_mode_inf =
  int_str^
  inf_pref^"How to generate short TR for the new bound during UCM\n"^
  inf_pref^"0 means full TR for the new bound\n"^
  inf_pref^"1 means extension that used all constants appeared in the reduced TR (default)\n"^
  inf_pref^"2 means extension that used only constants appeared in the last step of reduced TR\n"

(*--------*)

let bmc1_ucm_init_mode_str = "--bmc1_ucm_init_mode"

let bmc1_ucm_init_mode_fun n = !current_options.bmc1_ucm_init_mode <- n

let bmc1_ucm_init_mode_inf =
  int_str^
  inf_pref^"How to generate $init part of short TR for the new bound during UCM\n"^
  inf_pref^"0 means full TR for the new bound (default)\n"^
  inf_pref^"1 means extension that used all constants appeared in the reduced TR\n"^
  inf_pref^"2 means extension that used only constants appeared in the last unsat core\n"

(*--------*)

let bmc1_ucm_cone_mode_str = "--bmc1_ucm_cone_mode"

let bmc1_ucm_cone_mode_fun str =
  try
    !current_options.bmc1_ucm_cone_mode <- str_to_bmc1_ucm_cone_mode_type str
  with
    Unknown_bmc1_ucm_cone_mode_type ->
      failwith (args_error_msg bmc1_ucm_cone_mode_str str)

let bmc1_ucm_cone_mode_inf =
  bmc1_ucm_cone_mode_type_list_str^
  inf_pref^"Restrict problem to the cone of influence from unsat core during UCM\n"^
  inf_pref^"0 means no problem restriction (default)\n"^
  inf_pref^"1 means cone of influence extraction in AIG. Work only with AIG mode and without pred-elim\n"^
  inf_pref^"2 means generic cone of influence extraction (not implemented yet)\n"

(*--------*)

let bmc1_ucm_reduced_relation_type_str = "--bmc1_ucm_reduced_relation_type"

let bmc1_ucm_reduced_relation_type_fun n =
  !current_options.bmc1_ucm_reduced_relation_type <- n

let bmc1_ucm_reduced_relation_type_inf =
  int_str^
  inf_pref^"Define type of individual TR during UCM:"^
  inf_pref^"0 means individual relations guarded by short and bound guards (default)"^
  inf_pref^"1 means grounded individual relations"^
  inf_pref^"2 means chained relations guarded by short and bound guards (unimplemented)"^
  inf_pref^"3 means chained grounded individual relations \n"

(*--------*)

let bmc1_ucm_relax_model_str = "--bmc1_ucm_relax_model"

let bmc1_ucm_relax_model_fun n =
  !current_options.bmc1_ucm_relax_model <- n

let bmc1_ucm_relax_model_inf =
  int_str^
  inf_pref^"relax TR in the model by removing participated atoms during UCM\n"^
  inf_pref^"0 means do not relax model\n"^
  inf_pref^"1 means remove atoms that eventually participated in the TR\n"^
  inf_pref^"2 means remove atoms that participated in the TR at current bound\n"^
  inf_pref^"3 means remove symbols that eventually participated in the TR\n"^
  inf_pref^"4 means remove symbols that participated in the TR at current bound (default)\n"

(*--------*)

let bmc1_ucm_full_tr_after_sat_str = "--bmc1_ucm_full_tr_after_sat"

let bmc1_ucm_full_tr_after_sat_fun b =
  !current_options.bmc1_ucm_full_tr_after_sat <-  b

let bmc1_ucm_full_tr_after_sat_inf =
  bool_str^
  inf_pref^"If true, extract a model from the SAT state and use it together with full TR.\n"^
  inf_pref^"If false, use the SAT state similar to an unsat core and extract reduced TR.\n"

(*--------*)

let bmc1_ucm_expand_neg_assumptions_str = "--bmc1_ucm_expand_neg_assumptions"

let bmc1_ucm_expand_neg_assumptions_fun b =
  !current_options.bmc1_ucm_expand_neg_assumptions <-  b

let bmc1_ucm_expand_neg_assumptions_inf =
  bool_str^
  inf_pref^"Add negated $$next groundings assumptions to the reduced model used in UCM during EXPAND call\n"

(*--------*)

let bmc1_ucm_layered_model_str = "--bmc1_ucm_layered_model"

let bmc1_ucm_layered_model_fun str =
  try
    !current_options.bmc1_ucm_layered_model <- str_to_bmc1_ucm_cone_mode_type str
  with
    Unknown_bmc1_ucm_cone_mode_type ->
      failwith (args_error_msg bmc1_ucm_layered_model_str str)

let bmc1_ucm_layered_model_inf =
  bmc1_ucm_cone_mode_type_list_str^
  inf_pref^"Try to apply model to a problem cone restricted by depth during EXPAND call\n"

(*--------*)

let bmc1_ucm_max_lemma_size_str = "--bmc1_ucm_max_lemma_size"

let bmc1_ucm_max_lemma_size_fun n =
  !current_options.bmc1_ucm_max_lemma_size <- n

let bmc1_ucm_max_lemma_size_inf =
  int_str^
  inf_pref^"Maximal size of lemmas allowed for UCM. 0 means do not use lemmas\n"

(*----AIG----------------*)

let aig_mode_str = "--aig_mode"

let aig_mode_fun b =
  !current_options.aig_mode <- b

let aig_mode_inf =
  bool_str^
  inf_pref^"load AIG file using dedicated parser\n"^
  (* ugly hack *)
  (dash_str "Instantiation Options")^"\n"

(*----Instantiation------*)

let instantiation_flag_str = "--instantiation_flag"

let instantiation_flag_fun b =
  !current_options.instantiation_flag <- b

let instantiation_flag_inf =
  bool_str^
  inf_pref^"switches instantiation on/off\n"

(*--------*)

let inst_lit_sel_str = "--inst_lit_sel"

let inst_lit_sel_fun str =
  try
    let str_list = parse_list_opt str in
    let inst_lit_sel = List.map str_to_lit_cmp_type str_list in
    !current_options.inst_lit_sel <- inst_lit_sel
  with
  | Parse_list_fail | Unknown_lit_cmp_type ->
      failwith (args_error_msg inst_lit_sel_str str)

let inst_lit_sel_inf =
  lit_cmp_type_list_str^
  inf_pref^"instantiation selection function is a lex product of functions in the list"^
  example_str^inst_lit_sel_str^" [+sign;+ground;-num_symb]"^
  inf_pref^"in this ex. priority is given to positive literals,"^
  inf_pref^"then to ground and then to lits with fewer number of symbols\n"

(*--------*)

let inst_lit_sel_side_str = "--inst_lit_sel_side"

let inst_lit_sel_side_fun str = 
  try 
    !current_options.inst_lit_sel_side <- (str_to_cl_measure_type str)
  with 
  |Unknown_cl_measure_type ->
      failwith (args_error_msg inst_lit_sel_side_str str)

let inst_lit_sel_side_inf = 
  cl_measure_type_list^
  inf_pref^" literal selection based on minimising specified measure of the side clause set"^
  inf_pref^" this selection is applied first if not none; then inst_lit_sel \n"      

(*--------*)
let inst_solver_per_active_str = "--inst_solver_per_active"

let inst_solver_per_active_fun i =
  !current_options.inst_solver_per_active <- i

let inst_solver_per_active_inf =
  int_str^
  inf_pref^"number of propositional solver calls per active clauses\n"

(*
(*--------*)

let inst_solver_per_clauses_str = "--inst_solver_per_clauses"

let inst_solver_per_clauses_fun i =
  !current_options.inst_solver_per_clauses <- i

let inst_solver_per_clauses_inf =
  int_str^
  inf_pref^"number of propositional solver calls per generated clauses\n"
*)


(*--------*)
let inst_solver_calls_frac_str = "--inst_solver_calls_frac"

let inst_solver_calls_frac_fun f =
  !current_options.inst_solver_calls_frac <- f 

let inst_solver_calls_frac_inf =
  float_str^
  inf_pref^"the number of propositional solver calls as fraction of current clauses\n"

(*--------*)

let inst_passive_queue_type_str = "--inst_passive_queue_type"

let inst_passive_queue_type_fun str =
  try
    !current_options.inst_passive_queue_type <- (str_to_passive_queue_type str)
  with
  | Unknown_passive_queue_type ->
      failwith (args_error_msg inst_passive_queue_type_str str)

let inst_passive_queue_type_inf =
  "< queue | stack | list | proprity_queues >"^
  inf_pref^"type of the passive queue for instantiation\n"

(*--------*)

let inst_passive_queues_str = "--inst_passive_queues"

let inst_passive_queues_fun str =
  try
    let str_list_list = parse_list_list_opt str in
    let queue list = List.map str_to_cl_cmp_type list in
    let queues = List.map queue str_list_list in

    !current_options.inst_passive_queues <- queues

  with
  | Parse_list_fail | Unknown_cl_cmp_type ->
      failwith (args_error_msg inst_passive_queues_str str)

let inst_passive_queues_inf =
  cl_cmp_type_list_str^
  inf_pref^"passive priority queues for instantiation "^
  inf_pref^"priority is based on lex combination of parameters in the list"^
  example_str^inst_passive_queues_str^" [-num_var;-num_symb]"^
  inf_pref^"in this ex. priority is given to clauses with fewer number of vars"^
  inf_pref^"then with fewer number of symbols\n"

(*--------*)

let inst_passive_queues_freq_str = "--inst_passive_queues_freq"

let inst_passive_queues_freq_fun str =
  try
    let str_list = parse_list_opt str in
    let freqs = List.map int_of_string str_list in

    !current_options.inst_passive_queues_freq <- freqs

  with
  | Parse_list_fail | Unknown_cl_cmp_type ->
      failwith (args_error_msg inst_passive_queues_freq_str str)

let inst_passive_queues_freq_inf =
  "[n1;...;nN]"^
  inf_pref^"frequencies of passive priority queue for instantiation:"^
  inf_pref^"each is the number of clauses taken before switching to the next queue\n"

(*--------*)

let inst_dismatching_str = "--inst_dismatching"

let inst_dismatching_fun b =
  !current_options.inst_dismatching <- b

let inst_dismatching_inf =
  bool_str^
  inf_pref^"Dismatching constraints for instantiation\n"

(*--------*)

let inst_eager_unprocessed_to_passive_str = "--inst_eager_unprocessed_to_passive"

let inst_eager_unprocessed_to_passive_fun b =
  !current_options.inst_eager_unprocessed_to_passive <- b

let inst_eager_unprocessed_to_passive_inf =
  bool_str^"\n"

(*--------*)

let inst_prop_sim_given_str = "--inst_prop_sim_given"

let inst_prop_sim_given_fun b =
  !current_options.inst_prop_sim_given <- b

let inst_prop_sim_given_inf =
  bool_str^
  inf_pref^"instantiation: propositional simplification of the given clause\n"

(*--------*)

let inst_prop_sim_new_str = "--inst_prop_sim_new"

let inst_prop_sim_new_fun b =
  !current_options.inst_prop_sim_new <- b

let inst_prop_sim_new_inf =
  bool_str^
  inf_pref^"instantiation: propositional simplification of newly produced clauses\n"

(*--------*)

let inst_subs_given_str = "--inst_subs_given" 

let inst_subs_given_fun b = 
  !current_options.inst_subs_given <- b

let inst_subs_given_inf = 
  bool_str^
  inf_pref^"instantiation: strict subsumption of given clauses \n"

(*--------*)
 
let inst_subs_new_str = "--inst_subs_new" 

let inst_subs_new_fun b = 
  !current_options.inst_subs_new <- b

let inst_subs_new_inf = 
  bool_str^
  inf_pref^"instantiation: strict subsumption of new clauses \n"

(*--------*)
let inst_eq_res_simp_str = "--inst_eq_res_simp"

let inst_eq_res_simp_fun b = 
  !current_options.inst_eq_res_simp <- b

let inst_eq_res_simp_inf = 
  bool_str^
  inf_pref^"instantiation: t!=t \\/C => C \n"


(*--------*)

let inst_orphan_elimination_str = "--inst_orphan_elimination"

let inst_orphan_elimination_fun b =
  !current_options.inst_orphan_elimination <- b

let inst_orphan_elimination_inf =
  bool_str^
  inf_pref^"eliminates children if the parent gets eliminated; here only children obtained by instantiation are considered\n"


(*--------*)

let inst_learning_loop_flag_str = "--inst_learning_loop_flag"

let inst_learning_loop_flag_fun b =
  !current_options.inst_learning_loop_flag <- b

let inst_learning_loop_flag_inf =
  bool_str^
  inf_pref^"simple learning: restart instantiation after"^
  inf_pref^"inst_learning_start inst. loop iterations"^
  inf_pref^"keeping propositional set of clauses"^
  inf_pref^"which provides better guided proof search\n"

(*--------*)
let inst_learning_start_str = "--inst_learning_start"

let inst_learning_start_fun i =
  !current_options.inst_learning_start <- i

let inst_learning_start_inf =
  int_str^
  inf_pref^"number of instantiation loops before learning starts\n"

(*--------*)
let inst_learning_factor_str = "--inst_learning_factor"

let inst_learning_factor_fun i =
  !current_options.inst_learning_factor <- i

let inst_learning_factor_inf =
  int_str^
  inf_pref^"learning is repeated after that"^
  inf_pref^"the bound on number of loops is multiplied by this factor\n"

(*--------*)
let inst_start_prop_sim_after_learn_str = "--inst_start_prop_sim_after_learn"

let inst_start_prop_sim_after_learn_fun i =
  !current_options.inst_start_prop_sim_after_learn <- i

let inst_start_prop_sim_after_learn_inf =
  int_str^
  inf_pref^"prop simplification starts after"^
  inf_pref^"inst_start_prop_sim_after_learn of learning restarts\n"

(*--------*)

let inst_sel_renew_str = "--inst_sel_renew"

let inst_sel_renew_fun str =
  try
    !current_options.inst_sel_renew <- (str_to_inst_sel_renew_type str)
  with
    Unknown_out_options_type ->
      failwith (args_error_msg inst_sel_renew_str str)

let inst_sel_renew_inf =
  "<model|solver>"^
  inf_pref^" Selection is either based on (i) pre stored model and model values are tried to be enforced, or"^
  inf_pref^" (ii) current sat solver values \n"

(*--------*)

let inst_lit_activity_flag_str = "--inst_lit_activity_flag"

let inst_lit_activity_flag_fun b =
  !current_options.inst_lit_activity_flag <- b

let inst_lit_activity_flag_inf =
  bool_str^
  inf_pref^"if true then overactive literals are tried to be deselected in propositional models\n"

(*--------*)

let inst_restr_to_given_str = "--inst_restr_to_given"

let inst_restr_to_given_fun b =
  !current_options.inst_restr_to_given <- b

let inst_restr_to_given_inf =
  bool_str^
  inf_pref^"if true, instantiation is restricted to the given clause\n"

(*--------*)

let inst_activity_threshold_str = "--inst_activity_threshold"

let inst_activity_threshold_fun i =
  !current_options.inst_activity_threshold <- i

let inst_activity_threshold_inf =
  int_str^
  inf_pref^"inst lit activity threshold\n"


(*--------*)

let inst_out_proof_str = "--inst_out_proof"

let inst_out_proof_fun b =
  !current_options.inst_out_proof <-
    override_cmd b !current_options.inst_out_proof

let inst_out_proof_inf =
  bool_str^
  inf_pref^"output proofs from instantiation\n"^
  (* ugly hack *)
  (dash_str "Resolution Options")^"\n"

(*----Resolution------*)

let resolution_flag_str = "--resolution_flag"

let resolution_flag_fun b =
  !current_options.resolution_flag <- b

let resolution_flag_inf =
  bool_str^
  inf_pref^"switches resolution on/off\n"

(*--------*)

let res_lit_sel_str = "--res_lit_sel"

let res_lit_sel_fun str =
  try
    !current_options.res_lit_sel <- (str_to_sel_type str)
  with
    Unknown_res_sel_fun_type ->
      failwith (args_error_msg res_lit_sel_str str)

let res_lit_sel_inf =
  res_lit_sel_type_str^
  inf_pref^"resolution literal selection functions:"^
  inf_pref^"adaptive: select negative literals until no inference possible"^
  inf_pref^"          then change to kbo maximal"^
  inf_pref^"kbo_max: select kbo maximal literals"^
  inf_pref^"neg_max: select negative literals with a maximal number of symbols, otherwise kbo_max"^
  inf_pref^"neg_min: select negative literals with a minimal number of symbols, otherwise kbo_max\n"

(*--------*)

let res_lit_sel_side_str = "--res_lit_sel_side"

let res_lit_sel_side_fun str = 
  try 
    !current_options.res_lit_sel_side <- (str_to_cl_measure_type str)
  with 
  |Unknown_cl_measure_type ->
      failwith (args_error_msg res_lit_sel_side_str str)

let res_lit_sel_side_inf = 
  cl_measure_type_list^
  inf_pref^" literal selection based on minimising specified measure of the side clause set among negative lits"^
  inf_pref^" this selection is done first before --res_lit_sel unless --res_lit_sel_side none\n"      

(*--------*)
let res_ordering_str = "--res_ordering"

let res_ordering_fun str = 
  try 
    !current_options.res_ordering <- str_to_res_ord_type str
  with 
  |Unknown_res_ord_type -> 
       failwith (args_error_msg res_ord_type_str str)

let res_ordering_inf = 
  res_ord_type_str^
  inf_pref^"main ordering for literal selection\n"

(*--------*)
let res_to_prop_solver_str = "--res_to_prop_solver"

let res_to_prop_solver_fun str =
  try
    !current_options.res_to_prop_solver <- (str_to_res_to_prop_solver_type str)
  with
    Unknown_res_to_prop_solver_type ->
      failwith (args_error_msg res_to_prop_solver_str str)

let res_to_prop_solver_inf =
  "<active | passive | none>"^
  inf_pref^"adding grounding of clauses to the propositional solver\n"

(*--------*)
let res_prop_simpl_new_str = "--res_prop_simpl_new"

let res_prop_simpl_new_fun b =
  !current_options.res_prop_simpl_new <- b

let res_prop_simpl_new_inf =
  bool_str^
  inf_pref^"propositionally simplify newly generated (by resolution) clauses\n"

(*--------*)
let res_prop_simpl_given_str = "--res_prop_simpl_given"

let res_prop_simpl_given_fun b =
  !current_options.res_prop_simpl_given <- b

let res_prop_simpl_given_inf =
  bool_str^
  inf_pref^"propositionally simplify given (in the resolution loop) clauses\n"

(*--------*)

let res_passive_queue_type_str = "--res_passive_queue_type"

let res_passive_queue_type_fun str =
  try
    !current_options.res_passive_queue_type <- (str_to_passive_queue_type str)

  with
  | Unknown_passive_queue_type ->
      failwith (args_error_msg res_passive_queue_type_str str)

let res_passive_queue_type_inf =
  "< queue | stack | list | proprity_queues >"^
  inf_pref^"type of the passive queue for resolution\n"

(*--------*)

let res_passive_queues_str = "--res_passive_queues"

let res_passive_queues_fun str =
  try
    let str_list_list = parse_list_list_opt str in
    let queue list = List.map str_to_cl_cmp_type list in
    let queues = List.map queue str_list_list in

    !current_options.res_passive_queues <- queues

  with
  | Parse_list_fail | Unknown_cl_cmp_type ->
      failwith (args_error_msg res_passive_queues_str str)

let res_passive_queues_inf =
  cl_cmp_type_list_str^
  inf_pref^"passive priority queues for resolution "^
  inf_pref^"priority is based on lex combination of parameters in the list"^
  example_str^res_passive_queues_str^" [-num_var;-num_symb]"^
  inf_pref^"in this ex. priority is given to clauses with fewer number of vars"^
  inf_pref^"then with fewer number of symbols\n"

(*--------*)

let res_passive_queues_freq_str = "--res_passive_queues_freq"

let res_passive_queues_freq_fun str =
  try
    let str_list = parse_list_opt str in
    let freqs = List.map int_of_string str_list in

    !current_options.res_passive_queues_freq <- freqs

  with
  | Parse_list_fail | Unknown_cl_cmp_type ->
      failwith (args_error_msg res_passive_queues_freq_str str)

let res_passive_queues_freq_inf =
  "[n1;...;nN]"^
  inf_pref^"frequencies of passive priority queue for resolution:"^
  inf_pref^"each is the number of clauses taken before switching to the next queue\n"

(*--------*)
let res_forward_subs_str = "--res_forward_subs"

let res_forward_subs_fun str =
  try
    !current_options.res_forward_subs <- (str_to_res_subs_type str)
  with Unknown_res_subs_type ->
    failwith (args_error_msg res_forward_subs_str str)

let res_forward_subs_inf =
  res_subs_type_str^
  inf_pref^"full:                 full forward subsumption"^
  inf_pref^"subset_subsumption:   efficient but incomplete (always on);"^
  inf_pref^"length[n]:            subsumption by clauses of length less or equal to n"^
  example_str^res_forward_subs_str^" length[1]\n"

(*--------*)

let res_backward_subs_str = "--res_backward_subs"

let res_backward_subs_fun str =
  try
    !current_options.res_backward_subs <- (str_to_res_subs_type str)
  with Unknown_res_subs_type ->
    failwith (args_error_msg res_backward_subs_str str)

let res_backward_subs_inf =
  res_subs_type_str^
  inf_pref^"full:                 full forward subsumption"^
  inf_pref^"subset_subsumption:   efficient but incomplete (always on);"^
  inf_pref^"length[n]:            subsumption by clauses of length less or equal to n"^
  example_str^res_backward_subs_str^" length[1]\n"

(*--------*)

let res_forward_subs_resolution_str = "--res_forward_subs_resolution"

let res_forward_subs_resolution_fun b =
  !current_options.res_forward_subs_resolution <- b

let res_forward_subs_resolution_inf =
  bool_str^
  inf_pref^"forward subsumption resolution\n"

(*--------*)
let res_backward_subs_resolution_str = "--res_backward_subs_resolution"

let res_backward_subs_resolution_fun b =
  !current_options.res_backward_subs_resolution <- b

let res_backward_subs_resolution_inf =
  bool_str^
  inf_pref^"backward subsumption resolution\n"

(*--------*)
let res_orphan_elimination_str = "--res_orphan_elimination"

let res_orphan_elimination_fun b =
  !current_options.res_orphan_elimination <- b

let res_orphan_elimination_inf =
  bool_str^
  inf_pref^"orphan elimination\n"

(*--------*)
let res_time_limit_str = "--res_time_limit"

let res_time_limit_fun f =
  !current_options.res_time_limit <- f

let res_time_limit_inf =
  float_str^
  inf_pref^"time limit (in seconds) for each iteration of the resolution loop\n"

(*--------*)
let res_out_proof_str = "--res_out_proof"

let res_out_proof_fun b =
  !current_options.res_out_proof <- b

let res_out_proof_inf =
  bool_str^
  inf_pref^"Outputs the proof, if it is found by resolution\n"^
  (* ugly hack *)
  (dash_str "Combination Options")^"\n"

(*----Combination--------*)

let comb_res_mult_str = "--comb_res_mult"

let comb_res_mult_fun i =
  !current_options.comb_res_mult <- i

let comb_res_mult_inf =
  int_str^
  inf_pref^"resolution multiple in combination of instantiation and resolution\n"

(*--------*)
let comb_inst_mult_str = "--comb_inst_mult"

let comb_inst_mult_fun i =
  !current_options.comb_inst_mult <- i

let comb_inst_mult_inf =
  int_str^
  inf_pref^"instantiation multiple in combination of instantiation and resolution\n"^
  (* ugly hack *)
  (dash_str "Remaining Options")^"\n"

(*

  let _str = "--"

  let _fun =
  !current_options. <-

  let _inf =
  ^
  inf_pref^

  inf_pref^
  inf_pref^

  !current_options
  !current_options.
  !current_options.
  !current_options.
 *)

(*let info_str str = "\n    "^str*)
let spec_list =
  [(*(out_options_str, Arg.String(out_options_fun), out_options_inf);
   (tptp_safe_out_str, Arg.Bool(tptp_safe_out_fun), tptp_safe_out_inf);
   (problem_path_str, Arg.String(problem_path_fun), problem_path_inf);
   (include_path_str, Arg.String(include_path_fun), include_path_inf);
   (clausifier_str, Arg.String(clausifier_fun), clausifier_inf);
   (clausifier_options_str, Arg.String(clausifier_options_fun), clausifier_options_inf);
   (stdin_str, Arg.Bool(stdin_fun), stdin_inf);*)
   (dbg_backtrace_str, Arg.Bool(dbg_backtrace_fun), dbg_backtrace_inf);
   (time_out_real_str, Arg.Float(time_out_real_fun), time_out_real_inf);
   (dbg_out_stat_str, Arg.Bool(dbg_out_stat_fun), dbg_out_stat_inf);
   (fix_init_inter_str, Arg.Bool(fix_init_inter_fun), fix_init_inter_inf);

   (*------General-------*)
   (*(fof_str, Arg.Bool(fof_fun), fof_inf); *)
   (*(time_out_real_str, Arg.Float(time_out_real_fun), time_out_real_inf);*)
   (*(time_out_prep_mult_str, Arg.Float(time_out_prep_mult_fun), time_out_prep_mult_inf);
   (time_out_virtual_str, Arg.Float(time_out_virtual_fun), time_out_virtual_inf);
   (schedule_str, Arg.String(schedule_fun), schedule_inf);
   (splitting_mode_str, Arg.String(splitting_mode_fun), splitting_mode_inf);
   (splitting_grd_str, Arg.Bool(splitting_grd_fun), splitting_grd_inf);
   (splitting_cvd_str, Arg.Bool(splitting_cvd_fun), splitting_cvd_inf);
   (splitting_cvd_svl_str, Arg.Bool(splitting_cvd_svl_fun), splitting_cvd_svl_inf);
   (splitting_nvd_str, Arg.Int(splitting_nvd_fun), splitting_nvd_inf);
   (non_eq_to_eq_str, Arg.Bool(non_eq_to_eq_fun), non_eq_to_eq_inf);
   (prep_gs_sim_str, Arg.Bool(prep_gs_sim_fun), prep_gs_sim_inf);
   (prep_unflatten_str, Arg.Bool(prep_unflatten_fun), prep_unflatten_inf);
   (prep_res_sim_str, Arg.Bool(prep_res_sim_fun), prep_res_sim_inf);
   (prep_upred_str, Arg.Bool(prep_upred_fun), prep_upred_inf);
   (res_sim_input_str, Arg.Bool(res_sim_input_fun), res_sim_input_inf);
   (clause_weak_htbl_str, Arg.Bool(clause_weak_htbl_fun), clause_weak_htbl_inf);
   (gc_record_bc_elim_str, Arg.Bool(gc_record_bc_elim_fun), gc_record_bc_elim_inf);
   (symbol_type_check_str, Arg.Bool(symbol_type_check_fun), symbol_type_check_inf);
   (clausify_out_str, Arg.Bool(clausify_out_fun), clausify_out_inf);
   (prep_sem_filter_str, Arg.String(prep_sem_filter_fun), prep_sem_filter_inf);
   (prep_sem_filter_out_str, Arg.Bool(prep_sem_filter_out_fun), prep_sem_filter_out_inf);
   (preprocessed_out_str, Arg.Bool(preprocessed_out_fun), preprocessed_out_inf);
   (preprocessed_stats_str, Arg.Bool(preprocessed_stats_fun), preprocessed_stats_inf);
   (sub_typing_str, Arg.Bool(sub_typing_fun), sub_typing_inf);
   (eq_ax_congr_red_str, Arg.Bool(eq_ax_congr_red_fun), eq_ax_congr_red_inf);
   (brand_transform_str, Arg.Bool(brand_transform_fun), brand_transform_inf);
   (pure_diseq_elim_str, Arg.Bool(pure_diseq_elim_fun), pure_diseq_elim_inf);
   (min_unsat_core_str, Arg.Bool(min_unsat_core_fun), min_unsat_core_inf);
   (pred_elim_str, Arg.Bool(pred_elim_fun), pred_elim_inf);
   (add_important_lit_str, Arg.Bool(add_important_lit_fun), add_important_lit_inf);
   (soft_assumptions_str, Arg.Bool(soft_assumptions_fun), soft_assumptions_inf);
   (soft_lemma_size_str, Arg.Int(soft_lemma_size_fun), soft_lemma_size_inf);
   (prop_impl_unit_size_str, Arg.Int(prop_impl_unit_size_fun), prop_impl_unit_size_inf);
   (prop_impl_unit_str, Arg.String(prop_impl_unit_fun), prop_impl_unit_inf);
   (share_sel_clauses_str, Arg.Bool(share_sel_clauses_fun), share_sel_clauses_inf);

   (reset_solvers_str, Arg.Bool(reset_solvers_fun), reset_solvers_inf);
   (bc_imp_inh_str, Arg.String(bc_imp_inh_fun),bc_imp_inh_inf);
   (conj_cone_tolerance_str, Arg.Float(conj_cone_tolerance_fun), conj_cone_tolerance_inf);
   (extra_neg_conj_str, Arg.String(extra_neg_conj_fun), extra_neg_conj_inf);

   (abstr_ref_str, Arg.String(abstr_ref_fun), abstr_ref_inf);

(*
   (abstr_ref_arg_filter_str, Arg.Bool(abstr_ref_arg_filter_fun), abstr_ref_arg_filter_inf);
   (abstr_ref_sig_str, Arg.Bool(abstr_ref_sig_fun), abstr_ref_sig_inf);
   (abstr_ref_subs_str, Arg.Bool(abstr_ref_subs_fun), abstr_ref_subs_inf);
*)
   (abstr_ref_prep_str, Arg.Bool(abstr_ref_prep_fun), abstr_ref_prep_inf);
   (abstr_ref_until_sat_str, Arg.Bool(abstr_ref_until_sat_fun), abstr_ref_until_sat_inf);
   (* (abstr_terms_sig_str, Arg.Bool(abstr_terms_sig_fun), abstr_terms_sig_inf);
    * (abstr_skolem_sig_str, Arg.Bool(abstr_skolem_sig_fun), abstr_skolem_sig_inf); *)
   (abstr_ref_sig_restrict_str, Arg.String(abstr_ref_sig_restrict_fun), abstr_ref_sig_restrict_inf);
   (abstr_ref_af_restrict_to_split_sk_str, Arg.Bool(abstr_ref_af_restrict_to_split_sk_fun), abstr_ref_af_restrict_to_split_sk_inf);
   (prep_def_merge_str, Arg.Bool(prep_def_merge_fun), prep_def_merge_inf);
   (prep_def_merge_prop_impl_str, Arg.Bool(prep_def_merge_prop_impl_fun), prep_def_merge_prop_impl_inf);
   (prep_def_merge_mbd_str, Arg.Bool(prep_def_merge_mbd_fun), prep_def_merge_mbd_inf);
   (prep_def_merge_tr_red_str, Arg.Bool(prep_def_merge_tr_red_fun), prep_def_merge_tr_red_inf);
   (prep_def_merge_tr_cl_str, Arg.Bool(prep_def_merge_tr_cl_fun), prep_def_merge_tr_cl_inf);

   (*---Large Theories----*)
   (large_theory_mode_str, Arg.Bool(large_theory_mode_fun), large_theory_mode_inf);

   (prolific_symb_bound_str, Arg.Int(prolific_symb_bound_fun), prolific_symb_bound_inf);
   (lt_threshold_str, Arg.Int(lt_threshold_fun), lt_threshold_inf);

   (*-----Sat Mode----------*)
   (sat_mode_str, Arg.Bool(sat_mode_fun), sat_mode_inf);
   (sat_fm_restart_options_str, Arg.String(sat_fm_restart_options_fun), sat_fm_restart_options_inf);
   (sat_gr_def_str, Arg.Bool(sat_gr_def_fun), sat_gr_def_inf);
   (sat_epr_types_str, Arg.Bool(sat_epr_types_fun), sat_epr_types_inf);
   (sat_non_cyclic_types_str, Arg.Bool(sat_non_cyclic_types_fun), sat_non_cyclic_types_inf);
   (sat_finite_models_str, Arg.Bool(sat_finite_models_fun), sat_finite_models_inf);
   (sat_fm_lemmas_str, Arg.Bool(sat_fm_lemmas_fun), sat_fm_lemmas_inf);
   (sat_fm_prep_str, Arg.Bool(sat_fm_prep_fun), sat_fm_prep_inf);
   (sat_fm_uc_incr_str, Arg.Bool(sat_fm_uc_incr_fun), sat_fm_uc_incr_inf);  
   (sat_out_model_str, Arg.String(sat_out_model_fun), sat_out_model_inf);
   (sat_out_clauses_str, Arg.Bool(sat_out_clauses_fun), sat_out_clauses_inf);

   (*----- QBF Mode----------*)
   (qbf_mode_str, Arg.Bool(qbf_mode_fun), qbf_mode_inf);
   (qbf_elim_univ_str, Arg.Bool(qbf_elim_univ_fun), qbf_elim_univ_inf);
   (qbf_dom_inst_str, Arg.String(qbf_dom_inst_fun), qbf_dom_inst_inf);
   (qbf_dom_pre_inst_str, Arg.Bool(qbf_dom_pre_inst_fun), qbf_dom_pre_inst_inf);
   (qbf_sk_in_str, Arg.Bool(qbf_sk_in_fun), qbf_sk_in_inf);
   (qbf_pred_elim_str, Arg.Bool(qbf_pred_elim_fun), qbf_pred_elim_inf);
   (qbf_split_str, Arg.Int(qbf_split_fun), qbf_split_inf); 

   (*----BMC1---------------*)
   (bmc1_incremental_str,
    Arg.Bool(bmc1_incremental_fun),
    bmc1_incremental_inf);

   (bmc1_axioms_str,
    Arg.String(bmc1_axioms_fun),
    bmc1_axioms_inf);

   (bmc1_min_bound_str,
    Arg.Int(bmc1_min_bound_fun),
    bmc1_min_bound_inf);

   (bmc1_max_bound_str,
    Arg.Int(bmc1_max_bound_fun),
    bmc1_max_bound_inf);

   (bmc1_max_bound_default_str,
    Arg.Int(bmc1_max_bound_default_fun),
    bmc1_max_bound_default_inf);

   (bmc1_symbol_reachability_str,
    Arg.Bool(bmc1_symbol_reachability_fun),
    bmc1_symbol_reachability_inf);

   (bmc1_property_lemmas_str,
    Arg.Bool(bmc1_property_lemmas_fun),
    bmc1_property_lemmas_inf);

   (bmc1_k_induction_str,
    Arg.Bool(bmc1_k_induction_fun),
    bmc1_k_induction_inf);

   (bmc1_non_equiv_states_str,
    Arg.Bool(bmc1_non_equiv_states_fun),
    bmc1_non_equiv_states_inf);

   (bmc1_deadlock_str,
    Arg.Bool(bmc1_deadlock_fun),
    bmc1_deadlock_inf);

   (bmc1_ucm_str,
    Arg.Bool(bmc1_ucm_fun),
    bmc1_ucm_inf);

   (bmc1_add_unsat_core_str,
    Arg.String(bmc1_add_unsat_core_fun),
    bmc1_add_unsat_core_inf);

   (bmc1_unsat_core_children_str,
    Arg.Bool(bmc1_unsat_core_children_fun),
    bmc1_unsat_core_children_inf);

   (bmc1_unsat_core_extrapolate_axioms_str,
    Arg.Bool(bmc1_unsat_core_extrapolate_axioms_fun),
    bmc1_unsat_core_extrapolate_axioms_inf);

   (bmc1_out_stat_str,
    Arg.String(bmc1_out_stat_fun),
    bmc1_out_stat_inf);

   (bmc1_ground_init_str, Arg.Bool(bmc1_ground_init_fun), bmc1_ground_init_inf);

   (bmc1_pre_inst_next_state_str,
    Arg.Bool(bmc1_pre_inst_next_state_fun),
    bmc1_pre_inst_next_state_inf);

   (bmc1_pre_inst_state_str,
    Arg.Bool(bmc1_pre_inst_state_fun),
    bmc1_pre_inst_state_inf);

   (bmc1_pre_inst_reach_state_str,
    Arg.Bool(bmc1_pre_inst_reach_state_fun),
    bmc1_pre_inst_reach_state_inf);

   (bmc1_out_unsat_core_str,
    Arg.Bool(bmc1_out_unsat_core_fun),
    bmc1_out_unsat_core_inf);

   (bmc1_aig_witness_out_str,
    Arg.Bool(bmc1_aig_witness_out_fun),
    bmc1_aig_witness_out_inf);

   (bmc1_dump_clauses_tptp_str,
    Arg.Bool(bmc1_dump_clauses_tptp_fun),
    bmc1_dump_clauses_tptp_inf);

   (bmc1_dump_unsat_core_tptp_str,
    Arg.Bool(bmc1_dump_unsat_core_tptp_fun),
    bmc1_dump_unsat_core_tptp_inf);

   (bmc1_dump_file_str,
    Arg.String(bmc1_dump_file_fun),
    bmc1_dump_file_inf);

   (bmc1_verbose_str,
    Arg.Bool(bmc1_verbose_fun),
    bmc1_verbose_inf);

    (*----BMC1 UCM --*)

   (bmc1_ucm_expand_uc_limit_str,
    Arg.Int(bmc1_ucm_expand_uc_limit_fun),
    bmc1_ucm_expand_uc_limit_inf);

   (bmc1_ucm_n_expand_iterations_str,
    Arg.Int(bmc1_ucm_n_expand_iterations_fun),
    bmc1_ucm_n_expand_iterations_inf);

   (bmc1_ucm_extend_mode_str,
    Arg.Int(bmc1_ucm_extend_mode_fun),
    bmc1_ucm_extend_mode_inf);

   (bmc1_ucm_init_mode_str, Arg.Int(bmc1_ucm_init_mode_fun), bmc1_ucm_init_mode_inf);

   (bmc1_ucm_cone_mode_str, Arg.String(bmc1_ucm_cone_mode_fun), bmc1_ucm_cone_mode_inf);

   (bmc1_ucm_reduced_relation_type_str,
    Arg.Int(bmc1_ucm_reduced_relation_type_fun),
    bmc1_ucm_reduced_relation_type_inf);

   (bmc1_ucm_relax_model_str, Arg.Int(bmc1_ucm_relax_model_fun), bmc1_ucm_relax_model_inf);

   (bmc1_ucm_full_tr_after_sat_str,
    Arg.Bool(bmc1_ucm_full_tr_after_sat_fun),
    bmc1_ucm_full_tr_after_sat_inf);

   (bmc1_ucm_expand_neg_assumptions_str,
    Arg.Bool(bmc1_ucm_expand_neg_assumptions_fun),
    bmc1_ucm_expand_neg_assumptions_inf);

   (bmc1_ucm_layered_model_str, Arg.String(bmc1_ucm_layered_model_fun), bmc1_ucm_layered_model_inf);

  (* lemmas *)

   (bmc1_ucm_max_lemma_size_str,
    Arg.Int(bmc1_ucm_max_lemma_size_fun),
    bmc1_ucm_max_lemma_size_inf);

   (*----AIG----------------*)
   (aig_mode_str,
    Arg.Bool(aig_mode_fun),
    aig_mode_inf);

   (*------Instantiation--*)
   (instantiation_flag_str, Arg.Bool(instantiation_flag_fun), instantiation_flag_inf);
   (inst_lit_sel_str, Arg.String(inst_lit_sel_fun), inst_lit_sel_inf);
   (inst_lit_sel_side_str, Arg.String(inst_lit_sel_side_fun), inst_lit_sel_side_inf);
   (inst_solver_calls_frac_str, Arg.Float(inst_solver_calls_frac_fun), inst_solver_calls_frac_inf);

   (inst_solver_per_active_str,
    Arg.Int(inst_solver_per_active_fun), inst_solver_per_active_inf);
(*   (inst_solver_per_clauses_str,
    Arg.Int(inst_solver_per_clauses_fun), inst_solver_per_clauses_inf);
*)

   (inst_passive_queue_type_str,
    Arg.String(inst_passive_queue_type_fun), inst_passive_queue_type_inf);
   (inst_passive_queues_str,
    Arg.String(inst_passive_queues_fun), inst_passive_queues_inf);
   (inst_passive_queues_freq_str, Arg.String(inst_passive_queues_freq_fun), inst_passive_queues_freq_inf);
   (inst_dismatching_str, Arg.Bool(inst_dismatching_fun), inst_dismatching_inf);
   (inst_eager_unprocessed_to_passive_str,
    Arg.Bool(inst_eager_unprocessed_to_passive_fun),
    inst_eager_unprocessed_to_passive_inf);
   (inst_prop_sim_given_str,
    Arg.Bool(inst_prop_sim_given_fun), inst_prop_sim_given_inf);
   (inst_prop_sim_new_str, Arg.Bool(inst_prop_sim_new_fun), inst_prop_sim_new_inf);
   (inst_subs_new_str, Arg.Bool(inst_subs_new_fun), inst_subs_new_inf);
   (inst_eq_res_simp_str, Arg.Bool(inst_eq_res_simp_fun), inst_eq_res_simp_inf);
   (inst_subs_given_str, Arg.Bool(inst_subs_given_fun), inst_subs_given_inf);
   (inst_orphan_elimination_str, Arg.Bool(inst_orphan_elimination_fun), inst_orphan_elimination_inf);
   (inst_learning_loop_flag_str,
    Arg.Bool(inst_learning_loop_flag_fun), inst_learning_loop_flag_inf);
   (inst_learning_start_str,
    Arg.Int(inst_learning_start_fun), inst_learning_start_inf);
   (inst_learning_factor_str,
    Arg.Int(inst_learning_factor_fun), inst_learning_factor_inf);
   (inst_start_prop_sim_after_learn_str,
    Arg.Int(inst_start_prop_sim_after_learn_fun), inst_start_prop_sim_after_learn_inf);
   (inst_sel_renew_str, Arg.String(inst_sel_renew_fun), inst_sel_renew_inf);
   (inst_lit_activity_flag_str, Arg.Bool(inst_lit_activity_flag_fun), inst_lit_activity_flag_inf);
   (inst_restr_to_given_str, Arg.Bool(inst_restr_to_given_fun), inst_restr_to_given_inf);
   (inst_activity_threshold_str, Arg.Int(inst_activity_threshold_fun), inst_activity_threshold_inf);
   (inst_out_proof_str, Arg.Bool(inst_out_proof_fun), inst_out_proof_inf);

   (*------Resolution--*)
   (resolution_flag_str, Arg.Bool(resolution_flag_fun), resolution_flag_inf);
   (res_lit_sel_str, Arg.String(res_lit_sel_fun), res_lit_sel_inf);
   (res_lit_sel_side_str, Arg.String(res_lit_sel_side_fun), res_lit_sel_side_inf);
   (res_ordering_str, Arg.String(res_ordering_fun), res_ordering_inf);
   (res_to_prop_solver_str, Arg.String(res_to_prop_solver_fun), res_to_prop_solver_inf);
   (res_prop_simpl_new_str,
    Arg.Bool(res_prop_simpl_new_fun), res_prop_simpl_new_inf);
   (res_prop_simpl_given_str,
    Arg.Bool(res_prop_simpl_given_fun), res_prop_simpl_given_inf);
   (res_passive_queue_type_str, Arg.String(res_passive_queue_type_fun), res_passive_queue_type_inf);
   (res_passive_queues_str, Arg.String(res_passive_queues_fun), res_passive_queues_inf);
   (res_passive_queues_freq_str, Arg.String(res_passive_queues_freq_fun), res_passive_queues_freq_inf);
   (res_forward_subs_str,
    Arg.String(res_forward_subs_fun), res_forward_subs_inf);
   (res_backward_subs_str,
    Arg.String(res_backward_subs_fun), res_backward_subs_inf);
   (res_forward_subs_resolution_str,
    Arg.Bool(res_forward_subs_resolution_fun), res_forward_subs_resolution_inf);
   (res_backward_subs_resolution_str,
    Arg.Bool(res_backward_subs_resolution_fun), res_backward_subs_resolution_inf);
   (res_orphan_elimination_str,
    Arg.Bool(res_orphan_elimination_fun), res_orphan_elimination_inf);
   (res_time_limit_str, Arg.Float(res_time_limit_fun), res_time_limit_inf);
   (res_out_proof_str, Arg.Bool(res_out_proof_fun), res_out_proof_inf);
   (comb_res_mult_str, Arg.Int(comb_res_mult_fun), comb_res_mult_inf);
   (comb_inst_mult_str, Arg.Int(comb_inst_mult_fun), comb_inst_mult_inf);*)
   (*
     (_str, Arg.(_fun), _inf);
    *)
 ]

(*--------Options output-----------------*)

type opt_val_type = string * string

let val_distance = 40

let opt_val_to_str opt_val =
  let (opt_name, val_str') = opt_val in
  let tptp_safe_opt_name = tptp_safe_str opt_name in
  let val_str =
    if val_str' = "" then "\"\"" else val_str' in
  (space_padding_str val_distance tptp_safe_opt_name)^val_str

let opt_val_list_to_str l =
  String.concat "\n" (List.map opt_val_to_str l)

let input_options_str_list opt =
  [
   (out_options_str,
    (out_options_type_to_str (val_of_override opt.out_options)));
   (tptp_safe_out_str, (string_of_bool opt.tptp_safe_out));
   (problem_path_str, opt.problem_path);
   (include_path_str, opt.include_path);
   (clausifier_str, opt.clausifier);
   (clausifier_options_str, opt.clausifier_options);
   (stdin_str, (string_of_bool opt.stdin));
   ]

let string_of_bool_opt = function None -> "None" | Some b -> string_of_bool b

let general_options_str_list opt =
  [
   (fix_init_inter_str, (string_of_bool_opt opt.fix_init_inter));
   (time_out_real_str, (string_of_float opt.time_out_real));
   (symbol_type_check_str, (string_of_bool opt.symbol_type_check));
   (clausify_out_str, (string_of_bool opt.clausify_out));
  ]

let global_options_str_list opt =
  [
   (schedule_str, (schedule_type_to_str opt.schedule));
   (add_important_lit_str, (string_of_bool opt.add_important_lit));
   (min_unsat_core_str, (string_of_bool opt.min_unsat_core));
   (soft_assumptions_str, (string_of_bool opt.soft_assumptions));
   (soft_lemma_size_str, (string_of_int opt.soft_lemma_size));
   (prop_impl_unit_size_str, (string_of_int opt.prop_impl_unit_size));
   (prop_impl_unit_str, (prop_impl_unit_type_to_str opt.prop_impl_unit));
   (share_sel_clauses_str, (string_of_bool opt.share_sel_clauses));
   (reset_solvers_str, (string_of_bool opt.reset_solvers));
   (bc_imp_inh_str, (bc_imp_inh_list_type_to_str opt.bc_imp_inh));
   (conj_cone_tolerance_str, (string_of_float opt.conj_cone_tolerance));
   (extra_neg_conj_str, (extra_neg_conj_type_to_str opt.extra_neg_conj));
   (large_theory_mode_str, (string_of_bool opt.large_theory_mode));
   (prolific_symb_bound_str, (string_of_int opt.prolific_symb_bound));
   (lt_threshold_str, (string_of_int opt.lt_threshold));
   (clause_weak_htbl_str, (string_of_bool opt.clause_weak_htbl));
   (gc_record_bc_elim_str, (string_of_bool opt.gc_record_bc_elim));  
 ]


let preprocessing_options_str_list opt =
  [
   (time_out_prep_mult_str, (string_of_float opt.time_out_prep_mult));
   (splitting_mode_str, (splitting_mode_type_to_str opt.splitting_mode));
   (splitting_grd_str, (string_of_bool opt.splitting_grd));
   (splitting_cvd_str, (string_of_bool opt.splitting_cvd));
   (splitting_cvd_svl_str, (string_of_bool opt.splitting_cvd_svl));
   (splitting_nvd_str, (string_of_int opt.splitting_nvd)); 
   (sub_typing_str, (string_of_bool opt.sub_typing));
   (prep_gs_sim_str, (string_of_bool opt.prep_gs_sim));
   (prep_unflatten_str, (string_of_bool opt.prep_unflatten));
   (prep_res_sim_str, (string_of_bool opt.prep_res_sim));
   (prep_upred_str, (string_of_bool opt.prep_upred));
   (prep_sem_filter_str, (prep_sem_filter_type_to_str opt.prep_sem_filter));
   (prep_sem_filter_out_str, (string_of_bool opt.prep_sem_filter_out));
   (pred_elim_str,(string_of_bool opt.pred_elim));
   (res_sim_input_str, (string_of_bool opt.res_sim_input));
   (eq_ax_congr_red_str, (string_of_bool opt.eq_ax_congr_red));
   (pure_diseq_elim_str, (string_of_bool opt.pure_diseq_elim));  
   (brand_transform_str, (string_of_bool opt.brand_transform));
   (non_eq_to_eq_str, (string_of_bool opt.non_eq_to_eq));
   (prep_def_merge_str, (string_of_bool opt.prep_def_merge));
   (prep_def_merge_prop_impl_str, (string_of_bool opt.prep_def_merge_prop_impl));
   (prep_def_merge_mbd_str, (string_of_bool opt.prep_def_merge_mbd));
   (prep_def_merge_tr_red_str, (string_of_bool opt.prep_def_merge_tr_red));
   (prep_def_merge_tr_cl_str, (string_of_bool opt.prep_def_merge_tr_cl));
   (preprocessed_out_str, (string_of_bool opt.preprocessed_out));
   (preprocessed_stats_str, (string_of_bool opt.preprocessed_stats));
 ]

let abstr_ref_options_str_list opt =
  [
   (abstr_ref_str, abstr_ref_list_type_to_str opt.abstr_ref);
(*
   (abstr_ref_arg_filter_str, (string_of_bool opt.abstr_ref_arg_filter));
   (abstr_ref_sig_str, (string_of_bool opt.abstr_ref_sig));
   (abstr_ref_subs_str, (string_of_bool opt.abstr_ref_subs));
*)
   (abstr_ref_prep_str, (string_of_bool opt.abstr_ref_prep));
   (abstr_ref_until_sat_str, (string_of_bool opt.abstr_ref_until_sat));  
   (* (abstr_terms_sig_str, (string_of_bool opt.abstr_terms_sig));
    * (abstr_skolem_sig_str, (string_of_bool opt.abstr_skolem_sig)); *)
   (abstr_ref_sig_restrict_str, (abstr_ref_sig_restrict_type_to_str opt.abstr_ref_sig_restrict));
   (abstr_ref_af_restrict_to_split_sk_str, (string_of_bool opt.abstr_ref_af_restrict_to_split_sk));
 ]

let sat_options_str_list opt =
  [
   (sat_mode_str, (string_of_bool opt.sat_mode));
   (sat_fm_restart_options_str, (opt.sat_fm_restart_options));
   (sat_gr_def_str, (string_of_bool opt.sat_gr_def));
   (sat_epr_types_str, (string_of_bool opt.sat_epr_types));
   (sat_non_cyclic_types_str, (string_of_bool opt.sat_non_cyclic_types));
   (sat_finite_models_str, (string_of_bool opt.sat_finite_models));
   (sat_fm_lemmas_str,  (string_of_bool opt.sat_fm_lemmas));
   (sat_fm_prep_str,  (string_of_bool opt.sat_fm_prep));
   (sat_fm_uc_incr_str,  (string_of_bool opt.sat_fm_uc_incr));
   (sat_out_model_str, (sat_out_model_type_to_str opt.sat_out_model));
   (sat_out_clauses_str, (string_of_bool opt.sat_out_clauses))
 ]

let qbf_options_str_list opt =
  [
   (qbf_mode_str, (string_of_bool opt.qbf_mode)); 
   (qbf_elim_univ_str, (string_of_bool opt.qbf_elim_univ));
   (qbf_dom_inst_str, (qbf_dom_inst_type_to_str opt.qbf_dom_inst));
   (qbf_dom_pre_inst_str,(string_of_bool opt.qbf_dom_pre_inst));
   (qbf_sk_in_str, (string_of_bool opt.qbf_sk_in));
   (qbf_pred_elim_str, (string_of_bool opt.qbf_pred_elim));
   (qbf_split_str, (string_of_int opt.qbf_split));
 ]

let bmc1_options_str_list opt =
  [
   (bmc1_incremental_str,
    (string_of_bool (val_of_override opt.bmc1_incremental)));
   (bmc1_axioms_str,
    (bmc1_axioms_type_to_str (val_of_override opt.bmc1_axioms)));
   (bmc1_min_bound_str, (string_of_int (val_of_override opt.bmc1_min_bound)));
   (bmc1_max_bound_str, (string_of_int (val_of_override opt.bmc1_max_bound)));
   (bmc1_max_bound_default_str,
    (string_of_int (val_of_override opt.bmc1_max_bound_default)));
   (bmc1_symbol_reachability_str,
    (string_of_bool opt.bmc1_symbol_reachability));
   (bmc1_property_lemmas_str,
    (string_of_bool opt.bmc1_property_lemmas));
   (bmc1_k_induction_str,
    (string_of_bool opt.bmc1_k_induction));
   (bmc1_non_equiv_states_str,
    (string_of_bool opt.bmc1_non_equiv_states));
   (bmc1_deadlock_str,
    (string_of_bool opt.bmc1_deadlock));
   (bmc1_ucm_str,
    (string_of_bool opt.bmc1_ucm));
   (bmc1_add_unsat_core_str,
    (bmc1_add_unsat_core_type_to_str
       (val_of_override opt.bmc1_add_unsat_core)));
   (bmc1_unsat_core_children_str,
    (string_of_bool (val_of_override opt.bmc1_unsat_core_children)));
   (bmc1_unsat_core_extrapolate_axioms_str,
    (string_of_bool (val_of_override opt.bmc1_unsat_core_extrapolate_axioms)));
   (bmc1_out_stat_str,
    (bmc1_out_stat_type_to_str (val_of_override opt.bmc1_out_stat)));
   (bmc1_ground_init_str, (string_of_bool opt.bmc1_ground_init));
   (bmc1_pre_inst_next_state_str, (string_of_bool opt.bmc1_pre_inst_next_state));
   (bmc1_pre_inst_state_str, (string_of_bool opt.bmc1_pre_inst_state));
   (bmc1_pre_inst_reach_state_str, (string_of_bool opt.bmc1_pre_inst_reach_state));
   (bmc1_out_unsat_core_str,
    (string_of_bool (val_of_override opt.bmc1_out_unsat_core)));
   (bmc1_aig_witness_out_str, (string_of_bool opt.bmc1_aig_witness_out));
   (bmc1_verbose_str, (string_of_bool (val_of_override opt.bmc1_verbose)));

   (bmc1_dump_clauses_tptp_str,
    (string_of_bool (val_of_override opt.bmc1_dump_clauses_tptp)));

   (bmc1_dump_unsat_core_tptp_str,
    (string_of_bool (val_of_override opt.bmc1_dump_unsat_core_tptp)));
   (bmc1_dump_file_str,
    (string_of_string_option "-" (val_of_override opt.bmc1_dump_file)));
  (*----BMC1 UCM --*)
   (bmc1_ucm_expand_uc_limit_str, (string_of_int opt.bmc1_ucm_expand_uc_limit));
   (bmc1_ucm_n_expand_iterations_str, (string_of_int opt.bmc1_ucm_n_expand_iterations));
   (bmc1_ucm_extend_mode_str, (string_of_int opt.bmc1_ucm_extend_mode));
   (bmc1_ucm_init_mode_str, (string_of_int opt.bmc1_ucm_init_mode));
   (bmc1_ucm_cone_mode_str, (bmc1_ucm_cone_mode_type_to_str opt.bmc1_ucm_cone_mode));
   (bmc1_ucm_reduced_relation_type_str, (string_of_int opt.bmc1_ucm_reduced_relation_type));
   (bmc1_ucm_relax_model_str, (string_of_int opt.bmc1_ucm_relax_model));
   (bmc1_ucm_full_tr_after_sat_str, (string_of_bool opt.bmc1_ucm_full_tr_after_sat));
   (bmc1_ucm_expand_neg_assumptions_str, (string_of_bool opt.bmc1_ucm_expand_neg_assumptions));
   (bmc1_ucm_layered_model_str, (bmc1_ucm_cone_mode_type_to_str opt.bmc1_ucm_layered_model));
    (* lemmas *)
   (bmc1_ucm_max_lemma_size_str, (string_of_int opt.bmc1_ucm_max_lemma_size));
 ]

let aig_options_str_list opt =
  [
   (aig_mode_str,
    (string_of_bool opt.aig_mode));
  ]

let inst_options_str_list opt =
  [
   (instantiation_flag_str, (string_of_bool opt.instantiation_flag));
   (inst_lit_sel_str, (inst_lit_sel_type_to_str opt.inst_lit_sel));
   (inst_lit_sel_side_str, (cl_measure_type_to_str opt.inst_lit_sel_side));
   (inst_solver_per_active_str, (string_of_int opt.inst_solver_per_active));
(*   (inst_solver_per_clauses_str, (string_of_int opt.inst_solver_per_clauses));
*)
   (inst_solver_calls_frac_str, (string_of_float opt.inst_solver_calls_frac));
   (inst_passive_queue_type_str, (passive_queue_type_to_str opt.inst_passive_queue_type));
   (inst_passive_queues_str, (pass_queues_type_to_str opt.inst_passive_queues));
   (inst_passive_queues_freq_str, (passive_queue_freqs_to_str opt.inst_passive_queues_freq));
   (inst_dismatching_str, (string_of_bool opt.inst_dismatching));
   (inst_eager_unprocessed_to_passive_str, (string_of_bool opt.inst_eager_unprocessed_to_passive));
   (inst_prop_sim_given_str, (string_of_bool opt.inst_prop_sim_given));
   (inst_prop_sim_new_str, (string_of_bool opt.inst_prop_sim_new));
   (inst_subs_new_str, (string_of_bool opt.inst_subs_new));
   (inst_eq_res_simp_str, (string_of_bool opt.inst_eq_res_simp));
   (inst_subs_given_str, (string_of_bool opt.inst_subs_given));
   (inst_orphan_elimination_str, (string_of_bool opt.inst_orphan_elimination));
   (inst_learning_loop_flag_str, (string_of_bool opt.inst_learning_loop_flag));
   (inst_learning_start_str, (string_of_int opt.inst_learning_start));
   (inst_learning_factor_str, (string_of_int opt.inst_learning_factor));
   (inst_start_prop_sim_after_learn_str, (string_of_int opt.inst_start_prop_sim_after_learn));
   (inst_sel_renew_str, (inst_sel_renew_type_to_str opt.inst_sel_renew));
   (inst_lit_activity_flag_str, (string_of_bool opt.inst_lit_activity_flag));
   (inst_restr_to_given_str, (string_of_bool opt.inst_restr_to_given));
   (inst_activity_threshold_str,  (string_of_int opt.inst_activity_threshold));
   (inst_out_proof_str,
    (string_of_bool (val_of_override opt.inst_out_proof)));
 ]

let res_options_str_list opt =
  [
   (resolution_flag_str, (string_of_bool opt.resolution_flag));
   (res_lit_sel_str, (res_lit_sel_type_to_str opt.res_lit_sel));
   (res_lit_sel_side_str, (cl_measure_type_to_str opt.res_lit_sel_side));
   (res_ordering_str, (res_ord_type_to_str opt.res_ordering));
   (res_to_prop_solver_str, (res_to_prop_solver_type_to_str opt.res_to_prop_solver));
   (res_prop_simpl_new_str, (string_of_bool opt.res_prop_simpl_new));
   (res_prop_simpl_given_str, (string_of_bool opt.res_prop_simpl_given));
   (res_passive_queue_type_str, (passive_queue_type_to_str opt.res_passive_queue_type));
   (res_passive_queues_str, (pass_queues_type_to_str opt.res_passive_queues));
   (res_passive_queues_freq_str, (passive_queue_freqs_to_str opt.res_passive_queues_freq));
   (res_forward_subs_str, (res_subs_type_to_str opt.res_forward_subs));
   (res_backward_subs_str, (res_subs_type_to_str opt.res_backward_subs));
   (res_forward_subs_resolution_str, (string_of_bool opt.res_forward_subs_resolution));
   (res_backward_subs_resolution_str, (string_of_bool opt.res_backward_subs_resolution));
   (res_orphan_elimination_str, (string_of_bool opt.res_orphan_elimination));
   (res_time_limit_str, (string_of_float opt.res_time_limit));
   (res_out_proof_str, (string_of_bool opt.res_out_proof))
 ]

let comb_options_str_list opt =
  [
   (comb_res_mult_str, (string_of_int opt.comb_res_mult));
   (comb_inst_mult_str, (string_of_int opt.comb_inst_mult));
 ]

let dbg_options_str_list opt =
  [
   (dbg_backtrace_str, (string_of_bool opt.dbg_backtrace));
   (dbg_dump_prop_clauses_str, (string_of_bool opt.dbg_dump_prop_clauses));
   (dbg_dump_prop_clauses_file_str,
    opt.dbg_dump_prop_clauses_file);
   (dbg_out_stat_str, (string_of_bool opt.dbg_out_stat))   
 ]

(*

  (_str, opt.);
  (_str, (_type_to_str opt.));
  (_str, (string_of_ opt.));

 *)

let input_opt_str opt =
 String.concat ""
    [
     "\n";(s_pref_str ());"Input Options\n\n";
     opt_val_list_to_str (input_options_str_list opt);"\n"
   ]

let general_opt_str opt =
 String.concat ""
    [
     "\n";(s_pref_str ());"General Options\n\n";
     opt_val_list_to_str (general_options_str_list opt);"\n"
   ]

let global_opt_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"Global Options\n\n";
     opt_val_list_to_str (global_options_str_list opt);"\n"
   ]

let preprocessing_opt_str opt =
 String.concat ""
    [
     "\n";(s_pref_str ());"Preprocessing Options\n\n";
     opt_val_list_to_str (preprocessing_options_str_list opt);"\n"
   ]

let abstr_ref_options_str_list opt =
 String.concat ""
    [
     "\n";(s_pref_str ());"Abstraction refinement Options\n\n";
     opt_val_list_to_str (abstr_ref_options_str_list opt);"\n"
   ]


let sat_options_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"SAT Options\n\n";
     opt_val_list_to_str (sat_options_str_list opt);"\n"
   ]

let qbf_options_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"QBF Options\n\n";
     opt_val_list_to_str (qbf_options_str_list opt);"\n"
   ]


let bmc1_opt_str opt =
   String.concat ""
    [
     "\n";(s_pref_str ());"BMC1 Options\n\n";
     opt_val_list_to_str (bmc1_options_str_list opt);"\n"
   ]

let aig_opt_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"AIG Options\n\n";
     opt_val_list_to_str (aig_options_str_list opt);"\n"
   ]

let inst_opt_str opt =
  String.concat ""
    [
  "\n"^(s_pref_str ());"Instantiation Options\n\n";
     opt_val_list_to_str (inst_options_str_list opt);"\n"
   ]

let res_opt_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"Resolution Options\n\n";
     opt_val_list_to_str (res_options_str_list opt);"\n"
   ]

let comb_opt_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"Combination Options\n\n";
     opt_val_list_to_str (comb_options_str_list opt);"\n"
   ]

let dbg_opt_str opt =
  String.concat ""
    [
     "\n";(s_pref_str ());"Debug Options\n\n";
     opt_val_list_to_str (dbg_options_str_list opt);"\n"
   ]



let control_opt_str opt =
  String.concat ""
    [
     (general_opt_str opt);
     (global_opt_str opt);
     (preprocessing_opt_str opt);
     (abstr_ref_options_str_list opt);
     (sat_options_str opt);
     (qbf_options_str opt);
     (bmc1_opt_str opt);
     (aig_opt_str opt);
     (inst_opt_str opt);
     (res_opt_str opt);
     (comb_opt_str opt);
     (dbg_opt_str opt);
   ]

let all_opt_str opt =
  (input_opt_str opt)^(control_opt_str opt)

let options_to_str opt =
  let close_str = (s_pref_str ())^"\n" in
  (*(pref_str^(out_options_type_to_str opt.out_options)^"\n";*)
  match val_of_override opt.out_options with
  | Out_All_Opt -> (all_opt_str opt)^close_str
  | Out_Control_Opt -> (control_opt_str opt)^close_str
  | Out_No_Opt -> ""

(* inferred options: *)

let prop_solver_is_on () =
  !current_options.instantiation_flag ||
  !current_options.res_prop_simpl_new ||
  !current_options.res_prop_simpl_given ||
  !current_options.prep_gs_sim ||
  !current_options.prep_res_sim ||
  (match !current_options.res_to_prop_solver with
    Res_to_Solver_Active | Res_to_Solver_Passive -> true
  | Res_to_Solver_None -> false)

(*-------------Read Current Options--------------------------*)

let usage_msg = "koala [options] [filename]\n\n"
    (* ugly hack, redo via format later *)
  ^(dash_str "Input Options")^"\n"

let help_msg = "--help  Display list of options\n"

(*
  let read_args() =
  Arg.parse spec_list default_arg_fun usage_msg
 *)

let read_args() =
  let args = Sys.argv in
  (* let iprover_name = args.(0) in
     let current = Arg.current in *)
  try
    Arg.parse_argv args spec_list default_arg_fun usage_msg
  with

  | Arg.Bad s -> (
      let str_list = Str.split (Str.regexp "\n") s in
      out_str ((List.hd str_list)^"\n\n"
	       ^"Usage: "^usage_msg^"\n"^help_msg);
      (*
	out_str (s^ipr_name^": "^"unknown option "
	^"`"^(args.(!current))^"'"^"\n \n"
	^usage_msg^"\n"^help_msg);
       *)
      exit (1))

  | Arg.Help s -> (out_str (s); exit (0))

let check_options_consistency () =
  (if (!current_options.problem_files = [] && (not !current_options.stdin))
  then
    ((*Arg.usage spec_list usage_msg;*)
     out_str (usage_msg^"\n"^help_msg);
     failwith "No problem files to solve")
  else ()
  );
  (if (!current_options.prep_def_merge_tr_cl && !current_options.prep_def_merge_tr_red)
  then 
     failwith "should be either: --prep_def_merge_tr_cl false or --prep_def_merge_tr_red false"
  );
  (if ((val_of_override !current_options.bmc1_incremental) && !current_options.eq_ax_congr_red) 
  then
    (out_warning "setting --eq_ax_congr_red false";
     !current_options.eq_ax_congr_red <- false
    )
  ); 
  (
   if (!current_options.bmc1_pre_inst_state) && ((not !current_options.bmc1_pre_inst_next_state) || (not !current_options.bmc1_pre_inst_reach_state))
   then
     failwith "if \"--bmc1_pre_inst_state true\" then it  should be --bmc1_pre_inst_next_state true and --bmc1_pre_inst_reach_state true"
   else ()
  );
  (* manage different MC options *)
  (
   if !current_options.aig_mode && (not (val_of_override !current_options.bmc1_incremental))
   then
     failwith "if --aig_mode true then --bmc1_incremental should also be true"
   else ()
  );
  (
   if !current_options.bmc1_k_induction && (not (val_of_override !current_options.bmc1_incremental))
   then
     failwith "if --bmc1_k_induction true then --bmc1_incremental should also be true"
   else ()
  );
  (
   if !current_options.bmc1_property_lemmas && (not (val_of_override !current_options.bmc1_incremental))
   then
     failwith "if --bmc1_property_lemmas true then --bmc1_incremental should also be true"
   else ()
  );
  (
   if !current_options.bmc1_deadlock && (not (val_of_override !current_options.bmc1_incremental))
   then
     failwith "if --bmc1_deadlock true then --bmc1_incremental should be also true"
   else ()
  );
  (
   if  (!current_options.bmc1_deadlock && !current_options.bmc1_property_lemmas)
    || (!current_options.bmc1_deadlock && !current_options.bmc1_k_induction)
    || (!current_options.bmc1_property_lemmas && !current_options.bmc1_k_induction)
   then
     failwith "only one of --bmc1_deadlock, --bmc1_property_lemmas or --bmc1_k_induction should be true"
   else ()
  );
  (
   if (!current_options.bmc1_ucm_reduced_relation_type = 2)
   then
     failwith "--bmc1_ucm_reduced_relation_type 2 is currently unsupported"
  );
  (
   if (!current_options.soft_assumptions && !current_options.bmc1_ucm_expand_neg_assumptions)
   then
     failwith "only one of --soft_assumptions and --bmc1_ucm_expand_neg_assumptions could be true"
  );
  (
   if ((not !current_options.bmc1_ucm_full_tr_after_sat) && not (!current_options.bmc1_ucm_cone_mode == BMC1_Ucm_Cone_Mode_None))
   then
     failwith "BMC1 TR model mode (--bmc1_ucm_full_tr_after_sat false) require no code (expect --bmc1_ucm_cone_mode none)"
  );
  (

(*
   if ((!current_options.bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_AIG) &&
      ((not !current_options.aig_mode) || !current_options.pred_elim))
   then
     failwith "--bmc1_ucm_cone_mode 1 works only with --aig_mode true --pred_elim false"
*)
  );
  (* (                                                                                                                                 *)
  (*  if !current_options.bmc1_ucm && ((val_of_override !current_options.bmc1_add_unsat_core) = BMC1_Add_Unsat_Core_None) *)
  (*  then                                                                                                                             *)
  (*    failwith "if --bmc1_ucm true then --bmc1_add_unsat_core should not be none"                                       *)
  (*  else ()                                                                                                                          *)
  (* );                                                                                                                                *)
  (
   if (!current_options.sat_finite_models && (not !current_options.sat_mode))
   then
     failwith "if --sat_finite_model true then --sat_mode should be also true"
  )

let () = read_args();
  check_options_consistency ()

let get_problem_files () = !current_options.problem_files

(*-------------------------------------------------------------------*)
(*----- Some predefined options we will use in schedules-------------*)

type named_options = { options_name : string; options : options }

(*creates a fresh copy of the option*)
(* we need to use dummy out_options = option.out_options *)
let copy_options option = { option with out_options = option.out_options }

(* Input Options *)
let input_options = copy_options !current_options

let input_named_options =
  { options_name = "Input Options"; options = input_options }

(*--------------------------------*)
let strip_conj_named_opt named_opt =
  let new_opt =
    { named_opt.options with

      inst_lit_sel =
      strip_conj_lit_type_list named_opt.options.inst_lit_sel;

      inst_passive_queues = strip_conj_clause_type_list_list named_opt.options.inst_passive_queues;
      res_passive_queues = strip_conj_clause_type_list_list named_opt.options.res_passive_queues;
    }
  in
  { options = new_opt;
    options_name = (named_opt.options_name^" stripped conjectures") }

(*--------Creates a reasonable option to deal with many axioms such as SUMO-----*)
(* helper function: replace [l1;l2;...;ln] with [l1';l2] *)
let make_new_opt_list prefix list l1' =
  let tl1 = match list with
    | hd::tl -> tl
    | [] -> failwith ("Option --"^prefix^"_passive_queues expected to have at least 2 lists")
  in
  let l2 = match tl1 with
    | hd::tl -> hd
    | [] -> failwith ("Option --"^prefix^"_passive_queues expected to have at least 2 lists")
  in
  (* return new list *)
  [l1'; l2]

(*-------based on a given option-------------------*)
let named_opt_to_many_axioms_named_opt1 opt =
  let new_options =
    { opt.options with

      large_theory_mode = true;
(*      prep_sem_filter = Sem_Filter_Neg; *) (* commented 2017 *)
      prep_sem_filter_out = false;
      prolific_symb_bound = 500;
      lt_threshold = 2000;

      inst_passive_queues = make_new_opt_list "inst" opt.options.inst_passive_queues
        [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Var false];

      inst_passive_queues_freq = [1000;2];

      res_passive_queues = make_new_opt_list "res" opt.options.res_passive_queues
        [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Symb false];
      
      res_passive_queues_freq = [1000;5];

      res_backward_subs = Subs_Subset;
      res_forward_subs_resolution = false;
      res_backward_subs_resolution = false;
      res_orphan_elimination = false;
    }
  in
  { options_name = ("Many Axioms 1 "^opt.options_name);
    options = new_options }

(*----------Many Axioms 2-----------------------*)
let named_opt_to_many_axioms_named_opt2 opt =
  let new_options =
    { opt.options with

      large_theory_mode = true;
(*      prep_sem_filter = Sem_Filter_Neg; *) (* commented 2017 *)
      prep_sem_filter_out = false;
      prolific_symb_bound = 500;
      lt_threshold = 2000;

      inst_passive_queues = make_new_opt_list "inst" opt.options.inst_passive_queues
        [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Var false];

      inst_passive_queues_freq = [1000;2];

      inst_prop_sim_given = false;
      inst_prop_sim_new = false;
      inst_orphan_elimination = !current_options.inst_orphan_elimination;
      inst_learning_start = 3000000;
      inst_learning_factor = 2;

      res_passive_queues = make_new_opt_list "res" opt.options.res_passive_queues
        [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Var false];

      res_prop_simpl_new = false;
      res_prop_simpl_given = false;

      res_passive_queues_freq = [1000;2];

      res_forward_subs = Subs_Subset;
      res_backward_subs = Subs_Subset;
      res_forward_subs_resolution = false;
      res_backward_subs_resolution = false;
      res_orphan_elimination = false;
      comb_res_mult = 100;
      comb_inst_mult = 1000;
    }
  in
  { options_name = ("Many Axioms 2 "^opt.options_name);
    options = new_options }

(*------------------------------------------------*)

let named_opt_to_many_axioms_named_opt3 opt =
  let new_options =
    { opt.options with

      large_theory_mode = true;
(*      prep_sem_filter = Sem_Filter_Neg; *) (* commented 2017 *)
      prep_sem_filter_out = false;
      prolific_symb_bound = 500;
      lt_threshold = 2000;

      inst_passive_queues = make_new_opt_list "inst" opt.options.inst_passive_queues
        [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Var false; Cl_Max_Atom_Input_Occur false];

      inst_passive_queues_freq = [1000;2];

      res_passive_queues = make_new_opt_list "res" opt.options.res_passive_queues
        [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Symb false; Cl_Max_Atom_Input_Occur false];
      res_passive_queues_freq = [1000;5];
      res_backward_subs = Subs_Subset;
      res_forward_subs_resolution = false;
      res_backward_subs_resolution = false;
      res_orphan_elimination = false;
    }
  in
  { options_name = ("Many Axioms 3 "^opt.options_name);
    options = new_options }

(*-------Negative Selections------------------------*)
let option_1 () = { (*(!current_options)*) input_options with

  (*----General--------*)
  fix_init_inter = None;
  non_eq_to_eq = false;
  clausify_out = false;
  large_theory_mode = true;
  prep_sem_filter_out = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;

 (*----QBF Mode------*)


  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;
  inst_lit_sel = [Lit_Sign false;
		  Lit_Num_of_Var false; Lit_Num_of_Symb true];

   inst_lit_sel_side = CM_none; (* 2016 Nov *)
(*  inst_solver_per_active = 750;
    inst_solver_per_clauses = 5000;
*)
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;2];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = true;
  inst_learning_loop_flag = true;
(*
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
*)
(*
  inst_sel_renew = Inst_SR_Model;
  inst_lit_activity_flag = true;
  inst_out_proof = ValueDefault true;
*)

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_neg_sel_max;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  (*  res_forward_subs_resolution    = true; exp later for sat *)
  (* res_backward_subs_resolution   = false; *)
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 2.0;
  (*----Combination--------*)
  comb_res_mult = 300;
  comb_inst_mult = 1000;
}

let named_option_1 () =
  { options_name = "Option_1: Negative Selections"; options = (option_1()) }

(*--------------*)
let option_1_1 () = { (input_options) with

		      inst_lit_sel = [Lit_Sign false;
				      Lit_Num_of_Var false;
				      Lit_Num_of_Symb true];
		      res_lit_sel = Res_neg_sel_max
		    }

let named_option_1_1 () =
  { options_name = "Option_1_1: Negative Selections"; options = (option_1_1()) }

(*--------------*)

let option_1_2 () = { (input_options) with
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_EPR true; Cl_Num_of_Var false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;2];

  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Horn true; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];
		    }

let named_option_1_2 () =
  { options_name = "Option_1_2: EPR, Horn"; options = (option_1_2()) }

(*--Option 2----------------*)

let option_2 () = { (*!current_options*)  input_options with

  (*----General--------*)
  fix_init_inter = None;
  non_eq_to_eq = false;
  clausify_out = false;

  large_theory_mode = true;
  prep_sem_filter_out = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;	

(*----QBF Mode------*)
 
  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;
  inst_lit_sel = [Lit_Sign false;
		  Lit_Num_of_Var false; Lit_Num_of_Symb false];
(*
  inst_solver_per_active = 750;
  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = !current_options.inst_passive_queue_type;
  inst_passive_queues =
    [
      [Cl_Num_of_Symb false; Cl_Num_of_Var false; Cl_Conj_Dist false; Cl_Has_Conj_Symb true];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;2];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = true;
  inst_learning_loop_flag = true;
(*
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Model;
  inst_lit_activity_flag = true;

  inst_out_proof = ValueDefault true;
*)

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_KBO_max;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queues =
    [
      [Cl_Num_of_Symb false; Cl_Has_Conj_Symb true];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 2.0;
  (*----Combination--------*)
  comb_res_mult = 300;
  comb_inst_mult = 1000;

}

let named_option_2 () =
  { options_name = "Option_2: Max Selections"; options = (option_2()) }

let option_2_1 () = { (option_2 ()) with
		      inst_lit_sel = [Lit_Sign false;
				      Lit_Num_of_Var false;
				      Lit_Num_of_Symb true];

		      res_lit_sel = Res_KBO_max;
		    }

let named_option_2_1 () =
  { options_name = "Option_2_1: Max Selections"; options = (option_2_1()) }

(*--Option 3----------------*)

let option_3 () = {(* !current_options *) input_options with

  (*----General--------*)
  fix_init_inter = None;

  non_eq_to_eq = false;
  clausify_out = false;

  large_theory_mode = true;
  prep_sem_filter_out = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;	

(*----QBF Mode------*)
 
  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;
  inst_lit_sel = [Lit_Sign false; Lit_Num_of_Symb false];

  inst_lit_sel_side = CM_num_var; (* 2016 Nov *)
(*
  inst_solver_per_active = 750;
  inst_solver_per_clauses = 5000;
*)
  inst_passive_queues =
    [
      [Cl_Num_of_Symb false; Cl_Conj_Dist false; Cl_Has_Conj_Symb true];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;2];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = true;
  inst_learning_loop_flag = true;
(*
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Model;

  inst_lit_activity_flag = true;


  inst_out_proof = ValueDefault true;
*)
  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_neg_sel_min;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true; 
  res_passive_queues =
    [
      [Cl_Num_of_Symb false; Cl_Has_Conj_Symb true];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 2.0;
  (*----Combination--------*)
  comb_res_mult = 300;
  comb_inst_mult = 1000;
}

let named_option_3 () =
  { options_name = "Option_3: Min Selections"; options = (option_3()) }

let option_3_1 () = { (input_options) with
		      inst_lit_sel = [Lit_Sign false; Lit_Num_of_Symb true];
		      res_lit_sel = Res_neg_sel_min;
		    }

let named_option_3_1 () =
  { options_name = "Option_3_1: Min Selections"; options = (option_3_1()) }

(*--Option 4----------------*)

let option_4 () = { (* !current_options *) input_options with

  (*----General--------*)
  fix_init_inter = None;

  non_eq_to_eq = false;
  clausify_out = false;

  large_theory_mode = true;
  prep_sem_filter_out = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;	

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;
  inst_lit_sel = [Lit_Sign true; Lit_Num_of_Var false; Lit_Num_of_Symb false];

(*
  inst_solver_per_active = 750;
  inst_solver_per_clauses = 5000;
*)
  inst_passive_queues =
    [
      [Cl_Has_Conj_Symb true; Cl_Num_of_Symb false];
      [Cl_Age true]
    ];
  inst_passive_queues_freq = [25;10];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = true;
  inst_learning_loop_flag = true;
(*
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Model;
  inst_lit_activity_flag = true;
  inst_out_proof = ValueDefault true;
*)
  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_adaptive;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queues =
    [
      [Cl_Has_Conj_Symb true];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;10];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = false;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 2.0;
  (*----Combination--------*)
  comb_res_mult = 300;
  comb_inst_mult = 1000;
}

let named_option_4 () =
  { options_name = "Option_4: Selections"; options = (option_4()) }

let option_4_1 () = { (input_options) with
		      inst_lit_sel = [Lit_Sign true; Lit_Num_of_Var false; Lit_Num_of_Symb false];
		      res_lit_sel = Res_adaptive;
		    }

let named_option_4_1 () =
  { options_name = "Option_4_1: Selections"; options = (option_4_1()) }

(*------Finite Models--------------------------------------*)
let named_opt_sat_mode_off named_opt =
  { options_name = named_opt.options_name^" sat_mode off";
    options = { named_opt.options with
		sat_mode = false; sat_finite_models = false; sat_out_model = Model_Small }}

let named_opt_sat_mode_on named_opt =
  { options_name = named_opt.options_name^" sat_mode on";
    options = { named_opt.options with sat_mode = true; sat_finite_models = true; }}

let option_finite_models_before_2018_06 () = {(* !current_options *) input_options with

  (*----General--------*)
  fix_init_inter = None;

  schedule = Schedule_none;
  non_eq_to_eq = false;
  clausify_out = false;

  large_theory_mode = false;
  prep_sem_filter_out = false;
  brand_transform = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode-----*)
  sat_mode = true;
  sat_gr_def = false;
  sat_finite_models = true;

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;


  inst_lit_sel = [Lit_Prop true; Lit_Sign false; Lit_Ground true;
		  Lit_Num_of_Var false; Lit_Num_of_Symb false];

  (*
    inst_lit_sel = [Lit_Sign true;
    Lit_Num_of_Var false; Lit_Num_of_Symb false];
   *)
  (*
    inst_lit_sel = [ Lit_Ground true; Lit_Sign false;
    Lit_Num_of_Var true; Lit_Num_of_Symb false];
   *)
(*
  inst_solver_per_active = 750;
  inst_solver_per_clauses = 5000;
*)

  inst_passive_queues =
    [
      [Cl_Num_of_Var false; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [20;10];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;

  (* should not prop simplify! can lead to inconsistency  *)
  inst_prop_sim_given = false;
  inst_prop_sim_new = false;
  inst_learning_loop_flag = true;
(*
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Model;
  inst_lit_activity_flag = true;
  inst_out_proof = ValueDefault true;
*)
  (*----Resolution---------*)
  (*---always resolution_flag false-------------------*)
  resolution_flag = false;
  res_lit_sel = Res_adaptive;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Full;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = true;
  res_orphan_elimination = true;
  res_time_limit = 2.0;
  (*----Combination--------*)
  comb_res_mult = 1;
  comb_inst_mult = 1000;
}

(*----------------*)
let option_finite_models_2018_06_26357_sat () = {(* !current_options *) input_options with

(*
  (*----Input-------*)
  problem_path = "";
  include_path = "";
  problem_files = [];
  clausifier = "";
  clausifier_options = "";
  stdin = false;
  dbg_backtrace = false;
  dbg_dump_prop_clauses = false;
  dbg_dump_prop_clauses_file = "-";
  dbg_out_stat = false;
*)

  (*----General--------*)
(*
  fix_init_inter = None;
  time_out_real = -1.;
*)
  time_out_prep_mult = 0.2;
(*
  time_out_virtual = -1.;
*)
  schedule = Schedule_none;
  splitting_mode = Split_Input;
  splitting_grd = false;
  splitting_cvd = true;
  splitting_cvd_svl = true;
  splitting_nvd = 256;
  non_eq_to_eq = false;
  prep_gs_sim = false;
  prep_unflatten = true;
  prep_res_sim = true;
  prep_upred   = true;
  res_sim_input = false;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
  prep_sem_filter = Sem_Filter_None; (* Sem_Filter_Exhaustive; *)
  prep_sem_filter_out = false;
  preprocessed_out = false;
  preprocessed_stats = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = false;
  min_unsat_core = false;
  pred_elim  =  true;
  add_important_lit = false;
  soft_assumptions = false;
  soft_lemma_size = 3;
  prop_impl_unit_size = 0;
  prop_impl_unit = [];
  share_sel_clauses = true;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = [BCI_conj_cone]; 
  conj_cone_tolerance = 3.;
  extra_neg_conj = ENC_all_pos_neg;

  abstr_ref = [];
  abstr_ref_prep = false;
  abstr_ref_until_sat = false;
  abstr_ref_sig_restrict = Funpre;
  abstr_ref_af_restrict_to_split_sk = false;

  prep_def_merge = false;
  prep_def_merge_prop_impl = false;
  prep_def_merge_mbd = false;
  prep_def_merge_tr_red = false;
  prep_def_merge_tr_cl = false;

(*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*---Sat mode------------*)
  sat_mode = true;
  sat_fm_restart_options = "";
  sat_epr_types = false;
  sat_non_cyclic_types = true;
  sat_gr_def = false;
  sat_finite_models = true;
  sat_fm_lemmas = false;
  sat_fm_prep   = false;
(*  sat_fm_uc_incr = false; *)
  sat_fm_uc_incr = true; 
  sat_out_model = Model_Small;
  sat_out_clauses = false;

(*---QBF mode------------*)
  qbf_mode = false;
  qbf_elim_univ = false;
  qbf_dom_inst = QBF_dom_inst_none; (* QBF_dom_inst_chain; *)
  qbf_dom_pre_inst = false;
  qbf_sk_in = false;
  qbf_pred_elim = true;
  qbf_split = 512;

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  (*bmc1_symbol_reachability should be modified only by input options and not by options in schedule since it is calculated before options in schedule become active *)
  bmc1_symbol_reachability = false;
  bmc1_property_lemmas = false;
  bmc1_k_induction = false;
  bmc1_non_equiv_states = false;
  bmc1_deadlock = false;
  bmc1_ucm = false;
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_ground_init = false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_aig_witness_out = false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;
  (*----BMC1 UCM --*)
  bmc1_ucm_expand_uc_limit = 128;
  bmc1_ucm_n_expand_iterations = 6;
  bmc1_ucm_extend_mode = 1;
  bmc1_ucm_init_mode = 2;
  bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_None;
  bmc1_ucm_reduced_relation_type = 0;
  bmc1_ucm_relax_model = 4; (* symbols/clear *)
  bmc1_ucm_full_tr_after_sat = true;
  bmc1_ucm_expand_neg_assumptions = false;
  bmc1_ucm_layered_model = BMC1_Ucm_Cone_Mode_None;
  (* lemmas *)
  bmc1_ucm_max_lemma_size = 10;


  (*----AIG----------------*)
  aig_mode = false;

  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [Lit_Sign false; Lit_Num_of_Symb true; Lit_has_non_prolific_conj_symb true;];

  inst_lit_sel_side = CM_num_lit;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 0.01; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 1400; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
     [Cl_Conj_Dist true; Cl_Num_of_Lits true; Cl_Age false];
     [Cl_Has_Conj_Symb false; Cl_min_defined_symb false; Cl_bc_imp_inh true];
   ];
  inst_passive_queues_freq = [512;64];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = false;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = false; 
  inst_prop_sim_new = true;
  inst_subs_given = true;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = false;
  inst_learning_loop_flag = true;
  inst_learning_start = 5;
  inst_learning_factor = 8;
  inst_start_prop_sim_after_learn = 0;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = true;
  inst_restr_to_given = false;
  inst_activity_threshold = 10000;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = false;
  res_lit_sel = Res_neg_sel_nrc;
  res_lit_sel_side = CM_cnt;
  res_ordering = Res_ord_kbo;
  res_to_prop_solver = Res_to_Solver_None;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
     [Cl_Num_of_Lits false; Cl_Num_of_Var false; Cl_Horn true];
     [Cl_Ground false; Cl_Has_Conj_Symb true; Cl_Conj_Dist true];
   ];

  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 0.1;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 10;
  comb_inst_mult = 100;
}

(*--------*)
let named_option_finite_models () =
  { options_name = "Option: Finite Models"; 
    options = (option_finite_models_before_2018_06 ())
    (* options = (option_finite_models_2018_06_26357_sat ()) *)    
}

(*------------------------------------*)
let option_epr_non_horn_non_eq_before_2018 () = { (* !current_options *)  input_options (* !!! changed !!!*) with
(*------------------------------------*)

  (*----General--------*)
  fix_init_inter = None;
  non_eq_to_eq = false;
  clausify_out = false;

  large_theory_mode = true;
  prep_sem_filter_out = false;
  brand_transform = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;	

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;
  (*------------------------------------------*)


(*  inst_lit_sel = [Lit_Ground true; Lit_Sign false;]; *) (* before Jul 2015 *)
   
(*   inst_lit_sel = [Lit_Sign false; Lit_Ground true; Lit_Sign false;]; *)  (* before Jul 2016 *)
   inst_lit_sel = [Lit_Prop true; Lit_Sign false; Lit_Ground true; ];   (* before Jul 2016 *)

(*   inst_lit_sel = [Lit_Sign false; Lit_Num_of_Symb true;  Lit_Num_of_Var true];*)   (* before Jul 2015 *)
 
  (* before Intel example bpbimodalm_miter_full.focnf.bit_blast.Mclk1 *)
  (* inst_solver_per_active         = 750; after 7500 *)
  (*  inst_solver_per_active         = 750;*)
  (*  inst_solver_per_active         = 7500;*)

			       (*inst_solver_per_active = !current_options.inst_solver_per_active;*)

  (* inst_solver_per_clauses        = 5000; is ok*)
  (*  inst_solver_per_clauses        = 5000;*)
(*  inst_solver_per_clauses = !current_options.inst_solver_per_clauses;*)

  inst_passive_queue_type = input_options.inst_passive_queue_type;
(*
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false; ];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
*)
    inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false; ];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;20];

(*  inst_dismatching = false; *) 
    inst_dismatching               =  input_options.inst_dismatching;

  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = false;
  inst_learning_loop_flag = true;

  inst_learning_start = 30000;
  inst_learning_factor = 2;
(*  inst_start_prop_sim_after_learn = 3;*)

  inst_sel_renew = Inst_SR_Solver;
  inst_lit_activity_flag =  false; (* true;  *)
  (*  inst_lit_activity_flag            = true;*)
 (* inst_out_proof = ValueDefault true;*)

  (*----Resolution----------------------------*)
  resolution_flag = false; (* input_options.resolution_flag;*) (* true; *)
  (*------------------------------------------*)
  res_lit_sel = Res_adaptive;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = input_options.res_prop_simpl_given; (* true;*)
  res_passive_queue_type = input_options.res_passive_queue_type;
  res_passive_queues =
    [
(*      [Cl_Has_Conj_Symb true]; *)
      [Cl_Has_Conj_Symb true;Cl_Num_of_Var false; Cl_Num_of_Symb false]; 
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;10];

  res_forward_subs = Subs_Full;  (* Subs_Subset; *)
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = false;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;

  res_time_limit = 0.1; 
  (*----Combination--------*)
  comb_res_mult = 30;
  comb_inst_mult = 100; 
}


let option_epr_non_horn_non_eq_smac_2018_06_2946 () = { (* !current_options *)  input_options (* !!! changed !!!*) with
(*------------------------------------*)

  (*----General--------*)
  fix_init_inter = None;
  non_eq_to_eq = false;
  
  large_theory_mode = true;
  prolific_symb_bound = 500;
  lt_threshold = 2000;
  
(*----- prep ------*)                                                      
 time_out_prep_mult = 0.1;
  splitting_mode = Split_Input;
  splitting_grd = false;
  splitting_cvd = false;
  splitting_cvd_svl = false;
  splitting_nvd = 128;

   prep_gs_sim = true;
  prep_unflatten = true;
  prep_res_sim = true;
  prep_upred   = true;
  res_sim_input = false;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  prep_sem_filter    = Sem_Filter_Pos;
(*  prep_sem_filter = Sem_Filter_Exhaustive; *) (* commented 2017 *)
  prep_sem_filter_out = false;
  preprocessed_out = false;
  sub_typing          = false;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  = true;
  add_important_lit = false;
     
  reset_solvers = false;

  bc_imp_inh = []; 
  conj_cone_tolerance = 1.5;
  abstr_ref = [];                       

 
  (*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;	

  (*----BMC1---------------*)
  bmc1_symbol_reachability = true;

  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----Instantiation------*)
  instantiation_flag = true;
  (*------------------------------------------*)
  inst_activity_threshold = 1000;
  inst_restr_to_given = false;

(*  inst_lit_sel = [Lit_Ground true; Lit_Sign false;]; *) (* before Jul 2015 *)
   
(*   inst_lit_sel = [Lit_Sign false; Lit_Ground true; Lit_Sign false;]; *)  (* before Jul 2016 *)
   inst_lit_sel = [Lit_has_non_prolific_conj_symb false; Lit_Atom_depth false; Lit_Ground false; ];
   inst_lit_sel_side = CM_num_var;                                                     
   inst_solver_per_active         = 750;

(*   inst_lit_sel = [Lit_Sign false; Lit_Num_of_Symb true;  Lit_Num_of_Var true];*)   (* before Jul 2015 *)
 
  (* before Intel example bpbimodalm_miter_full.focnf.bit_blast.Mclk1 *)
  (* inst_solver_per_active         = 750; after 7500 *)

  (*  inst_solver_per_active         = 7500;*)

			       (*inst_solver_per_active = !current_options.inst_solver_per_active;*)

  (* inst_solver_per_clauses        = 5000; is ok*)
  (*  inst_solver_per_clauses        = 5000;*)
(*  inst_solver_per_clauses = !current_options.inst_solver_per_clauses;*)

  inst_passive_queue_type = PQT_PriorityQueues;
(*
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false; ];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
*)
    inst_passive_queues =
    [
      [Cl_Num_of_Var false; Cl_Conj_Dist false; Cl_Age true;];
      [Cl_Ground false; Cl_Has_Conj_Symb false;]
    ];
  inst_passive_queues_freq = [100;1];

(*  inst_dismatching = false; *) 
    inst_dismatching               =  false;

  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = true;
  inst_learning_loop_flag = true;

  inst_learning_start = 3000;
  inst_learning_factor = 4;
  inst_start_prop_sim_after_learn = 10;
  inst_orphan_elimination = true;
  inst_subs_given = false;
  inst_subs_new = false;
  inst_solver_calls_frac = 3.;
  inst_sel_renew = Inst_SR_Solver;
  inst_lit_activity_flag =  true; (* true;  *)
  (*  inst_lit_activity_flag            = true;*)
 (* inst_out_proof = ValueDefault true;*)

  (*----Resolution----------------------------*)
  resolution_flag = true; (* input_options.resolution_flag;*) (* true; *)
  (*------------------------------------------*)
  res_lit_sel = Res_neg_sel_nrc;
  res_lit_sel_side = CM_cnt;
  res_to_prop_solver = Res_to_Solver_Passive;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true; (* true;*)
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
       [Cl_Num_of_Symb false; Cl_Num_of_Lits true;  Cl_bc_imp_inh true;];
       [Cl_bc_imp_inh true; Cl_Num_of_Symb true; Cl_min_defined_symb true]
    ];
  res_passive_queues_freq = [5;1];

  res_forward_subs = Subs_Subset;  (* Subs_Subset; *)
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = true;

  res_time_limit = 0.01; 
  (*----Combination--------*)
  comb_res_mult = 1000;
  comb_inst_mult = 1000; 
}


(*------------*)
let named_option_epr_non_horn_non_eq () =
  { options_name = "Option_epr_non_horn_non_eq"; options = (option_epr_non_horn_non_eq_smac_2018_06_2946 ()) }

(*-----------------------*)
let option_epr_non_horn_eq_before_2018_06 () = { (* !current_options *)  input_options (* !!! changed !!!*) with 


 (*----General--------*)
  time_out_prep_mult = 0.1;
  splitting_mode = Split_None;
  splitting_grd = false;
  splitting_cvd = true;
  splitting_cvd_svl = true;
  splitting_nvd = 16;

  non_eq_to_eq = false;
  prep_gs_sim = true;
  prep_unflatten = true;
  prep_res_sim = true;
  prep_upred   = true;
  res_sim_input = true;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
(*  prep_sem_filter = Sem_Filter_Exhaustive; *) (* commented 2017 *)
  prep_sem_filter_out = false;
  preprocessed_out = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  = true;
  add_important_lit = false;
     
  reset_solvers = false;

  bc_imp_inh = [BCI_conj_cone]; 
  conj_cone_tolerance = 1.5;
  abstr_ref = [];                       
(*  abstr_ref_arg_filter = true; *)

  (*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

 
  (*----BMC1---------------*)
  bmc1_symbol_reachability = true;


  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [ Lit_Sign false; Lit_Num_of_Var true; Lit_has_conj_symb true; Lit_Prop true]; 

  inst_lit_sel_side = CM_num_lit;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 0.1; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 300; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
      [Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Lits false; Cl_Age true];
(* Cl_Conj_Dist false; Cl_Has_Conj_Symb true; ];*)
 (*     [Cl_Age true; Cl_Num_of_Symb false] *)
     [Cl_Num_of_Var false; Cl_Num_of_Symb false; Cl_bc_imp_inh true]
    ];
  inst_passive_queues_freq = [25;5];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = true; 
  inst_prop_sim_new = true;
  inst_subs_given = true;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 1000;
  inst_learning_factor = 16;
  inst_start_prop_sim_after_learn = 10;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = false;
  inst_restr_to_given = false;
  inst_activity_threshold = 100;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_neg_sel_nrc; 
  res_lit_sel_side = CM_none;
  res_to_prop_solver = Res_to_Solver_Passive;
  res_prop_simpl_new = false;
  res_prop_simpl_given = false;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
      [Cl_bc_imp_inh true];
      [Cl_Num_of_Symb false; Cl_Age false]
    ];
  res_passive_queues_freq = [25;5];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = false;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 3.0;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 10;
  comb_inst_mult = 1000;
}


(*-----------------------------------*)
let options_epr_non_horn_eq_samc_2018_06_28_15973 () = { input_options  with 
(*
  (*----Input-------*)
  problem_path = "";
  include_path = "";
  problem_files = [];
  clausifier = "";
  clausifier_options = "";
  stdin = false;
  dbg_backtrace = false;
  dbg_dump_prop_clauses = false;
  dbg_dump_prop_clauses_file = "-";
  dbg_out_stat = false;
*)

  (*----General--------*)
(*
  fix_init_inter = None;
  time_out_real = -1.;
*)
  time_out_prep_mult = 0.2;
(*
  time_out_virtual = -1.;
*)
  schedule = Schedule_none;
  splitting_mode = Split_Input;
  splitting_grd = true;
  splitting_cvd = false;
  splitting_cvd_svl = true;
  splitting_nvd = 128;
  non_eq_to_eq = false;
  prep_gs_sim = false;
  prep_unflatten = true;
  prep_res_sim = false;
  prep_upred   = true;
  res_sim_input = false;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
  prep_sem_filter = Sem_Filter_Neg; (* Sem_Filter_Exhaustive; *)
  prep_sem_filter_out = false;
  preprocessed_out = false;
  preprocessed_stats = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  =  true;
  add_important_lit = false;
  soft_assumptions = false;
  soft_lemma_size = 3;
  prop_impl_unit_size = 0;
  prop_impl_unit = [];
  share_sel_clauses = false;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = [BCI_conj_cone]; 
  conj_cone_tolerance = 3.;
  extra_neg_conj = ENC_none;

  abstr_ref = [];
  abstr_ref_prep = false;
  abstr_ref_until_sat = false;
  abstr_ref_sig_restrict = Funpre;
  abstr_ref_af_restrict_to_split_sk = false;

  prep_def_merge = false;
  prep_def_merge_prop_impl = false;
  prep_def_merge_mbd = false;
  prep_def_merge_tr_red = false;
  prep_def_merge_tr_cl = false;

(*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*---Sat mode------------*)
  sat_mode = false;
  sat_fm_restart_options = "";
  sat_epr_types = true;
  sat_non_cyclic_types = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep   = false;
(*  sat_fm_uc_incr = false; *)
  sat_fm_uc_incr = true; 
  sat_out_model = Model_Small;
  sat_out_clauses = false;

(*---QBF mode------------*)
  qbf_mode = false;
  qbf_elim_univ = false;
  qbf_dom_inst = QBF_dom_inst_none; (* QBF_dom_inst_chain; *)
  qbf_dom_pre_inst = false;
  qbf_sk_in = false;
  qbf_pred_elim = true;
  qbf_split = 512;

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  (*bmc1_symbol_reachability should be modified only by input options and not by options in schedule since it is calculated before options in schedule become active *)
  bmc1_symbol_reachability = true;
  bmc1_property_lemmas = false;
  bmc1_k_induction = false;
  bmc1_non_equiv_states = false;
  bmc1_deadlock = false;
  bmc1_ucm = false;
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_ground_init = false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_aig_witness_out = false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;
  (*----BMC1 UCM --*)
  bmc1_ucm_expand_uc_limit = 128;
  bmc1_ucm_n_expand_iterations = 6;
  bmc1_ucm_extend_mode = 1;
  bmc1_ucm_init_mode = 2;
  bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_None;
  bmc1_ucm_reduced_relation_type = 0;
  bmc1_ucm_relax_model = 4; (* symbols/clear *)
  bmc1_ucm_full_tr_after_sat = true;
  bmc1_ucm_expand_neg_assumptions = false;
  bmc1_ucm_layered_model = BMC1_Ucm_Cone_Mode_None;
  (* lemmas *)
  bmc1_ucm_max_lemma_size = 10;


  (*----AIG----------------*)
  aig_mode = false;

  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [Lit_has_non_prolific_conj_symb true; Lit_Prop true;];

  inst_lit_sel_side = CM_num_var;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 1.0; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 1400; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
     [Cl_Has_Eq_Lit false; Cl_Has_Conj_Symb true;  Cl_Num_of_Lits false];
     [Cl_Has_Non_Prolific_Conj_Symb true;Cl_Num_of_Lits false; Cl_Conj_Dist false]
   ];
  inst_passive_queues_freq = [10;2];

  inst_dismatching = false;
  inst_eager_unprocessed_to_passive = true;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = false; 
  inst_prop_sim_new = false;
  inst_subs_given = false;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 100;
  inst_learning_factor = 8;
  inst_start_prop_sim_after_learn = 10;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = false;
  inst_restr_to_given = false;
  inst_activity_threshold = 1000;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_neg_sel_nrc;
  res_lit_sel_side = CM_cnt;
  res_ordering = Res_ord_kbo;
  res_to_prop_solver = Res_to_Solver_None;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
     [Cl_Num_of_Lits false; Cl_Num_of_Var false; Cl_Horn true];
     [Cl_Ground false; Cl_Has_Conj_Symb true; Cl_Conj_Dist true];
   ];

  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 0.1;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 100;
  comb_inst_mult = 10000;
}


(*-----------------------------------*)
let options_epr_non_horn_eq_samc_2018_06_28_16873 () = { input_options  with 

(*
  (*----Input-------*)
  problem_path = "";
  include_path = "";
  problem_files = [];
  clausifier = "";
  clausifier_options = "";
  stdin = false;
  dbg_backtrace = false;
  dbg_dump_prop_clauses = false;
  dbg_dump_prop_clauses_file = "-";
  dbg_out_stat = false;
*)

  (*----General--------*)
(*
  fix_init_inter = None;
  time_out_real = -1.;
*)
  time_out_prep_mult = 0.2;
(*
  time_out_virtual = -1.;
*)
  schedule = Schedule_none;
  splitting_mode = Split_Input;
  splitting_grd = true;
  splitting_cvd = false;
  splitting_cvd_svl = true;
  splitting_nvd = 128;
  non_eq_to_eq = false;
  prep_gs_sim = false;
  prep_unflatten = true;
  prep_res_sim = false;
  prep_upred   = true;
  res_sim_input = false;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
  prep_sem_filter = Sem_Filter_Exhaustive;
  prep_sem_filter_out = false;
  preprocessed_out = false;
  preprocessed_stats = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  =  true;
  add_important_lit = false;
  soft_assumptions = false;
  soft_lemma_size = 3;
  prop_impl_unit_size = 32;
  prop_impl_unit = [Lit_bp_conj_symb(false)];
  share_sel_clauses = true;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = [BCI_conj_cone]; 
  conj_cone_tolerance = 3.;
  extra_neg_conj = ENC_none;

  abstr_ref = [];
  abstr_ref_prep = false;
  abstr_ref_until_sat = false;
  (* abstr_terms_sig = false;
   * abstr_skolem_sig = false; *)
  abstr_ref_sig_restrict = Funpre;
  abstr_ref_af_restrict_to_split_sk = false;

  prep_def_merge = true;
  prep_def_merge_prop_impl = true;
  prep_def_merge_mbd = false;
  prep_def_merge_tr_red = false;
  prep_def_merge_tr_cl = false;

(*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*---Sat mode------------*)
  sat_mode = false;
  sat_fm_restart_options = "";
  sat_epr_types = true;
  sat_non_cyclic_types = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep   = false;
(*  sat_fm_uc_incr = false; *)
  sat_fm_uc_incr = true; 
  sat_out_model = Model_Small;
  sat_out_clauses = false;

(*---QBF mode------------*)
  qbf_mode = false;
  qbf_elim_univ = false;
  qbf_dom_inst = QBF_dom_inst_none; (* QBF_dom_inst_chain; *)
  qbf_dom_pre_inst = false;
  qbf_sk_in = false;
  qbf_pred_elim = true;
  qbf_split = 512;

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  (*bmc1_symbol_reachability should be modified only by input options and not by options in schedule since it is calculated before options in schedule become active *)
  bmc1_symbol_reachability = true;
  bmc1_property_lemmas = false;
  bmc1_k_induction = false;
  bmc1_non_equiv_states = false;
  bmc1_deadlock = false;
  bmc1_ucm = false;
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_ground_init = false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_aig_witness_out = false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;
  (*----BMC1 UCM --*)
  bmc1_ucm_expand_uc_limit = 128;
  bmc1_ucm_n_expand_iterations = 6;
  bmc1_ucm_extend_mode = 1;
  bmc1_ucm_init_mode = 2;
  bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_None;
  bmc1_ucm_reduced_relation_type = 0;
  bmc1_ucm_relax_model = 4; (* symbols/clear *)
  bmc1_ucm_full_tr_after_sat = true;
  bmc1_ucm_expand_neg_assumptions = false;
  bmc1_ucm_layered_model = BMC1_Ucm_Cone_Mode_None;
  (* lemmas *)
  bmc1_ucm_max_lemma_size = 10;


  (*----AIG----------------*)
  aig_mode = false;

  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [Lit_Num_of_Var true; Lit_Ground false; Lit_Atom_depth false];

  inst_lit_sel_side = CM_cnt;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 1.0; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 1400; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
     [Cl_Has_Eq_Lit false; Cl_Has_Conj_Symb true;  Cl_Num_of_Var false];
     [Cl_Has_Non_Prolific_Conj_Symb true;Cl_Num_of_Lits false; Cl_Conj_Dist false]
   ];
  inst_passive_queues_freq = [16;2];

  inst_dismatching = false;
  inst_eager_unprocessed_to_passive = true;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = false; 
  inst_prop_sim_new = true;
  inst_subs_given = false;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 100;
  inst_learning_factor = 8;
  inst_start_prop_sim_after_learn = 10;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = true;
  inst_restr_to_given = false;
  inst_activity_threshold = 1000;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_KBO_max;
  res_lit_sel_side = CM_none;
  res_ordering = Res_ord_kbo;
  res_to_prop_solver = Res_to_Solver_None;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
     [Cl_Has_Eq_Lit true; Cl_Num_of_Symb true; Cl_Horn false];
     [Cl_Max_Atom_Input_Occur false; Cl_Ground true; Cl_Has_Conj_Symb false]
   ];

  res_passive_queues_freq = [1024;2];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 0.1;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 100;
  comb_inst_mult = 1000;
}

(*-----------------------*)

let named_option_epr_non_horn_eq () =
  { options_name = "Option_epr_non_horn_eq";
  (*  options = (options_epr_non_horn_eq_samc_2018_06_28_16873 ()) *)
    options = (options_epr_non_horn_eq_samc_2018_06_28_15973 ()) 
  }

(*-------------Horn-----------------------*)

(* TPTP has only non eq epr horn *)
let option_epr_horn_non_eq_before_2018 () = { (* !current_options *)  input_options (* !!! changed !!!*) with 

  (*----General--------*)
  time_out_prep_mult = 0.1;
  splitting_mode = Split_Input;
  splitting_grd = false;
  splitting_cvd = false;
  splitting_cvd_svl = true;
  splitting_nvd = 128;
  non_eq_to_eq = false;
  prep_gs_sim = true;
  prep_unflatten = true;
  prep_res_sim = true;
  prep_upred   = true;
  res_sim_input = false;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
(*  prep_sem_filter = Sem_Filter_Exhaustive; *) (*commented 2017 *)
  prep_sem_filter_out = false;
  preprocessed_out = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  = false;
  add_important_lit = false;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = []; 
  conj_cone_tolerance = 1.5;

  abstr_ref = [];
(*  abstr_ref_arg_filter = false; *)

  (*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----BMC1---------------*)
   bmc1_symbol_reachability = true;
 
  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [Lit_Prop true; Lit_Ground false; Lit_has_non_prolific_conj_symb true; Lit_Sign true;]; 

  inst_lit_sel_side = CM_num_var;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 3.0; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 1400; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
      [ Cl_Num_of_Var false; Cl_Conj_Dist false; Cl_min_defined_symb true];
      [Cl_Age false; Cl_bc_imp_inh true]
    ];
  inst_passive_queues_freq = [100;1];

  inst_dismatching = false;
  inst_eager_unprocessed_to_passive = true;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = true; 
  inst_prop_sim_new = false;
  inst_subs_given = false;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 3000;
  inst_learning_factor = 4;
  inst_start_prop_sim_after_learn = 10;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = true;
  inst_restr_to_given = false;
  inst_activity_threshold = 10000;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_adaptive;
  res_lit_sel_side = CM_cnt;
  res_to_prop_solver = Res_to_Solver_Passive;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
      [ Cl_Num_of_Symb false;  Cl_Num_of_Lits true ];
      [Cl_Has_Conj_Symb true; Cl_Ground true;Cl_Age true]
    ];
  res_passive_queues_freq = [10;1];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = false;
  res_orphan_elimination = true;
  res_time_limit = 0.01;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 1000;
  comb_inst_mult = 10000;
}

let option_epr_horn_non_eq_smac_2018_06_10662 () = { (* !current_options *)  input_options (* !!! changed !!!*) with 

  (*----General--------*)
  time_out_prep_mult = 0.8;
  splitting_mode = Split_None;
  splitting_grd = false;
  splitting_cvd = false;
  splitting_cvd_svl = false;
  splitting_nvd = 128;
  non_eq_to_eq = false;
  prep_gs_sim = true;
  prep_unflatten = true;
  prep_res_sim = false;
  prep_upred   = true;
  res_sim_input = false;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  (*  prep_sem_filter         = Sem_Filter_None;*)
  prep_sem_filter = Sem_Filter_Exhaustive;  (*commented 2017 *)
  prep_sem_filter_out = false;
  preprocessed_out = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  = false;
  add_important_lit = false;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = []; 
  conj_cone_tolerance = 1.5;

  abstr_ref = [];


  (*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----BMC1---------------*)
   bmc1_symbol_reachability = true;
 
  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = 
         [Lit_has_non_prolific_conj_symb true; Lit_Prop true; Lit_Num_of_Symb false];

  inst_lit_sel_side = CM_num_symb;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 1.0; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 100; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
   [
    [Cl_Ground true; Cl_Num_of_Symb true; Cl_min_defined_symb true];
    [Cl_Num_of_Lits false; Cl_Age true; Cl_Has_Non_Prolific_Conj_Symb true]
  ];
  inst_passive_queues_freq = [1000;5];

  inst_dismatching = false;
  inst_eager_unprocessed_to_passive = false;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = false; 
  inst_prop_sim_new = true;
  inst_subs_given = false; (* true; *)
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = false;
  inst_learning_loop_flag = true;
  inst_learning_start = 3000;
  inst_learning_factor = 4;
  inst_start_prop_sim_after_learn = 0;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = true;
  inst_restr_to_given = true;
  inst_activity_threshold = 10000;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_neg_sel_min;
  res_lit_sel_side = CM_none;
  res_to_prop_solver =  Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
 
  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Non_Prolific_Conj_Symb true; Cl_Num_of_Symb false;  Cl_Num_of_Symb false ];
      [Cl_Age true; Cl_Num_of_Symb false];
    ]; (* 2016*)
 (*
    [
     [Cl_Age false; Cl_Max_Atom_Input_Occur true; Cl_Num_of_Lits true];
     [Cl_Conj_Dist true; Cl_Age false; Cl_Has_Non_Prolific_Conj_Symb false];
   ];
*)
  res_passive_queues_freq = [10;5];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;(* Subs_Full; *)
  res_forward_subs_resolution = (* true; *) false;
  res_backward_subs_resolution = false;
  res_orphan_elimination = true;
  res_time_limit = 2.;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 1000; (* 100; *)
  comb_inst_mult = 300; (* 1000; *)
}



(* CASC 2016
let option_epr_horn () = { (* !current_options*) input_options with

  (*----General--------*)

  fix_init_inter = None;
  time_out_real = -1.;
  time_out_virtual = -1.;
  non_eq_to_eq = false;
  clausify_out = false;

  large_theory_mode = true;
  prep_sem_filter_out = false;
  brand_transform = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep = false;
  sat_fm_uc_incr = false;	

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;

  (*----------------------Instantiation------*)
  instantiation_flag = true;
  (*------------------------------------------*)

  inst_lit_sel = [Lit_Prop true; Lit_Sign true; Lit_Ground true; Lit_Num_of_Var false; Lit_Num_of_Symb false];

(*
  inst_solver_per_active = 750;
  inst_solver_per_clauses = 5000;
*)

  inst_passive_queue_type = !current_options.inst_passive_queue_type;
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;5];

  inst_dismatching = true;
  (*  inst_dismatching               =  !current_options.inst_dismatching;*)

  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Solver;
  inst_lit_activity_flag = true;
(*
  inst_out_proof = ValueDefault true;
*)
  (*----Resolution----------------------------*)
  resolution_flag = true;
  (*------------------------------------------*)
  res_lit_sel = Res_neg_sel_min;
  (*  res_lit_sel                    = Res_Adaptive;*)
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = !current_options.res_passive_queue_type;
  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = false;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 2.;
  (*----Combination--------*)
  comb_res_mult = 1000;
  comb_inst_mult = 300;

}
*)
(*

(* Options for CASC 2009 *)

  let option_epr_horn () = {

  out_options = !current_options.out_options;
  tptp_safe_out = !current_options.tptp_safe_out;

(*----Input-------*)
  problem_path = !current_options.problem_path;
  include_path = !current_options.include_path;
  problem_files = !current_options.problem_files;
  eprover_path = !current_options.eprover_path;
  stdin = !current_options.stdin;

(*----General--------*)
  fix_init_inter = None;
  time_out_real = -1.;
  time_out_virtual = -1.;
  schedule = !current_options.schedule;

  splitting_mode = Split_Input;
  non_eq_to_eq = false;
  prep_gs_sim = true;
  prep_unflatten = !current_options.prep_unflatten;
  symbol_type_check = !current_options.symbol_type_check;
  clausify_out = false;

  large_theory_mode = true;
  prep_sem_filter = !current_options.prep_sem_filter;
  prep_sem_filter_out = false;
  prolific_symb_bound = 500;
  lt_threshold = 2000;

(*----Sat Mode--------*)
  sat_mode = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_out_model = !current_options.sat_out_model;

(*----------------------Instantiation------*)
  instantiation_flag = false;
(*------------------------------------------*)

  inst_lit_sel = [Lit_Sign false; Lit_Ground true;];

  inst_solver_per_active = 750;
  inst_solver_per_clauses = 5000;
  inst_pass_queue1 = [Cl_Conj_Dist false;
  Cl_Has_Conj_Symb true;
  Cl_Ground true;
  Cl_Num_of_Var false];
  inst_pass_queue2 = [Cl_Age true; Cl_Num_of_Symb false];

(*"[+age;-num_symb]";*)
  inst_pass_queue1_mult = 25;
  inst_pass_queue2_mult = 20;

  inst_dismatching = false;
(*  inst_dismatching               =  !current_options.inst_dismatching;*)

  inst_eager_unprocessed_to_passive = true;
  inst_prop_sim_given = false;
  inst_prop_sim_new = false;
  inst_learning_loop_flag = true;
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 300;
  inst_sel_renew = Inst_SR_Solver;
  inst_lit_activity_flag = true;

(*----Resolution----------------------------*)
  resolution_flag = true;
(*------------------------------------------*)
  res_lit_sel = Res_Neg_Sel_Min;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
(*switch between simpl and priority queues*)
(* TO DO  Queues options like in Inst. *)
(*-----------------------------*)
  res_passive_queue_flag = false;
(*-----------------------------*)
  res_pass_queue1 = [Cl_Has_Conj_Symb true; ];
  res_pass_queue2 = [Cl_Age true; Cl_Num_of_Symb false];
  res_pass_queue1_mult = 15;
  res_pass_queue2_mult = 10;

  res_forward_subs = Subs_Subset;
  res_backward_subs = Subs_Subset;
  res_forward_subs_resolution = false;
  res_backward_subs_resolution = false;
  res_orphan_elimination = false;
  res_time_limit = 200000000000.0;
  res_out_proof = false;
(*----Combination--------*)
  comb_res_mult = 300000000;
  comb_inst_mult = 1;
  }

 *)

let named_option_epr_horn_non_eq () =
  { options_name = "Option_epr_horn"; options = (option_epr_horn_non_eq_smac_2018_06_10662 ()) }

(*-----------------------------------------------*)

type ver_epr_opt =
  | Ver_EPR_TABLES_BOUND_3 (* proves rat example bound 3 *)
  | Ver_EPR_TABLES
  | Ver_EPR_Default
  | Ver_EPR_DCU
  | Ver_EPR
  | Planning_EPR

(* *)
let option_verification_epr ver_epr_opt =

  match ver_epr_opt with
  | Ver_EPR_TABLES_BOUND_3 ->
      { !current_options with
       (*----General--------*)
       fix_init_inter = None;
       non_eq_to_eq = false;
       clausify_out = false;

       large_theory_mode = false;
       prep_sem_filter_out = false;
       (*  sub_typing              = !current_options.sub_typing;*)
       sub_typing = false;
       brand_transform = false;
       prolific_symb_bound = 5000;
       lt_threshold = 2000;

       (*----Sat Mode--------*)
       sat_mode = false;
       sat_gr_def = false;
       sat_finite_models = false;
       sat_fm_lemmas = false;
       sat_fm_prep = false;
       sat_fm_uc_incr = false;	

       (*----BMC1---------------*)
       bmc1_incremental = ValueDefault true;
       bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
       bmc1_min_bound = ValueDefault 0;
       bmc1_max_bound = ValueDefault (-1);
       bmc1_max_bound_default = ValueDefault (-1);
       bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_Leaves;
       bmc1_unsat_core_children = ValueDefault false;
       bmc1_unsat_core_extrapolate_axioms = ValueDefault true;
       bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
       bmc1_pre_inst_next_state = false;
       bmc1_pre_inst_state = false;
       bmc1_pre_inst_reach_state = false;
       bmc1_out_unsat_core = ValueDefault false;
       bmc1_verbose = ValueDefault false;
       bmc1_dump_clauses_tptp = ValueDefault false;
       bmc1_dump_unsat_core_tptp = ValueDefault false;
       bmc1_dump_file = ValueDefault None;

       (*----Instantiation------*)
       instantiation_flag = true;
       inst_lit_sel = [Lit_Prop true; Lit_Ground true; Lit_Sign false;];

       (* before Intel example bpbimodalm_miter_full.focnf.bit_blast.Mclk1 *)
       (* inst_solver_per_active         = 750; after 7500 *)
       (*  inst_solver_per_active         = 750;*)
       (*  inst_solver_per_active         = 7500;*)
(*
       inst_solver_per_active = 7500;
*)
       (* inst_solver_per_clauses        = 5000; is ok*)
       (*  inst_solver_per_clauses        = 5000;*)


        inst_passive_queues =
          [
            [Cl_in_unsat_core true; Cl_Age true; Cl_Num_of_Symb false];
            [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        inst_passive_queues_freq = [20;25;20];

       (* befor ok inst_dismatching               = false;*)
       inst_dismatching = false;
       (*  inst_dismatching               =  !current_options.inst_dismatching;*)

       inst_eager_unprocessed_to_passive = true;
       inst_prop_sim_given = false;
       inst_prop_sim_new = false;
       inst_learning_loop_flag = true;
       inst_learning_start = 3000;
       inst_learning_factor = 2;
       inst_start_prop_sim_after_learn = 3000;
       inst_sel_renew = Inst_SR_Solver;
       inst_lit_activity_flag = false;
(*  
     inst_out_proof = ValueDefault true;
*)
       (*----Resolution----------------------------*)
       resolution_flag = false;
       (*------------------------------------------*)
       res_lit_sel = Res_adaptive;
       res_to_prop_solver = Res_to_Solver_Active;
       res_prop_simpl_new = false;
       res_prop_simpl_given = false;
        res_passive_queue_type = !current_options.res_passive_queue_type;
        res_passive_queues =
          [
            [Cl_Has_Conj_Symb true];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        res_passive_queues_freq = [15;10];

       res_forward_subs = Subs_Subset;
       res_backward_subs = Subs_Subset;
       res_forward_subs_resolution = false;
       res_backward_subs_resolution = false;
       res_orphan_elimination = false;
       res_time_limit = 2.0;
       (*----Combination--------*)
       comb_res_mult = 30;
       comb_inst_mult = 1000;
     }

  | Ver_EPR_TABLES | Ver_EPR_Default ->
      { !current_options with
       (*----General--------*)
       fix_init_inter = None;
       splitting_mode = Split_None;
       non_eq_to_eq = false;
       clausify_out = false;

       large_theory_mode = false;
       prep_sem_filter_out = false;
       (*  sub_typing              = !current_options.sub_typing;*)
       sub_typing = false;
       brand_transform = false;
       prolific_symb_bound = 20000000;
       lt_threshold = 20000000;

       (*----Sat Mode--------*)
       sat_mode = false;
       sat_gr_def = false;
       sat_finite_models = false;
       sat_fm_lemmas = false;
       sat_fm_prep = false;
       sat_fm_uc_incr = false;	

       (*----BMC1---------------*)
       bmc1_incremental = ValueDefault true;
       bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
       bmc1_min_bound = ValueDefault 0;
       bmc1_max_bound = ValueDefault (-1);
       bmc1_max_bound_default = ValueDefault (-1);
       bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_Leaves;
       bmc1_unsat_core_children = ValueDefault false;
       bmc1_unsat_core_extrapolate_axioms = ValueDefault true;
       bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
       bmc1_pre_inst_next_state = false;
       bmc1_pre_inst_state = false;
       bmc1_pre_inst_reach_state = false;
       bmc1_out_unsat_core = ValueDefault false;
       bmc1_verbose = ValueDefault false;
       bmc1_dump_clauses_tptp = ValueDefault false;
       bmc1_dump_unsat_core_tptp = ValueDefault false;
       bmc1_dump_file = ValueDefault None;

       (*----Instantiation------*)
       instantiation_flag = true;
       inst_lit_sel = [Lit_Prop true; Lit_eq false; Lit_Ground true; Lit_Sign false;];

       (* before Intel example bpbimodalm_miter_full.focnf.bit_blast.Mclk1 *)
       (* inst_solver_per_active         = 750; after 7500 *)
       (*  inst_solver_per_active         = 750;*)
       (*  inst_solver_per_active         = 7500;*)


       (* inst_solver_per_clauses        = 5000; is ok*)
       (* inst_solver_per_clauses        = 5000;*)

        inst_passive_queues =
          [
            [Cl_in_unsat_core true; Cl_Age true; Cl_Num_of_Symb false];
            [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        inst_passive_queues_freq = [20;25;20];

       (* befor ok inst_dismatching               = false;*)
       inst_dismatching = false;
       (*  inst_dismatching               =  !current_options.inst_dismatching;*)

       inst_eager_unprocessed_to_passive = true;
       inst_prop_sim_given = false;
       inst_prop_sim_new = false;
       inst_learning_loop_flag = true;
       (* inst_learning_start               = 1000;*)
       inst_learning_start = 100000;
       inst_learning_factor = 10;
       inst_start_prop_sim_after_learn = 300000000;
       inst_sel_renew = Inst_SR_Solver;
       inst_lit_activity_flag = false;
       inst_out_proof = ValueDefault true;

       (*----Resolution----------------------------*)
       resolution_flag = false;
       (*------------------------------------------*)
       res_lit_sel = Res_adaptive;
       res_to_prop_solver = Res_to_Solver_Active;
       res_prop_simpl_new = false;
       res_prop_simpl_given = false;
        res_passive_queue_type = !current_options.res_passive_queue_type;
        res_passive_queues =
          [
            [Cl_Has_Conj_Symb true];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        res_passive_queues_freq = [15;10];

       res_forward_subs = Subs_Subset;
       res_backward_subs = Subs_Subset;
       res_forward_subs_resolution = false;
       res_backward_subs_resolution = false;
       res_orphan_elimination = false;
       res_time_limit = 2.0;
       (*----Combination--------*)
       comb_res_mult = 30;
       comb_inst_mult = 10000;
     }
  | Ver_EPR_DCU ->
      { !current_options with
       (*------------------------------------*)
       (* all general options are take from  !current_options anyway since *)
       (* schedule becomes effective only during proof search not during preprocessing  *)
       (* in particular sub_typing false should be added to the input option for bmc1 *)
       (*----General--------*)
       fix_init_inter = None;

       splitting_mode = Split_Input;
       non_eq_to_eq = false;
       clausify_out = false;

       large_theory_mode = false;
       (* prep_sem_filter         = !current_options.prep_sem_filter;  does not work correctly with bmc*)
       prep_sem_filter = Sem_Filter_None;
       prep_sem_filter_out = false;
       (*       sub_typing              = !current_options.sub_typing;*)
       sub_typing = false;
       brand_transform = false;
       prolific_symb_bound = 5000;
       lt_threshold = 2000;

       (*----Sat Mode--------*)
       sat_mode = false;
       sat_gr_def = false;
       sat_finite_models = false;
       sat_fm_lemmas = false;
       sat_fm_prep = false;
       sat_fm_uc_incr = false;	

       (*----BMC1---------------*)
       bmc1_incremental = ValueDefault true;
       bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
       bmc1_min_bound = ValueDefault 0;
       bmc1_max_bound = ValueDefault (-1);
       bmc1_max_bound_default = ValueDefault (-1);
       (*  bmc1_symbol_reachability should always be taken from !current_options.bmc1_symbol_reachability *)
       bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_Leaves;
       bmc1_unsat_core_children = ValueDefault false;
       bmc1_unsat_core_extrapolate_axioms = ValueDefault true;
       bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
       bmc1_out_unsat_core = ValueDefault false;
       bmc1_verbose = ValueDefault false;
       bmc1_dump_clauses_tptp = ValueDefault false;
       bmc1_dump_unsat_core_tptp = ValueDefault false;
       bmc1_dump_file = ValueDefault None;

       (*----Instantiation------*)
       instantiation_flag = true;

       (*
	 inst_lit_sel = [Lit_Ground true; Lit_Sign false;];
	*)
       (* usual *)
       inst_lit_sel =
       [
        Lit_Prop true;
	Lit_clock true;
	(* Lit_reachable_state true;
	   Lit_next_state true;*)
	Lit_Ground true;
	Lit_Sign false; ];

       (*
	 inst_lit_sel =
	 [
	 Lit_next_state false;
	 Lit_clock true;
	 (* Lit_reachable_state true;
	    Lit_next_state true;*)
	 Lit_Ground true;
	 Lit_Sign false; ];
	*)

       (*     inst_lit_sel                   = [Lit_Sign false;];*)
       (* before Intel example bpbimodalm_miter_full.focnf.bit_blast.Mclk1 *)
       (* inst_solver_per_active         = 750; after 7500 *)
       (*  inst_solver_per_active         = 750;*)
       (*  inst_solver_per_active         = 7500;*)

       (*       inst_solver_per_active         = 25000;*)
(*       inst_solver_per_active = 25000; *)

       (* inst_solver_per_clauses        = 5000; is ok*)
       (*  inst_solver_per_clauses        = 5000;*)
(*       inst_solver_per_clauses = !current_options.inst_solver_per_clauses; *)

        inst_passive_queue_type = !current_options.inst_passive_queue_type;
        inst_passive_queues =
          [
            [Cl_in_unsat_core true; Cl_min_defined_symb false; Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false];
            [Cl_Conj_Dist false; Cl_Has_Eq_Lit false; Cl_has_bound_constant true; Cl_Num_of_Var false];
            [Cl_Age true; Cl_min_defined_symb false; Cl_Num_of_Symb false]
          ];
        inst_passive_queues_freq = [20;25;20];

       (* befor ok inst_dismatching               = false;*)
       (*       inst_dismatching               = false;*)
       inst_dismatching = true;
       (*  inst_dismatching               =  !current_options.inst_dismatching;*)

       inst_eager_unprocessed_to_passive = true;

       (*    inst_prop_sim_given               = !current_options.inst_prop_sim_given; (*change to false*) *)
       inst_prop_sim_given = false;

       inst_prop_sim_new = false;
       inst_orphan_elimination = !current_options.inst_orphan_elimination;
       (*     inst_prop_sim_new                 = true;*)
       inst_learning_loop_flag = true;
       (*       inst_learning_loop_flag           = false; *)
       inst_learning_start = 30000;
       inst_learning_factor = 3;
       inst_start_prop_sim_after_learn = 0;
       inst_sel_renew = Inst_SR_Solver;
       inst_lit_activity_flag = false;
       (*    inst_lit_activity_flag            = true;*)
       inst_out_proof = ValueDefault true;

       (*----Resolution----------------------------*)
       resolution_flag = false;
       (*------------------------------------------*)
       res_lit_sel = Res_adaptive;
       res_to_prop_solver = Res_to_Solver_Active;
       res_prop_simpl_new = false;
       res_prop_simpl_given = false;
        res_passive_queue_type = !current_options.res_passive_queue_type;
        res_passive_queues =
          [
            [Cl_Has_Conj_Symb true];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        res_passive_queues_freq = [15;10];

       res_forward_subs = Subs_Subset;
       res_backward_subs = Subs_Subset;
       res_forward_subs_resolution = false;
       res_backward_subs_resolution = false;
       res_orphan_elimination = false;
       res_time_limit = 2.0;
       res_out_proof = !current_options.res_out_proof;
       (*----Combination--------*)
       comb_res_mult = 30;
       comb_inst_mult = 1000;
     }
  | Ver_EPR ->
      (out_warning "Split_Full; UCM is not yet compatible use --bmc1_ucm true");

      { !current_options with
       (*------------------------------------*)
       (* all general options are take from  !current_options anyway since *)
       (* schedule becomes effective only during proof search not during preprocessing  *)
       (* in particular sub_typing false should be added to the input option for bmc1 *)

       (*----General--------*)
       fix_init_inter = None;
       splitting_mode = !current_options.splitting_mode; (* Split_Input; *) (* Split_Full; *)  (* KK changed in 27 Sep 2015 *)
       non_eq_to_eq = false;
       clausify_out = false;

       large_theory_mode = false;
       (* prep_sem_filter         = !current_options.prep_sem_filter;  does not work correctly with bmc*)
(*       prep_sem_filter = Sem_Filter_None; *)
       prep_sem_filter_out = false;
       sub_typing = false;
       brand_transform = false;
       prolific_symb_bound = 5000;
       lt_threshold = 2000;
(*	bc_imp_inh = [BCI_conj_cone];  gets from the !current_options since used in preprocessing before this options iis active *)
       (*----Sat Mode--------*)
       sat_mode = false;
       sat_gr_def = false;
       sat_finite_models = false;
       sat_fm_lemmas = false;
       sat_fm_prep = false;
       sat_fm_uc_incr = false;

       (*----BMC1---------------*)
       bmc1_incremental = ValueDefault true;
       bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
       bmc1_min_bound = ValueDefault 0;
       bmc1_max_bound = ValueDefault (-1);
       bmc1_max_bound_default = ValueDefault (-1);
       (*  bmc1_symbol_reachability should always be taken from !current_options.bmc1_symbol_reachability *)
       bmc1_unsat_core_children = ValueDefault false;
       bmc1_unsat_core_extrapolate_axioms = ValueDefault true;
       bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
       bmc1_out_unsat_core = ValueDefault false;
       bmc1_aig_witness_out = true;
       bmc1_verbose = ValueDefault false;
       bmc1_dump_clauses_tptp = ValueDefault false;
       bmc1_dump_unsat_core_tptp = ValueDefault false;
       bmc1_dump_file = ValueDefault None;

       (*----Instantiation------*)
       instantiation_flag = true;

       (* usual *)
       inst_lit_sel =
       [
        Lit_Prop true;
(*        Lit_Split true;
        Lit_Num_of_Var true;
*)
        Lit_Ground true; 
        (* Lit_next_state true; *)
        Lit_Sign false;
       ];

      inst_solver_calls_frac = 0.2;
      inst_solver_per_active = 25000;
(*
       inst_solver_per_active    = 10000; (* 25000; was *)
       inst_solver_per_clauses   = 5000; (* was 5000 *) 
*)
       (* inst_solver_per_clauses = !current_options.inst_solver_per_clauses;*)

        inst_passive_queue_type = !current_options.inst_passive_queue_type;
        inst_passive_queues =
          [
(*KK*)

	   [Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false]; 
(*         [Cl_in_unsat_core true; Cl_min_defined_symb false; Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false]; *)
	   [Cl_Num_of_Var false; Cl_Num_of_Symb false];

(*           [Cl_has_bound_constant true; Cl_Conj_Dist false; Cl_Num_of_Var false]; *)
           [Cl_Age true; Cl_Num_of_Var false]; 

          ];
        inst_passive_queues_freq = [20;25;20];
    (*    inst_passive_queues_freq = [20;25;20];*)

       inst_dismatching = true;
       inst_eager_unprocessed_to_passive = true;
      inst_prop_sim_given =  false;  
       inst_prop_sim_new = false;
       inst_learning_loop_flag = (* false; *)  true;
       inst_learning_start = 30000; 
       inst_learning_factor = 3;
       inst_start_prop_sim_after_learn = 0;
       inst_sel_renew =  Inst_SR_Solver; (* Inst_SR_Solver; *)


       inst_lit_activity_flag = false;

(*       inst_lit_activity_flag = !current_options.inst_lit_activity_flag; *)
 
        (* TODO: add proof at the end of k-induction !! *)
       inst_out_proof = ValueDefault true;

       (*----Resolution----------------------------*)
       resolution_flag = false;
       (*------------------------------------------*)
       res_lit_sel = Res_adaptive;
       res_to_prop_solver = Res_to_Solver_Active;
       res_prop_simpl_new = false;
       res_prop_simpl_given = false;

        res_passive_queue_type = !current_options.res_passive_queue_type;
        res_passive_queues =
          [
            [Cl_Has_Conj_Symb true];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        res_passive_queues_freq = [15;10];

       res_forward_subs = Subs_Subset;
       res_backward_subs = Subs_Subset;
       res_forward_subs_resolution = false;
       res_backward_subs_resolution = false;
       res_orphan_elimination = false;
       res_time_limit = 2.0;
       (*----Combination--------*)
       comb_res_mult = 30;
       comb_inst_mult = 1000;
     }

 | Planning_EPR ->
      (out_warning "Split_Full; UMC is not yet compatible use --bmc1_ucm false");

      { !current_options with
       (*------------------------------------*)
       (* all general options are take from  !current_options anyway since *)
       (* schedule becomes effective only during proof search not during preprocessing  *)
       (* in particular sub_typing false should be added to the input option for bmc1 *)

       (*----General--------*)
       fix_init_inter = None;
       splitting_mode = !current_options.splitting_mode; (* Split_Input; *) (* Split_Full; *)  (* KK changed in 27 Sep 2015 *)
       non_eq_to_eq = false;
       clausify_out = false;

       large_theory_mode = false;
       (* prep_sem_filter         = !current_options.prep_sem_filter;  does not work correctly with bmc*)
(*       prep_sem_filter = Sem_Filter_None; *)
       prep_sem_filter_out = false;
       sub_typing = false;
       brand_transform = false;
       prolific_symb_bound = 5000;
       lt_threshold = 2000;
(*	bc_imp_inh = [BCI_conj_cone];  gets from the !current_options since used in preprocessing before this options iis active *)
       (*----Sat Mode--------*)
       sat_mode = false;
       sat_gr_def = false;
       sat_finite_models = false;
       sat_fm_lemmas = false;
       sat_fm_prep = false;
       sat_fm_uc_incr = false;

       (*----BMC1---------------*)
       bmc1_incremental = ValueDefault true;
       bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
       bmc1_min_bound = ValueDefault 0;
       bmc1_max_bound = ValueDefault (-1);
       bmc1_max_bound_default = ValueDefault (-1);
       (*  bmc1_symbol_reachability should always be taken from !current_options.bmc1_symbol_reachability *)
       bmc1_unsat_core_children = ValueDefault false;
       bmc1_unsat_core_extrapolate_axioms = ValueDefault true;
       bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
       bmc1_out_unsat_core = ValueDefault false;
       bmc1_aig_witness_out = true;
       bmc1_verbose = ValueDefault false;
       bmc1_dump_clauses_tptp = ValueDefault false;
       bmc1_dump_unsat_core_tptp = ValueDefault false;
       bmc1_dump_file = ValueDefault None;

       (*----Instantiation------*)
       instantiation_flag = true;

       (* usual *)
       inst_lit_sel =
       [
        Lit_Prop true;
        Lit_Ground (*false; *)  true; 
        (* Lit_next_state true; *)
        Lit_Sign false; 
(*        Lit_Sign true; *)
       ];

      inst_solver_calls_frac = 0.2;
      inst_solver_per_active = 25000;
(*
       inst_solver_per_active    = 10000; (* 25000; was *)
       inst_solver_per_clauses   = 5000; (* was 5000 *) 
*)
       (* inst_solver_per_clauses = !current_options.inst_solver_per_clauses;*)

        inst_passive_queue_type = !current_options.inst_passive_queue_type;
        inst_passive_queues =
          [

(* 2015 *)
	   [Cl_in_unsat_core true; Cl_min_defined_symb false;  Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false]; 
(*          [Cl_in_unsat_core true; Cl_min_defined_symb false; Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false]; *)
	   [Cl_bc_imp_inh true; Cl_Num_of_Symb false];

(*           [Cl_has_bound_constant true; Cl_Conj_Dist false; Cl_Num_of_Var false]; *)
           [Cl_Age true;    Cl_min_defined_symb false; Cl_Num_of_Symb false]; 


(*KK 2017 not good *)

(*
	   [Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false]; 
(*         [Cl_in_unsat_core true; Cl_min_defined_symb false; Cl_Conj_Dist false; Cl_Age true; Cl_Num_of_Symb false]; *)
	   [Cl_Num_of_Var false; Cl_Num_of_Symb false];

(*           [Cl_has_bound_constant true; Cl_Conj_Dist false; Cl_Num_of_Var false]; *)
           [Cl_Age true; Cl_Num_of_Var false]; 
*)
          ];
        inst_passive_queues_freq = [20;25;20];
    (*    inst_passive_queues_freq = [20;25;20];*)

       inst_dismatching = true;
       inst_eager_unprocessed_to_passive = true;
      inst_prop_sim_given =  false;  
       inst_prop_sim_new = false;
       inst_learning_loop_flag = false; (* true;*)
       inst_learning_start = 30000; 
       inst_learning_factor = 3;
       inst_start_prop_sim_after_learn = 0;
       inst_sel_renew =  Inst_SR_Solver; (* Inst_SR_Solver;*) (* Inst_SR_Solver; *)


       inst_lit_activity_flag =   true; (*  false;  *)

(*       inst_lit_activity_flag = !current_options.inst_lit_activity_flag; *)
 
        (* TODO: add proof at the end of k-induction !! *)
       inst_out_proof = ValueDefault false; (* true; *)

       (*----Resolution----------------------------*)
       resolution_flag = false;
       (*------------------------------------------*)
       res_lit_sel = Res_adaptive;
       res_to_prop_solver = Res_to_Solver_Active;
       res_prop_simpl_new = false;
       res_prop_simpl_given = false;

        res_passive_queue_type = !current_options.res_passive_queue_type;
        res_passive_queues =
          [
            [Cl_Has_Conj_Symb true];
            [Cl_Age true; Cl_Num_of_Symb false]
          ];
        res_passive_queues_freq = [15;10];

       res_forward_subs = Subs_Subset;
       res_backward_subs = Subs_Subset;
       res_forward_subs_resolution = false;
       res_backward_subs_resolution = false;
       res_orphan_elimination = false;
       res_time_limit = 2.0;
       (*----Combination--------*)
       comb_res_mult = 30;
       comb_inst_mult = 1000;
     }

let named_option_verification_epr_old () =
  { options_name = "Option_verification_epr_old";
    (*   options = (option_verification_epr Ver_EPR_TABLES_BOUND_3)*)
    options = (option_verification_epr Ver_EPR_DCU)
      (*was Ver_EPR_DCU when in June 8th 2012*)
      (*  options = (option_verification_epr Ver_EPR_Default)*)
  }

let named_option_verification_epr_tables () =
  { options_name = "Option_verification_epr_tables";
    options = (option_verification_epr Ver_EPR_TABLES) }

let named_option_verification_epr () =
  { 
    options_name = "Option_verification_epr";
    options = (option_verification_epr Ver_EPR)
(*
    options_name = "Option_planning_epr"; 
    options = (option_verification_epr Planning_EPR)
*)
  }


(*---------------- smac tmp -----------------*)
(*-- Currently NOT in USE; temporal set of opetions used as default in the current smac experiment -----*)

let smac_tmp_options () = !current_options

(* {

  out_options = ValueDefault Out_All_Opt;
  tptp_safe_out = false;

  (*----Input-------*)
  problem_path = "";
  include_path = "";
  problem_files = [];
  clausifier = "";
  clausifier_options = "";
  stdin = false;
  dbg_backtrace = false;
  dbg_dump_prop_clauses = false;
  dbg_dump_prop_clauses_file = "-";
  dbg_out_stat = false;

  (*----General--------*)
  fix_init_inter = None;
  time_out_real = -1.;
  time_out_prep_mult = 0.2;
  time_out_virtual = -1.;
  schedule = Schedule_default;
  splitting_mode = Split_Input;
  splitting_grd = false;
  splitting_cvd = true;
  splitting_cvd_svl = true;
  splitting_nvd = 16;
  non_eq_to_eq = false;
  prep_gs_sim = true;
  prep_unflatten = true;
  prep_res_sim = true;
  prep_upred   = true;
  res_sim_input = true;
  clause_weak_htbl = true;
  gc_record_bc_elim = false;
  symbol_type_check = false;
  clausify_out = false;
  prep_sem_filter = Sem_Filter_Exhaustive;
  prep_sem_filter_out = false;
  preprocessed_out = false;
  sub_typing          = true;
  eq_ax_congr_red     = true;
  brand_transform = false;
  pure_diseq_elim = true;
  min_unsat_core = false;
  pred_elim  =  true;
  add_important_lit = false;
  soft_assumptions = false;
  soft_lemma_size = 3;
  prop_impl_unit_size = 20;
  prop_impl_unit = [Lit_bp_epr(true)];
  share_sel_clauses = true;

  reset_solvers = false;
(*  bc_imp_inh = [BCI_bmc1_lemma;BCI_conj_cone]; *)(* [BCI_conj_cone];*)
  bc_imp_inh = []; 
  conj_cone_tolerance = 1.5;
  extra_neg_conj = ENC_none;

  abstr_ref_arg_filter = false;
  abstr_ref_sig = false;
  abstr_ref_prep = false;
  abstr_ref_until_sat = false;
  abstr_terms_sig = false;
  abstr_skolem_sig = false;

  prep_def_merge = true;
  prep_def_merge_prop_impl = true;
  prep_def_merge_mbd = true;
  
(*---Large Theories---------------*)
  large_theory_mode = true;

  prolific_symb_bound = 500;
  lt_threshold = 2000;

  (*---Sat mode------------*)
  sat_mode = false;
  sat_fm_restart_options = "";
  sat_epr_types = true;
  sat_non_cyclic_types = false;
  sat_gr_def = false;
  sat_finite_models = false;
  sat_fm_lemmas = false;
  sat_fm_prep   = false;
(*  sat_fm_uc_incr = false; *)
  sat_fm_uc_incr = true; 
  sat_out_model = Model_Small;
  sat_out_clauses = false;

(*---QBF mode------------*)
  qbf_mode = false;
  qbf_elim_univ = true;
  qbf_sk_in = true;
  qbf_pred_elim = true;
  qbf_split = 32;

  (*----BMC1---------------*)
  bmc1_incremental = ValueDefault false;
  bmc1_axioms = ValueDefault BMC1_Axioms_Reachable_All;
  bmc1_min_bound = ValueDefault 0;
  bmc1_max_bound = ValueDefault (-1);
  bmc1_max_bound_default = ValueDefault (-1);
  (*bmc1_symbol_reachability should be modified only by input options and not by options in schedule since it is calculated before options in schedule become active *)
  bmc1_symbol_reachability = true;
  bmc1_property_lemmas = false;
  bmc1_k_induction = false;
  bmc1_non_equiv_states = false;
  bmc1_deadlock = false;
  bmc1_ucm = false;
  bmc1_add_unsat_core = ValueDefault BMC1_Add_Unsat_Core_None;
  bmc1_unsat_core_children = ValueDefault false;
  bmc1_unsat_core_extrapolate_axioms = ValueDefault false;
  bmc1_ground_init = false;
  bmc1_pre_inst_next_state = false;
  bmc1_pre_inst_state = false;
  bmc1_pre_inst_reach_state = false;
  bmc1_out_stat = ValueDefault BMC1_Out_Stat_Full;
  bmc1_out_unsat_core = ValueDefault false;
  bmc1_aig_witness_out = false;
  bmc1_verbose = ValueDefault false;
  bmc1_dump_clauses_tptp = ValueDefault false;
  bmc1_dump_unsat_core_tptp = ValueDefault false;
  bmc1_dump_file = ValueDefault None;
  (*----BMC1 UCM --*)
  bmc1_ucm_expand_uc_limit = 128;
  bmc1_ucm_n_expand_iterations = 6;
  bmc1_ucm_extend_mode = 1;
  bmc1_ucm_init_mode = 2;
  bmc1_ucm_cone_mode = BMC1_Ucm_Cone_Mode_None;
  bmc1_ucm_reduced_relation_type = 0;
  bmc1_ucm_relax_model = 4; (* symbols/clear *)
  bmc1_ucm_full_tr_after_sat = true;
  bmc1_ucm_expand_neg_assumptions = false;
  bmc1_ucm_layered_model = BMC1_Ucm_Cone_Mode_None;
  (* lemmas *)
  bmc1_ucm_max_lemma_size = 10;


  (*----AIG----------------*)
  aig_mode = false;

  (*----Instantiation------*)
  instantiation_flag = true;
(*
  inst_lit_sel = [Lit_Num_of_Symb true; Lit_Num_of_Var true; Lit_Sign false; ];
*)

  inst_lit_sel = [Lit_Prop true; Lit_Sign true; Lit_Ground true;
		  Lit_Num_of_Var false; Lit_Num_of_Symb false]; (*  CASC 2015*)

  inst_lit_sel_side = CM_num_symb;

(*  inst_solver_calls_frac = 0.5; *)
  inst_solver_calls_frac = 1.0; 

(*  inst_solver_per_active = 750; *)
  inst_solver_per_active = 1400; 
(*  inst_solver_per_clauses = 5000;
*)
  inst_passive_queue_type = PQT_PriorityQueues;
  inst_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Var false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  inst_passive_queues_freq = [25;2];

  inst_dismatching = true;
  inst_eager_unprocessed_to_passive = true;
(*  inst_prop_sim_given = false; *)
(*  inst_prop_sim_new = true; *)
  inst_prop_sim_given = true; 
  inst_prop_sim_new = false;
  inst_subs_given = false;
  inst_subs_new = false;   
  inst_eq_res_simp = false;
  inst_orphan_elimination = true;
  inst_learning_loop_flag = true;
  inst_learning_start = 3000;
  inst_learning_factor = 2;
  inst_start_prop_sim_after_learn = 3;
  inst_sel_renew = Inst_SR_Solver; (* Inst_SR_Model; *)
  inst_lit_activity_flag = true;
  inst_restr_to_given = false;
  inst_activity_threshold = 500;
  inst_out_proof = ValueDefault true;

  (*----Resolution---------*)
  resolution_flag = true;
  res_lit_sel = Res_adaptive;
  res_lit_sel_side = CM_none;
  res_ordering = Res_ord_kbo;
  res_to_prop_solver = Res_to_Solver_Active;
  res_prop_simpl_new = false;
  res_prop_simpl_given = true;
  res_passive_queue_type = PQT_PriorityQueues;
  res_passive_queues =
    [
      [Cl_Conj_Dist false; Cl_Has_Conj_Symb true; Cl_Num_of_Symb false];
      [Cl_Age true; Cl_Num_of_Symb false]
    ];
  res_passive_queues_freq = [15;5];

  res_forward_subs = Subs_Full;
  res_backward_subs = Subs_Full;
  res_forward_subs_resolution = true;
  res_backward_subs_resolution = true;
  res_orphan_elimination = true;
  res_time_limit = 2.0;
  res_out_proof = true;
  (*----Combination--------*)
  comb_res_mult = 300;
  comb_inst_mult = 1000;
}

*)

let named_option_smac_tmp () =
  { options_name = "option_smac_tmp"; options = smac_tmp_options (); }
