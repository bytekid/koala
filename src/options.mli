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






(* Option values with defaults and overrides from files or command-line *)

(** An option set from different sources *)
type 'a override =

    (** Option has the default value *)
  | ValueDefault of 'a

	(** Default has been overridden by file argument *)
  | ValueFile of 'a

	(** Default has been overridden by command-line argument *)
  | ValueCmd of 'a

(** Get current value of option *)
val val_of_override : 'a override -> 'a

(** Override a default value, returning a new default value, but keep
    file and command-line values *)
val override_default : 'a -> 'a override -> 'a override

(** Override a default or file value, returning a new file value,
    but keep a command-line value *)
val override_file : 'a -> 'a override -> 'a override

(** Override a default, file or command-line value, returning a new
    command-line value *)
val override_cmd : 'a -> 'a override -> 'a override


(*-----------------Option Types---------------------------*)

type out_options_type = Out_All_Opt | Out_Control_Opt | Out_No_Opt


(** Output no statistics, statistics after every bound or only after
    the last bound in BMC1 *)
type bmc1_out_stat_type =
    BMC1_Out_Stat_None | BMC1_Out_Stat_Full | BMC1_Out_Stat_Last

(** Axioms for BMC1 *)
type bmc1_axioms_type =
    BMC1_Axioms_Reachable_All | BMC1_Axioms_Reachable_Last

(** Adding unsat core for next bound *)
type bmc1_add_unsat_core_type =
  | BMC1_Add_Unsat_Core_None (** Do not add clauses from unsat core *)
  | BMC1_Add_Unsat_Core_Clauses (** Add clauses in unsat core *)
  | BMC1_Add_Unsat_Core_Leaves (** Add leaf (input) clauses *)
  | BMC1_Add_Unsat_Core_All (** Add all clauses and their parents *)

type bmc1_ucm_cone_mode_type =
  | BMC1_Ucm_Cone_Mode_None
  | BMC1_Ucm_Cone_Mode_AIG
  | BMC1_Ucm_Cone_Mode_Symb
  | BMC1_Ucm_Cone_Mode_UC

(*--------*)
type splitting_mode_type = Split_Input |Split_Full | Split_None

(*--------*)
type prep_sem_filter_type =
    Sem_Filter_None | Sem_Filter_Pos | Sem_Filter_Neg | Sem_Filter_Exhaustive


type schedule_type =
  |Schedule_none
  |Schedule_default
  |Schedule_sat
  |Schedule_abstr_ref
  |Schedule_abstr_ref_sat
  |Schedule_verification_epr_old
  |Schedule_verification_epr_tables
  |Schedule_verification_epr
  |Schedule_smac_tmp

(*-----Lit Params----------*)

type lit_cmp_type =
  | Lit_Sign    of bool
  | Lit_Ground  of bool
  | Lit_Prop    of bool
  | Lit_Num_of_Var  of bool
  | Lit_Num_of_Symb of bool
  | Lit_Atom_depth of bool
  | Lit_Split       of bool
  | Lit_Id         of bool
  | Lit_has_conj_symb of bool
  | Lit_has_bound_constant of bool
  | Lit_next_state of bool
  | Lit_reachable_state of bool
  | Lit_has_non_prolific_conj_symb of bool
  | Lit_eq                         of bool
  | Lit_clock                      of bool
  | Lit_less                       of bool
  | Lit_range                      of bool

(*----------------------------- *)

type lit_bool_prop_type = 
  | Lit_bp_sign of bool
  | Lit_bp_epr of bool
  | Lit_bp_eq of bool 
  | Lit_bp_ground of bool 
  | Lit_bp_prop of bool 
  | Lit_bp_conj_symb of bool 

type prop_impl_unit_type = lit_bool_prop_type list

(*----Clause Param---------*)
type cl_cmp_type =
  |Cl_Age         of bool
  |Cl_Num_of_Var  of bool
  |Cl_Num_of_Symb of bool
  |Cl_Num_of_Lits of bool
  |Cl_Ground      of bool
  |Cl_Conj_Dist   of bool
  |Cl_Has_Conj_Symb of bool
  |Cl_has_bound_constant of bool
  |Cl_has_next_state of bool
  |Cl_has_reachable_state of bool
  |Cl_Has_Non_Prolific_Conj_Symb of bool
  |Cl_Max_Atom_Input_Occur of bool
  |Cl_Horn         of bool
  |Cl_EPR          of bool
  |Cl_in_unsat_core of bool
  |Cl_Has_Eq_Lit   of bool
  |Cl_min_defined_symb of bool
  |Cl_bc_imp_inh of bool
  
val cl_cmp_type_to_str : cl_cmp_type -> string

(*-------------------- bc_imp_inh: important basic clauses --------------*)

type bc_imp_inh_type = BCI_bmc1_lemma | BCI_conj_cone

type bc_imp_inh_list_type = bc_imp_inh_type list

(*----------- abstr-ref -----------*)
exception Unknown_abstr_ref_type

type abstr_ref_type = 
  |Abstr_ref_subs 
  |Abstr_ref_sig  
  |Abstr_ref_arg_filter

val abstr_ref_type_to_str : abstr_ref_type -> string
val str_to_abstr_ref_type : string -> abstr_ref_type

type abstr_ref_list_type = abstr_ref_type list 
val abstr_ref_list_type_to_str : abstr_ref_list_type -> string
val str_to_abstr_ref_list_type : string ->  abstr_ref_list_type    

(*-------------------- Abstr_ref signature abstraction restricted ----------------*)
exception Unknown_abstr_ref_sig_restrict_type

type abstr_ref_sig_restrict_type = Funpre | Skc

val abstr_ref_sig_restrict_type_to_str : abstr_ref_sig_restrict_type -> string
val str_to_abstr_ref_sig_restrict_type : string -> abstr_ref_sig_restrict_type

(*--------------*)
type qbf_dom_inst_type = 
  | QBF_dom_inst_none
  | QBF_dom_inst_single 
  | QBF_dom_inst_chain

(*---Inst Lit Sel----*)

type inst_lit_sel_type    = lit_cmp_type list

type cl_measure_type = 
  |CM_num_lit
  |CM_num_var
  |CM_num_symb
  |CM_cnt
  |CM_none

type passive_queue_type   = PQT_Queue | PQT_Stack | PQT_List | PQT_PriorityQueues
type pass_queue_type      = cl_cmp_type  list
type pass_queue_list_type = pass_queue_type list
type passive_queue_freqs  = int list

type inst_sel_renew_type = Inst_SR_Solver | Inst_SR_Model



(*---------------------sat_out_model option types-----------------------------------*)

type sat_out_model_type = Model_Small | Model_Pos | Model_Neg | Model_Implied | Model_Debug | Model_Intel |Model_None


(*--------------------Resolution Option Types--------------*)

(*----Subsumption----*)
type res_subs_type = Subs_Full | Subs_Subset | Subs_By_Length of int

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

(*-----*)
type res_ord_type =
  | Res_ord_kbo
  | Res_ord_kbo_pred

type res_to_prop_solver_type =
    Res_to_Solver_Active | Res_to_Solver_Passive | Res_to_Solver_None

(*---------*)
type extra_neg_conj_type = ENC_none | ENC_all_neg | ENC_all_pos | ENC_all_pos_neg


(*-----All options-----*)

(* Warning: functional options such as inst_lit_sel and inst_pass_queue1 *)
(* declare only types! if the options are changed, *)
(* one needs to change corresponding functions separately *)

type options = {

    mutable out_options           : out_options_type override;
    mutable tptp_safe_out         : bool;

(*----Input-------*)
    mutable problem_path          : string;
    mutable include_path          : string;
    mutable problem_files         : string list;
    mutable clausifier            : string;
    mutable clausifier_options    : string;
    mutable stdin                 : bool;
    mutable dbg_backtrace         : bool;
    mutable dbg_more         : bool;
    mutable dbg_dump_prop_clauses : bool;
    mutable dbg_dump_prop_clauses_file : string;
    mutable dbg_out_stat          : bool;

(*----General--------*)
    mutable fix_init_inter        : bool option;
    mutable time_out_real         : float;
    mutable time_out_prep_mult    : float;
    mutable time_out_virtual      : float;
    mutable schedule              : schedule_type;
    mutable splitting_mode        : splitting_mode_type;
    mutable splitting_grd         : bool;
    mutable splitting_cvd         : bool;
    mutable splitting_cvd_svl     : bool;
    mutable splitting_nvd         : int;
    mutable non_eq_to_eq          : bool;
    mutable prep_gs_sim           : bool;
    mutable prep_unflatten        : bool;
    mutable prep_res_sim          : bool;
    mutable prep_upred            : bool;
    mutable res_sim_input         : bool;
    mutable clause_weak_htbl      : bool;
    mutable gc_record_bc_elim     : bool;
    mutable symbol_type_check     : bool;
    mutable clausify_out          : bool;
    mutable prep_sem_filter       : prep_sem_filter_type;
    mutable prep_sem_filter_out   : bool;
    mutable preprocessed_out      : bool;
    mutable preprocessed_stats    : bool;
    mutable sub_typing            : bool;
    mutable eq_ax_congr_red       : bool;
    mutable brand_transform       : bool;
    mutable pure_diseq_elim       : bool;
    mutable min_unsat_core        : bool;
    mutable pred_elim             : bool;
    mutable add_important_lit     : bool;
    mutable soft_assumptions      : bool;
    mutable soft_lemma_size       : int;
    mutable prop_impl_unit_size   : int; 
    mutable prop_impl_unit        : prop_impl_unit_type;
    mutable share_sel_clauses     : bool;
    mutable reset_solvers         : bool;
    mutable bc_imp_inh            : bc_imp_inh_list_type;
    mutable conj_cone_tolerance   : float;
    mutable extra_neg_conj        : extra_neg_conj_type;

    mutable abstr_ref : abstr_ref_list_type;
(*
    mutable abstr_ref_arg_filter  : bool;
    mutable abstr_ref_sig         : bool;
    mutable abstr_ref_subs        : bool;
*)
    mutable abstr_ref_prep        : bool;
    mutable abstr_ref_until_sat   : bool;
    (* mutable abstr_terms_sig       : bool;
     * mutable abstr_skolem_sig      : bool; *)
    mutable abstr_ref_sig_restrict : abstr_ref_sig_restrict_type;
    mutable abstr_ref_af_restrict_to_split_sk : bool;
    mutable prep_def_merge        : bool;
    mutable prep_def_merge_prop_impl : bool;
    mutable prep_def_merge_mbd    : bool;
    mutable prep_def_merge_tr_red : bool;
    mutable prep_def_merge_tr_cl  : bool;

(*---Large Theories---------------*)
    mutable large_theory_mode     : bool;
    mutable prolific_symb_bound   : int;
(*---threshold when the theory is considered to be large---*)
    mutable lt_threshold          : int;

(*----Sat Mode-----------*)
    mutable sat_mode              : bool;
    mutable sat_fm_restart_options : string;
    mutable sat_gr_def            : bool;
    mutable sat_epr_types         : bool;
    mutable sat_non_cyclic_types  : bool;
    mutable sat_finite_models     : bool;
    mutable sat_fm_lemmas         : bool;
    mutable sat_fm_prep           : bool;
    mutable sat_fm_uc_incr        : bool;   
    mutable sat_out_model         : sat_out_model_type;
    mutable sat_out_clauses       : bool;

 (*---- QBF Mode-----------*)
    mutable qbf_mode      : bool;
    mutable qbf_elim_univ : bool;
    mutable qbf_dom_inst  : qbf_dom_inst_type;
    mutable qbf_dom_pre_inst : bool;
    mutable qbf_sk_in     : bool;
    mutable qbf_pred_elim : bool;
    mutable qbf_split     : int;

(*----BMC1---------------*)
    mutable bmc1_incremental      : bool override;
    mutable bmc1_axioms           : bmc1_axioms_type override;
    mutable bmc1_min_bound        : int override;
    mutable bmc1_max_bound        : int override;
    mutable bmc1_max_bound_default : int override;
    mutable bmc1_symbol_reachability : bool;
    mutable bmc1_property_lemmas  : bool;
    mutable bmc1_k_induction      : bool;
    mutable bmc1_non_equiv_states : bool;
    mutable bmc1_deadlock         : bool;
    mutable bmc1_ucm              : bool;
    mutable bmc1_add_unsat_core   : bmc1_add_unsat_core_type override;
    mutable bmc1_unsat_core_children : bool override;
    mutable bmc1_unsat_core_extrapolate_axioms : bool override;
    mutable bmc1_ground_init          : bool;
    mutable bmc1_pre_inst_next_state  : bool;
    mutable bmc1_pre_inst_state       : bool;
    mutable bmc1_pre_inst_reach_state : bool;
    mutable bmc1_out_stat         : bmc1_out_stat_type override;
    mutable bmc1_out_unsat_core   : bool override;
    mutable bmc1_aig_witness_out  : bool;
    mutable bmc1_verbose          : bool override;
    mutable bmc1_dump_clauses_tptp : bool override;
    mutable bmc1_dump_unsat_core_tptp : bool override;
    mutable bmc1_dump_file        : string option override;
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
    mutable aig_mode               : bool;

(*----Instantiation------*)
    mutable instantiation_flag                : bool;
    mutable inst_lit_sel                      : inst_lit_sel_type;
    mutable inst_lit_sel_side                 : cl_measure_type;
    mutable inst_solver_per_active            : int;
(*    mutable inst_solver_per_clauses           : int;
*)
    mutable inst_solver_calls_frac            : float;
    mutable inst_passive_queue_type           : passive_queue_type;
    mutable inst_passive_queues               : pass_queue_list_type;
    mutable inst_passive_queues_freq          : passive_queue_freqs;
    mutable inst_dismatching                  : bool;
    mutable inst_eager_unprocessed_to_passive : bool;
    mutable inst_prop_sim_given               : bool;
    mutable inst_prop_sim_new                 : bool;
    mutable inst_subs_given                   : bool;
    mutable inst_subs_new                     : bool;    
    mutable inst_eq_res_simp                  : bool;
    mutable inst_orphan_elimination           : bool;
    mutable inst_learning_loop_flag           : bool;
    mutable inst_learning_start               : int;
    mutable inst_learning_factor              : int;
    mutable inst_start_prop_sim_after_learn   : int;
    mutable inst_sel_renew                    : inst_sel_renew_type;
    mutable inst_lit_activity_flag            : bool;
    mutable inst_restr_to_given               : bool;
    mutable inst_activity_threshold           : int;
    mutable inst_out_proof                    : bool override;

(*----Resolution---------*)
    mutable resolution_flag               : bool;
    mutable res_lit_sel                   : res_lit_sel_type;
    mutable res_lit_sel_side              : cl_measure_type;
    mutable res_ordering                  : res_ord_type;
    mutable res_to_prop_solver            : res_to_prop_solver_type;
    mutable res_prop_simpl_new            : bool;
    mutable res_prop_simpl_given          : bool;
    
    mutable res_passive_queue_type        : passive_queue_type;
    mutable res_passive_queues            : pass_queue_list_type;
    mutable res_passive_queues_freq       : passive_queue_freqs;

    mutable res_forward_subs              : res_subs_type;
    mutable res_backward_subs             : res_subs_type;
    mutable res_forward_subs_resolution   : bool;
    mutable res_backward_subs_resolution  : bool;
    mutable res_orphan_elimination        : bool;
    mutable res_time_limit                : float;
    mutable res_out_proof                 : bool;

(*----Combination--------*)
    mutable comb_res_mult                 : int;
    mutable comb_inst_mult                : int;
}

type named_options = {options_name : string; options : options}

val current_options : options ref

(* Set new current options, preserving overridden option values *)
val set_new_current_options : options -> unit

val input_options : options
val input_named_options : named_options

(*-------------------------------------------*)
(* maps bc_imp_inh into integer priorities; *)
(* priority decreases with values highest priority is 0, lowest max_int *)
(* priorities are grouped in blocks by shifting by 8 bits;  *)   

(* maps bc_imp_inh into integer priorities *)   
val bc_imp_inh_default_val : int

(* get the summand for the priority block corresponding to bc_imp_inh_type  *)
val get_bc_imp_inh_shift : options -> bc_imp_inh_type -> int

val bc_imp_inh_exists :  options -> bc_imp_inh_type -> bool

(*-------------------------------------------*)
(* if there is no conjectures then we can to remove corresponding comparisons*)

val strip_conj_named_opt : named_options -> named_options


type opt_val_type = string * string

val opt_val_to_str : opt_val_type -> string

val opt_val_list_to_str : opt_val_type list -> string

val pass_queues_type_to_str : pass_queue_list_type -> string
val passive_queue_freqs_to_str : int list -> string

(*--------Creates a reasonable option to deal with many axioms such as SUMO-----*)
(*-------based on a given option-------------------*)
val named_opt_to_many_axioms_named_opt1 : named_options -> named_options
val named_opt_to_many_axioms_named_opt2 : named_options -> named_options
val named_opt_to_many_axioms_named_opt3 : named_options -> named_options


val named_option_1   : unit -> named_options
val named_option_1_1 : unit -> named_options
val named_option_1_2 : unit -> named_options
val named_option_2   : unit -> named_options
val named_option_2_1 : unit -> named_options
val named_option_3   : unit -> named_options
val named_option_3_1 : unit -> named_options
val named_option_4   : unit -> named_options
val named_option_4_1 : unit -> named_options

val named_option_finite_models : unit -> named_options
val named_opt_sat_mode_off : named_options -> named_options
val named_opt_sat_mode_on  : named_options -> named_options

val named_option_epr_non_horn_non_eq : unit -> named_options
val named_option_epr_non_horn_eq : unit -> named_options

(* val option_epr_non_horn_eq : unit -> options *)

val named_option_epr_horn_non_eq     : unit -> named_options
(* val option_epr_horn : unit -> options *)

val named_option_verification_epr_old : unit -> named_options
val named_option_verification_epr_tables : unit -> named_options
val named_option_verification_epr : unit -> named_options

val named_option_smac_tmp : unit -> named_options

val res_lit_sel_type_to_str : res_lit_sel_type -> string
val get_problem_files : unit -> string list

val options_to_str : options -> string

(* inferred options: *)

val prop_solver_is_on : unit -> bool
