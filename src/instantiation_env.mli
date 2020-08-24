(*-------- instantiation env -----------*)

open Lib
open Logic_interface 

type dismatching = Dismatching.constr_set

type inst_cp (* inst clause param *)
type inst_cps = inst_cp BCMap.t

val inst_create_cp : unit -> inst_cp

val inst_get_in_active : inst_cp -> bool 
val inst_set_in_active : bool -> inst_cp -> unit 

(* can rasie Not_found *)
val get_inst_cp : inst_cps -> clause -> inst_cp
val add_inst_cp : inst_cps -> clause -> inst_cp -> inst_cps
val mem_inst_cp : inst_cps -> clause -> bool

val inst_assign_dismatching : dismatching -> inst_cp -> unit
exception Dismatching_undef
val get_inst_dismatching : inst_cp -> dismatching

val inst_assign_sel_lit : lit -> inst_cp -> unit 

exception Inst_sel_lit_undef
val inst_cp_get_sel_lit : inst_cp -> lit
val inst_get_sel_lit : inst_cps -> clause -> lit


val add_inst_child : inst_cp -> child:clause -> unit
val get_inst_children : inst_cp -> clause list

val inst_get_activity : inst_cp -> int
val inst_assign_activity : int -> inst_cp -> unit

(*---------- inst pre model ------------*)
type inst_pre_model_entry = 
    {
     mutable inst_pme_sel_lit : lit  param; 
     mutable inst_pme_dismatching : dismatching param;
   }

type inst_pre_model = inst_pre_model_entry BCMap.t

(* can raise Dismatching_undef *)
val inst_pme_get_dismatching : inst_pre_model_entry -> dismatching 

(* can raise Inst_sel_lit_undef *)
val inst_pme_get_sel_lit : inst_pre_model_entry -> lit

(* can raise Dismatching_undef *)
val inst_pm_get_dismatching : inst_pre_model -> clause -> dismatching

(* can raise Inst_sel_lit_undef *)
val inst_pm_get_sel_lit : inst_pre_model -> clause -> lit

(* union of two pre models; *)
(* assumed that keys (clauses) in two models are disjoint otherwise only one of them  will be added *)
val inst_pre_model_union :  inst_pre_model -> inst_pre_model -> inst_pre_model

val inst_cps_into_pre_model : inst_cps -> inst_pre_model

val inst_pm_get_clauses : inst_pre_model -> clause list
