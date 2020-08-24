(*--- environment for resolution_loop  ---*)
open Lib
open Logic_interface

type res_cl_param

exception  Res_sel_lits_undef

val res_create_cl_param : unit -> res_cl_param

(*------ in_active --------*)

val res_is_in_active : res_cl_param -> bool
val res_set_in_active : bool ->  res_cl_param -> unit

(*------ selection --------*)
val res_sel_is_def : res_cl_param -> bool

(* can raise  Res_sel_lits_undef *)
val res_get_sel_lits : res_cl_param -> lit list

val res_assign_sel_lits : res_cl_param -> lit list -> unit

(*
val res_get_sel_assign : (clause -> lit list) ->  res_cl_param -> clause -> lit list
*)

val res_get_sel_final : res_cl_param -> bool 

val res_set_sel_final : bool ->  res_cl_param -> unit
