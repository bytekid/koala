open Lib
open Logic_interface

(*--- environment for resolution_loop  ---*)

(*----------- clause params ------------*)

let res_in_active  = 1   
let res_sel_final    = 2 
let res_in_passive_queue = 3 (* TODO move to passive queues *)
let res_simplifying = 4

type res_cl_param = 
    {
     mutable res_bool_param : Bit_vec.bit_vec;
     mutable res_sel_lits : lit list; 
     mutable res_when_born  : int param;           
   }   
      
let res_get_cl_bp param c_param = (* bp -- bool param*)
  Bit_vec.get param c_param.res_bool_param 
    
let res_set_cl_bp value bparam c_param =
  c_param.res_bool_param <- Bit_vec.set value bparam c_param.res_bool_param

let res_create_cl_param () =
  {
   res_bool_param = Bit_vec.false_vec;
   res_sel_lits = [];
   res_when_born = Undef;
 }

type rcp = res_cl_param BCMap.t (* sim clause params *)

(*-----*)
let res_is_in_active cl_param  = res_get_cl_bp res_in_active cl_param
let res_set_in_active value cl_param = res_set_cl_bp value res_in_active cl_param

(*-----*)
let res_get_sel_final cl_param = 
  res_get_cl_bp res_sel_final cl_param

let res_set_sel_final value cl_param  = 
  res_set_cl_bp value res_sel_final cl_param


(*-----*)
let res_sel_is_def cl_param =  (not (cl_param.res_sel_lits = []))

exception Res_sel_lits_undef

let res_get_sel_lits cl_param = 
  if (cl_param.res_sel_lits = [])
  then 
    (
     raise Res_sel_lits_undef
    )
  else
    cl_param.res_sel_lits

let res_assign_sel_lits cl_param lits = 
  assert(not (lits = []));
  cl_param.res_sel_lits <- lits


(*
(* don't need it much since in unif index we store (L,clause) *)
let res_get_sel_assign sel_fun cl_param clause =
  if (cl_param.res_sel_lits = [])
  then 
    (
     let sel_lits = sel_fun clause in
     assert(not (sel_lits = []));
     cl_param.res_sel_lits <- sel_lits;
     sel_lits
    )
  else
    (
     cl_param.res_sel_lits
    ) 
  *)    
(*
let res_assign_sel_lits sel_lits cp =
  cp.inst_sel_lit <- Def(sel_lits)
*)



