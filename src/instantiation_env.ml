open Lib
open Options
open Logic_interface

(*-------- instantiation env -----------*)

type dismatching = Dismatching.constr_set

(*----------- clause params ------------*)

let inst_in_active  = 1   
(* let inst_in_unif_index = 2  *)  (* TODO move *)
(* let inst_in_passive_queue = 3 *) (* TODO move to passive queues *)

type inst_cp = (* inst clause param *)
    {
     mutable inst_bool_param : Bit_vec.bit_vec;
(*   mutable inst_sel_lit : (term * sel_place) param; *)
     mutable inst_sel_lit : term  param; 
     mutable inst_dismatching : dismatching param;
     mutable inst_activity : int;
     mutable inst_children : clause list;  
   }   

let inst_create_cp () =
  {
   inst_bool_param = Bit_vec.false_vec;
(*   ps_when_born = Undef; *)
   
   (* inst params *)
   inst_sel_lit = Undef;
   inst_dismatching = Undef;
   inst_activity = 0;
   inst_children = [];

 }

      
let inst_get_cl_bp param cl_param = (* bp -- bool param*)
  Bit_vec.get param cl_param.inst_bool_param 
    
let inst_set_cl_bp bval bparam cl_param =
  cl_param.inst_bool_param <- Bit_vec.set bval bparam cl_param.inst_bool_param

let inst_get_in_active cl_param = 
  inst_get_cl_bp inst_in_active cl_param

let inst_set_in_active bval cl_param = 
  inst_set_cl_bp bval inst_in_active cl_param


type inst_cps = inst_cp BCMap.t (* sim clause params *)

type inst_env = 
    {
     inst_cps          : inst_cps; (* clause paramters *)

(* inst_gr_sel_to_cl: maps grounding of literals selected in clauses into  clauses *)
(* inv: 1. the keys are consistent: there are no complementary literals in the key set *)
(* inv: 2. [C\/L is in active and L is selected in C\/L] iff [ L\gr -> {C\/ L,..} is in inst_gr_sel_to_cl ]  *)
(* inv: 3. in_active iff in unif index *)
     inst_gr_sel_to_cl : (CSet.t ref) TMap.t; 
   }

(* can rasie Not_found *)
let get_inst_cp inst_cps clause = 
  BCMap.find clause inst_cps

let add_inst_cp inst_cps clause cp = 
  BCMap.add clause cp inst_cps

let mem_inst_cp inst_cps clause = 
  BCMap.mem  clause inst_cps


(*----inst non-boolean params -----------*)

 

(*
exception Sel_lit_not_in_cluase

let rec inst_find_sel_place sel_lit lit_list =
  match lit_list with
  | h:: tl ->
      if (h == sel_lit) then 0
      else 1 + (inst_find_sel_place sel_lit tl)
  |[] -> raise Sel_lit_not_in_cluase

*)

let inst_assign_sel_lit sel_lit cp =
  cp.inst_sel_lit <- Def(sel_lit)
(*  let sel_place = inst_find_sel_place sel_lit (get_lits clause) in *)
(*  let ps_param = get_ps_param clause in *)
  (* Format.eprintf
     "Selecting literal %s in clause (%d) %s@."
     (Term.to_string sel_lit)
     (match clause.fast_key with
     | Def key -> key
     | Undef -> -1)
     (to_string clause); *)
(*  ps_param.inst_sel_lit <- Def((sel_lit, sel_place)) *)

let inst_assign_dismatching dismatching cp =
  cp.inst_dismatching <- Def(dismatching)

exception Inst_sel_lit_undef
let inst_cp_get_sel_lit cp =
  match cp.inst_sel_lit with
  | Def(sel_lit) -> sel_lit
  | Undef -> raise Inst_sel_lit_undef

let inst_get_sel_lit inst_cps clause = 
  try 
    let cp = get_inst_cp inst_cps clause in
    inst_cp_get_sel_lit cp 
  with
    Not_found -> raise Inst_sel_lit_undef
(*
let inst_compare_sel_place c1 c2 =
  let c1_ps_param = get_ps_param c1 in
  let c2_ps_param = get_ps_param c2 in
  match (c1_ps_param.inst_sel_lit, c2_ps_param.inst_sel_lit) with
  | (Def((_, sp1)), Def((_, sp2)))
    -> Pervasives.compare sp1 sp2
  | _ -> raise Inst_sel_lit_undef
*)

exception Dismatching_undef
let get_inst_dismatching cp =
  match cp.inst_dismatching with
  | Def(dismatching) -> dismatching
  | Undef -> raise Dismatching_undef

let add_inst_child cp ~child =
  cp.inst_children <- child:: (cp.inst_children)

let get_inst_children cp =
  cp.inst_children

let inst_get_activity cp =
  cp.inst_activity

let inst_assign_activity act cp =
  cp.inst_activity <- act


(*------------ pre-model (pm) ----------------*)

type inst_pre_model_entry = (* pme *)
    {
     mutable inst_pme_sel_lit : lit  param; 
     mutable inst_pme_dismatching : dismatching param;
   }

type inst_pre_model = inst_pre_model_entry BCMap.t

let inst_pme_get_dismatching pme = 
  match pme.inst_pme_dismatching with
  | Def(dismatching) -> dismatching
  | Undef -> raise Dismatching_undef


let inst_pme_get_sel_lit pme =
  match pme.inst_pme_sel_lit with
  | Def(sel_lit) -> sel_lit
  | Undef -> raise Inst_sel_lit_undef


(* can raise Not_found *)
let inst_pm_get_dismatching pm clause = 
 let pme = BCMap.find clause pm in 
 inst_pme_get_dismatching pme

let inst_pm_get_sel_lit pm clause = 
  let pme = BCMap.find clause pm in 
  inst_pme_get_sel_lit pme

(* copy sel_lit and dismatching from cps into pre_model *)
let inst_cps_into_pre_model cps =
  let f clause cp rest = 
    if (inst_get_in_active cp)
    then
      let pre_model_entry = 
        {
         inst_pme_sel_lit = cp.inst_sel_lit;
         inst_pme_dismatching = cp.inst_dismatching;         
       }
    in
      BCMap.add clause pre_model_entry rest
    else
      rest
  in
  BCMap.fold f cps BCMap.empty
    
let inst_pre_model_union pm1 pm2 = 
  let (larger_pm, smaller_pm) = 
    if ((BCMap.cardinal pm1) > (BCMap.cardinal pm2))
    then 
      (pm1,pm2)
    else
      (pm2,pm1)
  in
  let f clause pme rest = 
    BCMap.add clause pme rest 
  in 
  BCMap.fold f smaller_pm larger_pm

let inst_pm_get_clauses inst_pre_model =
  let f cl _cl_param rest = cl::rest in
  BCMap.fold f inst_pre_model []
