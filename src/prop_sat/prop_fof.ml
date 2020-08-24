open Lib
open Logic_interface 

(*----- debug modifiable part -----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace


let dbg_gr_to_str = function 
  | D_trace -> "trace"

let dbg_groups =
  [
   D_trace;  
 ]

let module_name = "prop_fof"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


(* can not open both prop modules and Logic_interface since many name clashes *)
module PV  = Prop_var
module PVE = Prop_env

module PVMap = PV.VMap
module PVSet = PV.VSet

module PLMap = PV.LMap
module PLSet = PV.LSet

let bool_type = Symbol.symb_bool_type
let prop_type = Symbol.symb_default_type

type pvar = PV.var
type plit = PV.lit
type pclause = PVE.clause

type prop_fof_env = 
    {
     mutable prop_to_fof_symbs : symbol PVMap.t;
     mutable fof_to_prop_symbs : PV.var SMap.t;

     mutable prop_to_fof_lits : term PLMap.t;
     mutable fof_to_prop_lits : plit TMap.t;

     mutable prop_to_fof_clauses : Clause.clause PVE.CMap.t;
     mutable fof_to_prop_clauses : PVE.clause CMap.t;
   }

let pf_env_create () = 
  {
   prop_to_fof_symbs = PVMap.empty;
   fof_to_prop_symbs = SMap.empty;
   prop_to_fof_lits = PLMap.empty;
   fof_to_prop_lits = TMap.empty;
   prop_to_fof_clauses = PVE.CMap.empty;
   fof_to_prop_clauses = CMap.empty;
 }


let get_prop_to_fof_symbs pf_env = pf_env.prop_to_fof_symbs

let prop_var_to_fsymb pf_env pvar = 
  try 
    PVMap.find pvar pf_env.prop_to_fof_symbs
  with 
    Not_found -> 
      let pred_name = ("$$iProver_qbf_prop_"^(PV.var_to_string pvar)) in 
      let stype = create_stype [] bool_type in
      let pred_symb = create_symbol pred_name stype in
      pf_env.prop_to_fof_symbs <- PVMap.add pvar pred_symb pf_env.prop_to_fof_symbs;
      pf_env.fof_to_prop_symbs <- SMap.add pred_symb pvar pf_env.fof_to_prop_symbs;
      pred_symb

(* can raise Not_found *)
let fof_to_prop_symb pf_env symb = 
  SMap.find symb pf_env.fof_to_prop_symbs

let prop_lit_to_fof pf_env plit = 
  try 
    PLMap.find plit pf_env.prop_to_fof_lits 
  with 
    Not_found -> 
      let (sign,pvar) = PV.lit_to_var plit in
      let pred_symb = prop_var_to_fsymb pf_env pvar in 
      let fof_lit = add_lit_symb sign pred_symb [] in
      let fof_compl_lit = add_compl_lit fof_lit in 
      let compl_plit = PV.compl_lit plit in
      (* add both lit and its complement *) 
      pf_env.prop_to_fof_lits <- PLMap.add plit fof_lit pf_env.prop_to_fof_lits;
      pf_env.prop_to_fof_lits <- PLMap.add compl_plit fof_compl_lit pf_env.prop_to_fof_lits;

      pf_env.fof_to_prop_lits <- TMap.add fof_lit plit pf_env.fof_to_prop_lits;   
      pf_env.fof_to_prop_lits <- TMap.add fof_compl_lit compl_plit pf_env.fof_to_prop_lits;   

(*
  pf_env.prop_to_fof_lits <- PLMap.add plit fof_lit pf_env.prop_to_fof_lits;
  pf_env.fof_to_prop_lits <- TMap.add fof_lit plit pf_env.fof_to_prop_lits;   
 *)      
      fof_lit

        
let fof_lit_to_prop pf_env flit = 
  try 
    TMap.find flit pf_env.fof_to_prop_lits
  with 
    Not_found -> failwith ("fof_lit_to_prop: fof lit "^(Term.to_string flit)^" is not in pf_env")


let prop_clause_to_fof pf_env pclause =   
  let plits = PVE.clause_get_lits pclause in
  let fof_lits = List.map (prop_lit_to_fof pf_env) plits in
  let tstp_source = Clause.tstp_source_input "qbf_preprocess" "qbf" in (* TODO change tstp_source_input *)
  let new_fof_clause = create_clause tstp_source fof_lits in 
  new_fof_clause
    

let fof_clause_to_prop pf_env fclause = 
  let flits = Clause.get_literals fclause in 
  let plits = List.map (fof_lit_to_prop pf_env) flits in 
  let new_prop_clause = PVE.clause_create plits PVE.P_Input in (* TODO change source *)
  new_prop_clause
    

