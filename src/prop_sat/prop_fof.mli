open Lib
open Logic_interface

module PV = Prop_var
module PVE = Prop_env

module PVMap = PV.VMap
module PVSet = PV.VSet

type pvar = PV.var
type plit = PV.lit
type pclause = PVE.clause

type prop_fof_env

val pf_env_create : unit -> prop_fof_env

val prop_var_to_fsymb : prop_fof_env -> pvar -> symbol

(* can raise Not_found *)
val fof_to_prop_symb : prop_fof_env -> symbol -> pvar 

val get_prop_to_fof_symbs : prop_fof_env -> symbol PVMap.t

val prop_lit_to_fof : prop_fof_env -> plit -> term

val fof_lit_to_prop : prop_fof_env -> term -> plit 

val prop_clause_to_fof : prop_fof_env -> pclause -> clause

val fof_clause_to_prop : prop_fof_env -> clause -> pclause

