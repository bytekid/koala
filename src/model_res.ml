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


open Logic_interface
open Instantiation_env
(*------- out models for resolution ---------------*)

let sat_out_active_clauses ~res_model ~filtered_out_inst_pre_model =
  
  (* Filter clause database for active clauses *)
  let res_model_clauses = 
    let f c _cl_param rest = c::rest in
    BCMap.fold f res_model []
  in
  let filtered_out_clauses = 
    let f c _cl_param rest = c::rest in
    BCMap.fold f filtered_out_inst_pre_model []
  in
  (* Start saturation output *)
  Format.printf "@\n%% SZS output start Saturation@\n@.";
  let all_clauses_list = filtered_out_clauses@res_model_clauses in

  (* Saturation output *)
  Format.printf
    "%a@."
    TstpProof.pp_clauses_with_clausification
    all_clauses_list;
  
  (* End saturation output *)
  Format.printf "%% SZS output end Saturation@\n@."

let out_res_model ~res_model ~filtered_out_inst_pre_model =
  sat_out_active_clauses ~res_model ~filtered_out_inst_pre_model
