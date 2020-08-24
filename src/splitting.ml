(*----------------------------------------------------------------------(C)-*)
(* Copyright (C) 2006-2017 Konstantin Korovin and The University of Manchester. 
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
open Options
open Statistics

(* a wrapper of all splittings *)

(*------------ splitting --------------*) 
(* TODO: refactor splitting *)

let splitting_grd def_env ~out_progress clauses = 
  (match !current_options.splitting_mode with
  |Split_Input |Split_Full ->    
      if !current_options.splitting_grd
      then
        begin
          let start_gs_time = Unix.gettimeofday () in
          if out_progress then (print_string " gs_s "; flush stdout;);
          let split_result = 
	    (Splitting_grd.ground_split_clause_list def_env clauses) in
          incr_int_stat 
	    (Splitting_grd.get_num_of_splits split_result) num_of_splits; 

          let current_list = Splitting_grd.get_split_list split_result in
          
          let end_gs_time = Unix.gettimeofday () in         
          let gs_time = (end_gs_time -. start_gs_time) in          
          let gs_time_int = truncate (end_gs_time -. start_gs_time) in
          Statistics.add_float_stat gs_time Statistics.splitting_time;
          if out_progress then
            (
             print_string (" sp: "^ (string_of_int (get_val_stat num_of_splits)));
             print_string (" "^ (string_of_int (gs_time_int))^"s ");
             print_string " gs_e "; flush stdout;      
            );
          current_list
        end
      else clauses
  |Split_None-> clauses
  )

 let splitting_cvd def_env ~out_progress clauses = 
   (match !current_options.splitting_mode with
   |Split_Input |Split_Full -> 
       if !current_options.splitting_cvd  
       then 
          begin
            let start_scvd_time = Unix.gettimeofday () in
            if out_progress then (print_string " scvd_s "; flush stdout;);
            let old_num_cls = List.length clauses in
            let current_list = Splitting_cvd.cvd_split_clause_list def_env clauses in
            let new_num_cls = List.length current_list in
            let num_of_splits = new_num_cls - old_num_cls in
            let end_scvd_time = Unix.gettimeofday () in
            let scvd_time = end_scvd_time -. start_scvd_time in
            let scvd_time_int = truncate scvd_time in
            Statistics.incr_int_stat num_of_splits Statistics.num_of_splits;
            Statistics.add_float_stat scvd_time Statistics.splitting_time;
            if out_progress then
              (
               print_string ("sp: "^ (string_of_int (num_of_splits)));
               print_string (" "^ (string_of_int (scvd_time_int))^"s");
               print_string " scvd_e "; flush stdout;
              );
            current_list
          end
        else 
          (clauses)
    |Split_None -> (clauses)
    )
   
 let splitting_nvd def_env ~out_progress clauses = 
   (match !current_options.splitting_mode with
   |Split_Input |Split_Full -> 
       if !current_options.splitting_nvd > 0 
       then 
         begin
           let start_snvd_time = Unix.gettimeofday () in
           if out_progress then (print_string " snvd_s "; flush stdout;);
           let old_num_cls = List.length clauses in
           let current_list = Splitting_nvd.split_clause_list def_env !current_options.splitting_nvd clauses in
           let new_num_cls = List.length current_list in
           let num_of_splits = new_num_cls - old_num_cls in
           let end_snvd_time = Unix.gettimeofday () in
           let snvd_time = end_snvd_time -. start_snvd_time in
           let snvd_time_int = truncate snvd_time in
           Statistics.incr_int_stat num_of_splits Statistics.num_of_splits;
           Statistics.add_float_stat snvd_time Statistics.splitting_time;
           if out_progress then
             (
              print_string ("sp: "^ (string_of_int (num_of_splits)));
              print_string (" "^ (string_of_int (snvd_time_int))^"s");
              print_string " snvd_e "; flush stdout;
             );
           current_list
         end
       else 
         (clauses)
   |Split_None -> (clauses)
   )

let splitting def_env ~out_progress clauses = 
  (splitting_nvd def_env ~out_progress 
     (splitting_cvd def_env ~out_progress 
        (splitting_grd def_env ~out_progress clauses)))
   
