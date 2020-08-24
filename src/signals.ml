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
open Options 

(*------------------Signals:-----------------*)

exception Time_out_real
exception Time_out_virtual

let set_sys_signals () =
  let signal_handler signal =
    if (signal = Sys.sigint || signal = Sys.sigterm || signal = Sys.sigquit)
    then raise Termination_Signal
    else
      if (signal = Sys.sigalrm)
      then raise Time_out_real
      else
	if (signal = Sys.sigvtalrm)
	then raise Time_out_virtual
	else failwith "Unknown Signal"
  in
  Sys.set_signal Sys.sigint (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigterm (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigquit (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle signal_handler);
  Sys.set_signal Sys.sigvtalrm (Sys.Signal_handle signal_handler)
    
let set_time_out () =
  (if input_options.time_out_real > 0.
  then
    (
     ignore
       (Unix.setitimer Unix.ITIMER_REAL
	  {
	   Unix.it_interval = 0.;
	   Unix.it_value = !current_options.time_out_real;
	 })
    )
  else
    if input_options.time_out_real = 0.
    then raise Time_out_real
    else () (* if negative then unlimited *)
  );
  (if input_options.time_out_virtual > 0.
  then
    ignore
      (Unix.setitimer Unix.ITIMER_VIRTUAL
	 {
	  Unix.it_interval = 0.;
	  Unix.it_value = input_options.time_out_virtual;
	})
      
  else
    if !current_options.time_out_virtual = 0.
    then raise Time_out_virtual
    else () (* if negative then unlimited *)
  )
