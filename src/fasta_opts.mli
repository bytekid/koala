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


type options = { mutable output_dir : string; }
val default_options : unit -> options
val options : options ref
val bool_str : string
val str_str : string
val int_str : string
val float_str : string
val inf_pref : string
val usage_msg : string
val default_arg_fun : 'a -> 'b
val opt_output_dir_str : string
val opt_output_dir_fun : string -> unit
val opt_output_dir_inf : string
val speclist : (string * Arg.spec * string) list
val parse_options : unit -> unit
