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

type options = 
    {
(*---input----*)
     mutable output_dir                  : string;
   }

let default_options () = 
  {
(*---input----*)
   output_dir             = "";
 }

(*---------------*)
let options = ref (default_options ())

(*--------------*)
let bool_str   = "<bool>"
let str_str = "<str>"
let int_str    = "<int>"
let float_str    = "<float>"
let inf_pref  = "\n    "

(*--------------*)


 let usage_msg = 
   "\n fasta <options> "
   ^inf_pref^"generates fasta\n"

(*--------------*)

let default_arg_fun str = 
  failwith "there should be no default arguments"

(*---------*)
let opt_output_dir_str = "--output_dir"

let opt_output_dir_fun s = 
  !options.output_dir <- s
  (*tmp_file_name:=Filename.concat s !tmp_file_name*)

let opt_output_dir_inf = 
  (str_str^" -- the full path for the output of the resulting files\n")

(*-----------------------------*)      
let speclist = 
  [
   (opt_output_dir_str, Arg.String(opt_output_dir_fun),opt_output_dir_inf);
 ]

let parse_options () =
  Arg.parse speclist default_arg_fun usage_msg


let _ =  parse_options ()
