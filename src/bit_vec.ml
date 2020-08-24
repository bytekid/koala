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







type bit_vec = int

(* in order better type check bit vec is bool vec*)
(* impl: 0 is false 1 is true*)

let false_vec = 0
let true_vec  = lnot 0
    
let max_pos = 30

let set (b:bool) (i: int) (v: bit_vec) = 
  if  ((i <= max_pos) && (i>= 0)) 
  then  
    if b then 
      (*lsl -- shift 1 by i bits*)
      (1 lsl i) lor v 
    else 
      (lnot (1 lsl i)) land v
  else
    failwith "bit_vec: trying to access over the range of bit_vec"

let get (i: int) (v: bit_vec) =
  if  ((i <= max_pos) && (i>= 0)) 
  then
(* lsr shift right*)     
    if ((v lsr i) mod 2) = 0
    then false 
    else true
  else
    failwith "bit_vec: trying to access over the range of bit_vec"
      
