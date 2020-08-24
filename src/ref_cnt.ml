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

(* refernce counting *)

open Lib

module type RCSig = 
  sig
    type el 
    type rc   
    val create : unit -> rc  
    val get_num_el : rc -> int (* num of refs without multiplicities *)
    val get_cnt : rc -> el -> int
    val add_cnt : rc -> el -> int
    val remove_cnt : rc -> el -> int
(*    include Map.S   *)
  end


module Make (El:Ordered) = 
  struct
    module CMap = Map.Make (El)
    open CMap

    type el = El.t

    type rc = (* ref count *)
          {
           mutable cnt_map : int CMap.t;
           mutable num_el  : int; 
         }

    let create () = 
      {
       cnt_map = CMap.empty;
       num_el = 0
     }

    let get_num_el rc = rc.num_el

    let get_cnt rc e = 
      try 
        CMap.find e rc.cnt_map 
      with 
        Not_found -> 0

(* adds element and returns current count *)
    let add_cnt rc e = 
      let current_cnt = get_cnt rc e in
      let new_count = current_cnt + 1 in 
      rc.cnt_map <- CMap.add e new_count rc.cnt_map; 
      (if (new_count = 1) 
      then 
        rc.num_el <- rc.num_el + 1
      );
      new_count
        
    let remove_cnt rc e = 
      let current_cnt =  get_cnt rc e in
      let new_count = current_cnt - 1 in 
      (if (current_cnt = 1)
      then 
        rc.num_el <- rc.num_el - 1
      ); 
      if (new_count <= 0) 
      then 
        begin
          rc.cnt_map <- CMap.remove e rc.cnt_map;
          0
        end
      else
        begin
          rc.cnt_map <- CMap.add e new_count rc.cnt_map; 
          new_count
        end
  end
