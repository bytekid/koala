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








type key = int

(*type 'a array = 'a array*)

type 'a table = 
    {mutable array      :  'a array; 
     mutable max_key    :   int;
     mutable array_size : int}

let create init_size x = 
  {array   = Array.make init_size x;
   max_key = 0; array_size = init_size}
    (* max_key is current unused key *)
    
let num_of_elem table = table.max_key
    
let get table key = Array.get table.array key
    
let assign table key value = 
  if key <= table.max_key 
  then  Array.set table.array key value
  else failwith "tableArray: assignment is out of the range" 
      
let get_next_key table = 
  let old_key = table.max_key in
  if table.max_key < table.array_size -1
  then 
    (table.max_key <- table.max_key +1;
     old_key)
  else
    let new_array_size = 2*table.array_size in
    let new_array = Array.make new_array_size table.array.(0) in
    Array.blit table.array 0 new_array 0 table.array_size;
    table.array <- new_array;
    table.array_size <- new_array_size; 
    table.max_key <- table.max_key +1;
    old_key

let iter f table  = 
  if table.max_key =0 then ()
  else
    for i = 0 to table.max_key-1
    do f table.array.(i) done

let fold_left f a table = 
  if table.max_key =0 then a 
  else
    (let res_ref = ref a in 
    (for i = 0 to table.max_key-1
    do res_ref := f !res_ref table.array.(i) done);
    !res_ref)

let key_to_int key = key
