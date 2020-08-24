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

let assign_map_counter =  ref 0
    
module type KeyEl = 
  sig
    type t
    type e (* t -> element *)
	  (* val compare : t -> t -> int *)
    val hash : t -> int 
    val equal : t -> t -> bool  
    val assign_fast_key : e -> int -> unit
    val assign_db_id : e -> int -> unit
  end

module Make(MKey:KeyEl) = 
  struct
    type key = MKey.t
    type e = MKey.e
    module M = Hashtbl.Make(MKey) 

    type assign_map = 
	{
	 mutable map : e M.t;
	 name : string;
	 map_id : int;        (* all assign_maps get unique id *) 
  	 mutable key_counter : int}

    type t = assign_map 
	  
	  (* size initial size; will be resized as necesssary *)	
    let create size name =
      let new_map = 
	{ map = M.create size;
	  name = name;
	  map_id = !assign_map_counter;
	  key_counter = 0 
	} 
      in
      assign_map_counter := !assign_map_counter +1;
      new_map

    let get_name m  =  m.name

	(* Return the unique identifier of the map *)
    let get_map_id m  = m.map_id

    let mem m k = M.mem m.map k
    let find m k = M.find m.map k
    let size m = M.length m.map
	
	(* f : key -> e -> a -> a*)
    let fold f m a =  M.fold f m.map a

    let iter f m = M.iter f m.map

	(* add m key e *)
	(* adds key -> e to the map and returns the e with assigned map_id and fast_key *)
	(* use find to check key is in the map separately *)
    let add m key e = 
      try (M.find m.map key)
      with
    	Not_found-> 
	  (
	   
	   MKey.assign_fast_key e (m.key_counter);  					
	   MKey.assign_db_id e (get_map_id m);
	   m.key_counter <- m.key_counter + 1;
	   (M.add m.map key e);
	   e
	  )
	    

	    (*note that remove does not decrease the greatest_key*)   	   
    let remove m key =   
      M.remove m.map key
	
    let to_stream s (el_to_str: 'a string_stream -> e -> unit) separator m =
      s.stream_add_str 
	"\n%----------------------------------------------------------\n";
      s.stream_add_str "% ";
      s.stream_add_str (get_name m);
      s.stream_add_str ":\n";
      (M.iter
	 (fun key elem -> 	 
	   (el_to_str s elem);
	   s.stream_add_str separator)
	 m.map);
      s.stream_add_str 
	"\n%----------------------------------------------------------\n";
      s.stream_add_str "%Size of DB ";
      s.stream_add_str (get_name m);     
      s.stream_add_str " is ";
      s.stream_add_str (string_of_int (size m));
      s.stream_add_char '\n'



    let out = to_stream stdout_stream

    let to_string el_to_str separator =
      let stream_fun s m = 
	to_stream s el_to_str separator m in
      to_string_fun_from_to_stream_fun 1000 stream_fun
	

(*debug*)
    let  get_key_counter m = m.key_counter

  end
