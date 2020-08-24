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

(* Unique identifier for next database created *)
let next_db_id = ref 0

module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
  end
      
module type AbstDB =
  sig   
    type elem
    type abstDB 
    val create      : unit -> abstDB 
    val create_name : string -> abstDB
    val mem         : elem -> abstDB -> bool 
    val add         : elem -> abstDB -> abstDB
    val add_ref     : elem -> abstDB ref -> elem
    val remove      : elem -> abstDB -> abstDB 
    val find        : elem -> abstDB -> elem
    val size        : abstDB -> int
    val map         : (elem -> elem)-> abstDB -> abstDB 
    val fold        : (elem -> 'a ->  'a) -> abstDB -> 'a -> 'a 
    val iter        : (elem -> unit) -> abstDB -> unit
    val get_name    : abstDB -> string
    val get_db_id   : abstDB -> int

    val to_stream   : 
	'a string_stream -> ('a string_stream -> elem -> unit) ->
	  string -> abstDB -> unit

    val out            : 
	(out_channel string_stream -> elem -> unit) ->
	  string -> abstDB -> unit

    val to_string   : (Buffer.t string_stream -> elem  -> unit) 
      -> string -> abstDB ->  string
(*
  val to_string   : 
  (elem -> 'a string_stream -> unit) 
  -> string -> abstDB ->  string
 *)
	  
  end	

(* implemented as Map with additional size tracking*)

module Make(El : ElemDB) =
  struct
    type   elem  = El.t    
    module BasicAbstDB =  Map.Make (El) 

    type abstDB = 
	{ db : (elem BasicAbstDB.t); 
	  name : string; 

	  (* Unique identifier for this database, needed to create
	     globally unique names for elements with fast_key *)
	  db_id : int;

	  size : int}   
	  
    let create () = 

      (* Increment unique identifier for next database *)
      next_db_id := succ !next_db_id;

      (* Create database *)
      { db = BasicAbstDB.empty; 
	name = "Anonymous DB"; 
	db_id = pred !next_db_id;
	size = 0 }
	
    let create_name (name : string) = 

      (* Increment unique identifier for next database *)
      next_db_id := succ !next_db_id;
      
      (* Create database *)
      { db = BasicAbstDB.empty; 
	name = name; 
	db_id = pred !next_db_id;
	size =0 }
	
    let get_name elem_db = elem_db.name 

	(* Get unique identifier of the database *)
    let get_db_id elem_db = elem_db.db_id 
	
    let mem (elem : elem) (abstDB : abstDB) = BasicAbstDB.mem elem abstDB.db
	
    let find elem elem_db = BasicAbstDB.find elem elem_db.db
    let size elem_db = elem_db.size    
	
    let add_ref elem elem_db_ref = 
      try (find elem !elem_db_ref)
      with
	Not_found-> 
	  elem_db_ref:= 
	    {!elem_db_ref with
             db   =(BasicAbstDB.add elem elem (!elem_db_ref).db); 
	     size = (!elem_db_ref).size + 1 };
	  elem
	    
    let add elem  elem_db =
      let elem_db_ref = ref elem_db in
      let _= add_ref elem elem_db_ref in
      !elem_db_ref
	

    let remove elem elem_db =  
      {elem_db with 
       db   = (BasicAbstDB.remove elem elem_db.db); 
       size = elem_db.size-1}
	
    let map f elem_db = 
      { elem_db with
	db   = (BasicAbstDB.map f elem_db.db)}

    let fold f elem_db a = 
      let f' key elem  a = f elem a in 
      BasicAbstDB.fold f' elem_db.db a
	
    let iter f elem_db = 
      let f' key elem = f elem  in 
      BasicAbstDB.iter f' elem_db.db
	
	(*------------To streams/strings------------------------*)

    let to_stream s (el_to_str: 'a string_stream -> elem -> unit) separator elem_db =
      s.stream_add_str 
	"\n%----------------------------------------------------------\n";
      s.stream_add_str "%DB ";
      s.stream_add_str (get_name elem_db);
      s.stream_add_str ":\n";
      (BasicAbstDB.iter
	 (fun key elem -> 	 
	   (el_to_str s elem);
	   s.stream_add_str separator)
	 elem_db.db);
      s.stream_add_str 
	"\n%----------------------------------------------------------\n";
      s.stream_add_str "%Size of DB ";
      s.stream_add_str (get_name elem_db);     
      s.stream_add_str " is ";
      s.stream_add_str (string_of_int (size elem_db));
      s.stream_add_char '\n'


    let out = to_stream stdout_stream

    let to_string el_to_str separator =
      let stream_fun s elem_db = 
	to_stream s el_to_str separator elem_db in
      to_string_fun_from_to_stream_fun 1000 stream_fun
	

(*
  let to_string el_to_str separator elem_db =
  let sep_line  = 
  "\n%----------------------------------------------------------\n" in
  let init_str  = "%DB "^(get_name elem_db)^":\n" in
  let final_str = 
  "%Size of DB "^(get_name elem_db)^" is "
  ^(string_of_int (size elem_db))^"\n" in
  let main_str = 							 
  BasicAbstDB.fold 
  (fun key elem prev_str -> 
  ((el_to_str elem)^separator^prev_str)) elem_db.db "" in
  init_str^sep_line^main_str^sep_line^final_str
 *)
	
  end
