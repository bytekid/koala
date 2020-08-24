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

module type ElemDB = 
  sig
    type t
    val compare : t -> t -> int
    val assign_fast_key : t -> int -> unit
    val assign_db_id : t -> int -> unit
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
    val fold        : (elem -> 'a -> 'a) -> abstDB -> 'a -> 'a
    val iter        : (elem -> unit) -> abstDB -> unit
(*    val to_string   : (elem -> string) -> string -> abstDB ->string*)
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

(*debug*)
    val get_greatest_key : abstDB -> int
  end	
      

module Make(El : ElemDB) =
  struct
    type   elem  = El.t    
    module BasicElem = 
      struct
	type t = El.t
	let compare = El.compare
      end
    module BasicAbstDB =  AbstDB.Make (BasicElem) 
	
    type abstDB = { db : BasicAbstDB.abstDB; 
		    greatest_key : int }

	  (* greates unused key*)
    let create () = 
      { db = BasicAbstDB.create (); greatest_key = 0 }

    let create_name name =
      { db = BasicAbstDB.create_name name; greatest_key = 0 }

    let get_name elem_db  = BasicAbstDB.get_name elem_db.db

	(* Return the unique identifier of the database *)
    let get_db_id elem_db  = BasicAbstDB.get_db_id elem_db.db

    let mem elem elem_db  = BasicAbstDB.mem elem elem_db.db
    let find elem elem_db = BasicAbstDB.find elem elem_db.db
    let size elem_db = BasicAbstDB.size elem_db.db   
    let fold f elem_db a = BasicAbstDB.fold f elem_db.db a

    let iter f elem_db = BasicAbstDB.iter f elem_db.db

	(*add_ref is diff from abstDB*)

    let add_ref elem elem_db_ref = 
      try (find elem !elem_db_ref)
      with
	Not_found-> 

	  let ()=(El.assign_fast_key elem (!elem_db_ref).greatest_key) in       
	  
	  (* Assign unique identifier of database to element *)
	  El.assign_db_id elem (get_db_id !elem_db_ref);

	  let new_greatest_key = ((!elem_db_ref).greatest_key + 1) in
	  elem_db_ref:={db =(BasicAbstDB.add elem (!elem_db_ref).db); 
			greatest_key = new_greatest_key};	  
	  elem
	    
(*since add_ref is diff from abstDB, so add also*)
    let add elem elem_db =
      let elem_db_ref = ref elem_db in
      let _= add_ref elem elem_db_ref in
      !elem_db_ref
	
	(*note that remove does not decrease the greatest_key*)   	   
    let remove elem elem_db =   
      {db   = (BasicAbstDB.remove elem elem_db.db); 
       greatest_key = elem_db.greatest_key }
	
    let map f elem_db = 
      {db   = (BasicAbstDB.map f elem_db.db); 
       greatest_key = elem_db.greatest_key}
	
    let to_stream s (el_to_str: 'a string_stream -> elem -> unit) separator elem_db =
      BasicAbstDB.to_stream s el_to_str separator elem_db.db
	
    let out = to_stream stdout_stream

    let to_string el_to_str separator elem_db =
      BasicAbstDB.to_string el_to_str separator elem_db.db

(*debug*)
    let  get_greatest_key elem_db = elem_db.greatest_key

  end
