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




exception SZS_Unknown

(* unsatisfiable ground possibly with assumptions *)
exception Unsatisfiable_gr 

(* unsatisfiable ground without assumtions; *)
(* solvers should NOT be used after Unsatisfiable_gr_na other than to get proof *)
exception Unsatisfiable_gr_na 

exception Eliminated

val szs_pref            : string 

val szs_unknown_str     : string 
val szs_theorem_str     : string 
val szs_unsat_str       : string 
val szs_sat_str         : string 
val szs_counter_sat_str : string 


val answer_mode_ref : bool ref

val sat_incomplete_mode : bool ref
val unsat_incomplete_mode : bool ref

val iprover_start_time : float
val iprover_running_time : unit -> float

(*  Lazy debug  *)
(* for usage see predElim.ml *)

val dbg_out_pref : bool -> 'a list -> 'a -> ('a -> string) -> string -> string Lazy.t -> unit

val dbg_flag_msg : bool -> string -> unit
    
val dbg_env_set :  bool -> 'a list -> 'a -> (unit -> unit) -> unit

(* gets path to the iprover executable if defined by /proc/self/exe *)
(* else raises Not_found *)

val iprover_exe_name : unit -> string
val iprover_exe_path : unit -> string


(*---------------*)
exception None_opt

(* get_some get option value or raises None_opt if the option is None *)
val get_some : 'a option -> 'a
val get_some_fun : ('b -> 'a option) -> ('b -> 'a)
val is_some : 'a option -> bool

(* "split_some apply list" returns (res_list, none_list); *)
(* iterates over list applying apply and collecting results in res_list *)
(* if Some(res); when apply returns None we add the element of list into  non_list *)

val split_some : ('a -> 'b option) -> 'a list -> ('b list * 'a list)

type 'a param = Def of 'a | Undef 

(* true if param is Def and false if Undef*)
val param_is_def: 'a param -> bool

exception Undef_param

val id_fun   : 'a -> 'a
val unit_fun : 'a -> unit 

(*---------------*)

val apply_fun : ('a -> 'b) param -> 'a -> 'b
val apply_fun_if_def : ('a -> unit) param -> 'a -> unit


(* get_param_val gets prameter value or raises Undef is the paramter is Undef *)
val get_param_val : 'a param -> 'a 
val get_param_val_fun : ('b -> 'a param) -> ('b -> 'a) 

(* elements and ref to elem of indexies and all others*)

  type 'a elem = Elem of 'a | Empty_Elem
  type 'a ref_elem = ('a elem) ref


exception Not_a_singleton
val get_singleton_from_list : 'a list -> 'a

exception Not_a_pair
val get_pair_from_list  : 'a list -> 'a * 'a
val get_pair_first : 'a * 'b -> 'a 
val get_pair_second : 'a * 'b -> 'b 

val pair_get_min : 'a -> 'a -> 'a (* use only for numbers *)

exception Not_a_triple
val get_triple_from_list  : 'a list -> 'a * 'a * 'a

val get_last_pair_from_triple_list : 'a list -> 'a * 'a

exception Empty_list
val split_list : 'a list -> 'a * ('a list) 

(* adds element to a list reference *)
val add_list_ref: 'a list ref ->  'a -> unit

(* does nothing *)
val clear_memory : unit -> unit 

val print_live_memory_usage : unit -> unit
val print_memory_usage : unit -> unit
val print_mem_time_fun : ('a->'b)-> 'a -> 'b

(* print_objsize name t;  prints object size in Megabytes *)

val print_objsize : string -> 'a -> unit

(*------- can be used to test memory usage running the same function n times -------*)
(*------- printing memory statistics -----------------------------------------------*)

val mem_test : (unit->unit) -> int -> unit

val string_of_char : char -> string

(* fun is a function unit -> unit, get_time_fun returns time taken by fun  *)
(* truncated by tranc digits after . *)
val get_time_fun : int -> (unit->unit)-> float

(* truncates float to n digits after . *)
val truncate_n : int -> float -> float 

(* outcome of compare fun.*)
val cequal   : int
val cgreater : int
val cless    : int


val cmp_bool : bool -> bool -> int

(* *)
val param_str_ref : string ref 

val pref_str      : string

(* pref string according to tptp_safe_out option*)
val s_pref_str    : unit -> string 

(* dash_str str:  ------- str ---------*)
val dash_str      : string -> string 

val add_param_str : string -> unit
val add_param_str_front : string -> unit
val param_str_new_line : unit -> unit

val compose_sign  : bool -> ('a -> 'b -> int) -> ('a -> 'b -> int)
(* hash sum where the first arg is rest and second is next number*)
val hash_sum : int -> int ->int 

(*let hash_list hash_elem list*)
val hash_list : ('a -> int) -> 'a list -> int

exception Termination_Signal

(*----------------Processes-----------------*)
(* add_child_process pid *)
val add_child_process           : int -> unit 

(* add_child_process_channels (in_channel,out_channel,error_channel) *)
val add_child_process_channels  : 
    (in_channel * out_channel * in_channel) -> unit


(* removes from the list without killing *)
val remove_top_child_process_channels : unit -> unit 


val kill_all_child_processes : unit -> unit

(*----------------End Processes-----------------*)

(* composes functions *)

val compose_12   : ('a->'b)->('c->'d ->'a) -> 'c->'d -> 'b


(* used for localization of vars, binding can be 
   applied for vars, terms, clauses *)
type 'a bind = int * 'a

val unbound : 'a bind -> 'a
val get_bound : 'a bind -> int

val  propagate_binding_to_list :  ('a list) bind -> ('a bind) list


val apply_to_bounded : ('a -> 'b) -> 'a bind -> 'b bind

val binded_to_string  : ('a -> string) -> 'a bind ->  string

(* lexicographic comparison of pairs*)
val pair_compare_lex : ('a -> 'a -> int)-> ('b -> 'b -> int) -> 'a*'b ->'a*'b -> int

(* bool operations *)
val bool_plus : bool -> bool -> bool

(* returns 1 if true and 0 if false *)
(* in OCaml true >= false and compare true false = 1 *)
val bool_to_int : bool-> int

(*-------- folds a function over intervals -------------*)
(*  fold_up_interval f a b init_val *)
(* folds f from a to b inclusive *)
(* f rest i *)

val fold_up_interval   : ('a -> int -> 'a) -> int -> int -> 'a -> 'a
val fold_down_interval : ('a -> int -> 'a) -> int -> int -> 'a -> 'a

(*----------------lists-------------*)

(* create list of length n consisting of e *)
val list_create : 'a -> int -> 'a list

(* checks whether list is empty *)
val list_is_empty : 'a list -> bool

(* checks whether list is non-empty *)
val list_non_empty : 'a list -> bool

(*returns a list [e;e;e;...] of legth n *)
val list_n : int -> 'a -> 'a list 

val list_skip : 'a -> 'a list -> 'a list

(* partition list into chuncks of specified size  *)	
val list_partition : int -> 'a list -> ('a list) list

(* count the number of elements satisfying p *)
val list_count_p : ('a -> bool) -> 'a list -> int  

val list_remove_last : 'a list -> ('a * 'a list) option

(* explicitly maps from left to right, 
   since order can matter when use imperative features *)
val list_map_left : ('a -> 'b) -> 'a list -> 'b list

val list_to_string : ('a -> string) -> 'a list -> string -> string

val list_of_str_to_str : (string list) -> string -> string

val list_findf : ('a -> 'b option) -> 'a list -> 'b option

(* if tptp_safe_out_ref is true then  % is added to all out_str output *)
(* tptp_safe_out_ref by default is false reassigned by tptp_safe_out input option *)

val tptp_safe_out_ref : bool ref

val tptp_safe_str : string -> string

val out_str : string -> unit
(* out if debug is on *)
(*val out_str_debug : string -> unit*)

val out_err_str : string->unit 
(* out in stderr *)

val out_warning : string->unit 

val list_compare_lex : ('a -> 'a -> int) -> 'a list -> 'a list ->int
val lex_combination  : ('a -> 'a -> int) list -> 'a -> 'a -> int

(* apply iteratively funs in a list to the result  *)
(* let fold_left_fun_list fun_list x = *)

val fold_left_fun_list : ('a -> 'a) list -> 'a -> 'a
val iter_fun_list : ('a -> unit) list -> 'a -> unit

val fix_point_eq : ('a -> 'a -> bool) -> ('a -> 'a) -> 'a -> 'a

val fix_point : ('a -> 'a) -> 'a -> 'a

(* in list_is_max_elem and list_get_max_elements
   we assume that compare as follows: 
   returns cequal if t greater or equal to s and 
   returns cequal+1 if t is strictly greater
   returns cequal-1 if it is not the case
  Note: it is assumed that 
   if t (gr or eq) s and s (gr or eq) t then t==s
*)    

val list_is_max_elem_v :   ('a -> 'a -> int) -> 'a -> 'a list -> bool

val list_get_max_elements_v : ('a -> 'a -> int) -> 'a list -> 'a list

(* for usual orderings *)
val list_is_max_elem :   ('a -> 'a -> int) -> 'a -> 'a list -> bool

(* finds max element in the list if the list is empty raises Not_found*)
val list_find_max_element : ('a -> 'a -> int) -> 'a list -> 'a

val list_find_min_element : ('a -> 'a -> int) -> 'a list -> 'a

val list_find_all_min_elements : ('a -> 'a -> int) -> 'a list -> 'a list
val list_find_all_max_elements : ('a -> 'a -> int) -> 'a list -> 'a list

(* as above but also filter on test *)
val list_find_max_element_p : ('a -> bool) -> ('a -> 'a -> int) -> 'a list -> 'a
val list_find_min_element_p : ('a -> bool) -> ('a -> 'a -> int) -> 'a list -> 'a

(* list_find_pos finds position of the element in a list which satisfies test; starting with 0 *)

val list_find_pos : 'a list -> ('a -> bool) -> int

(* removes duplicates  based on the fact 
  that literals are preordered i.e. the same are in sequence*)
(* based on == *)
val list_remove_duplicates : ('a list) -> ('a list)

(* as above based on = *)
val list_remove_duplicates_ordered_non_ptr : ('a list) -> ('a list)

val unique : ?c:('a -> 'a -> int) -> ('a list) -> ('a list)

val list_find2 : ('a -> 'b -> bool) -> ('a list) -> ('b list) -> ('a *'b) 

val list_return_g_if_f2 : 
    ('a -> 'b -> bool) -> ('a -> 'b -> 'c) -> ('a list) -> ('b list) -> 'c

(* finds first el. a' b' not equal by compare_el, 
  which suppose to return ctrue if equal,
  and returns compare_el 'a 'b 
*)

val list_find_not_equal :  
    ('a -> 'b -> int) -> ('a list) -> ('b list) -> int
	
val list_find_not_identical :
    ('a list) -> ('a list) -> 'a * 'a

(* minimise_list ~keep ~test list  *)
(* returns a minimal substet of the list on which test is true *)
(* keep -- elements that must be kept *)
(* we assume test is monotone -- if test is true on a sub-list then it is true on all lists containing this sub-list *)
(* can raise Not_found if the input list does not satisfy the test *)
(* cmp: compare for priority smaller prioritised for inclusion (larger are eliminated first) *)
val minimise_list : ?cmp:('a -> 'a -> int) -> keep:('a -> bool) -> test:('a list -> bool) -> 'a list -> 'a list

(* returns a list of minimal subsets satisfying test which do not overlap with exception of keep *)
(* if the inital list does not satisfy test then returns [] (does not raise Not_found)*)

val minimise_list_enum : ?cmp:('a -> 'a -> int) -> keep:('a -> bool) -> test:('a list -> bool) -> 'a list -> ('a list) list

(* association lists *)

type ('a, 'b) ass_list = ('a*'b) list

(* appends ass lists: if list1 and list2 have
 elem with (k,v1)  and (k,v2) resp. then new list will have (k,(f !v1 !v2))
 otherwise  appends (k1,v1) and (k2,v2)*)

val append_ass_list : 
    ('b -> 'b -> 'b) -> ('a, 'b) ass_list -> ('a, 'b) ass_list -> ('a, 'b) ass_list

type 'a num_ass_list =  ('a,int) ass_list


(*----------------------------------------------*)
(*------------- reachibility depth -------------*)
(* given a module with an elemet, and reachability relation *)
(* outputs map of rechable elements with the reachability depth *)


module type El =
  sig
    type t 
    val compare : t -> t -> int
  end


module MakeReach : functor
    (El:El) 
    (ReachMap:Map.S with type key=El.t) 
    (ElSet:Set.S with type elt = El.t)     
  ->
  sig
    type reach_map_el = int ReachMap.t
    val compute_reachability_set :
        succ_rel:(ReachMap.key -> ElSet.t) -> ElSet.t -> reach_map_el
    val compute_reachability_list :
        succ_rel:(ReachMap.key -> ElSet.t) -> ElSet.elt list -> reach_map_el
  end

(*
module type ReachRel =
  sig
    type t 
    val succ_rel : t -> t list 
    val compare : t -> t -> int
  end


module MakeReach :
  functor (ReachRel : ReachRel) ->
    sig
      type e = ReachRel.t
      module ReachMap :
          sig   
	    type key = ReachRel.t
	    type 'a t = 'a Map.Make(ReachRel).t
	    val empty : 'a t
	    val is_empty : 'a t -> bool
	    val add : key -> 'a -> 'a t -> 'a t
            val find : key -> 'a t -> 'a
	    val remove : key -> 'a t -> 'a t
	    val mem : key -> 'a t -> bool
	    val iter : (key -> 'a -> unit) -> 'a t -> unit
	    val map : ('a -> 'b) -> 'a t -> 'b t
	    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
	    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
	    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
	    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
          end
      type reach_map_el = int ReachMap.t
      val compute_reachability : ReachMap.key list -> int ReachMap.t
    end

*)


(*----------- Output Buffers/Channels ----------------------*)

(* string stream can be e.g. a buffer or a channel *)

type 'a string_stream = 
    {
     stream : 'a;
     stream_add_char : char   -> unit;
     stream_add_str  : string -> unit;
   }

val stdout_stream : out_channel string_stream
   
(*  "list_to_stream s to_str_el l separator_str" itreates "to_str_el s el" *)
(* over all elements in l and adds sepearator str in between elem. *)

val list_to_stream : ('a string_stream) ->  
                     (('a string_stream) -> 'b -> unit) ->
		     ('b list) -> 
		      string -> 
		      unit

(* "let to_string = to_string_fun_from_to_stream_fun 30 to_stream" *)
(*    creates to_string function from to_stream function with      *)
(*    initial buffer size 30                                       *)


val to_string_fun_from_to_stream_fun :
           int -> (Buffer.t string_stream -> 'a -> 'b) -> 'a -> string
(*
val to_string_fun_from_to_stream_fun :
    int->
    ('a string_stream -> 'b -> unit) ->
    ('b -> string) 
*)

val create_buffer_stream : int -> (Buffer.t string_stream) 

val to_string_buffer_stream :  (Buffer.t string_stream) -> string




val param_to_string : ('a -> string) -> 'a param -> string

val param_to_stream : 
    ((('a string_stream) -> 'b -> unit )-> 
      ('a string_stream)  -> 'b param -> unit)


(** [formatter_of_filename a n] opens the file [n] and returns a
    formatter writing into the opened file. If [a] is true and the
    file exists it is opened for appending, otherwise it is truncated
    to zero length if it exists. Return the formatter writing to
    stdout if file name is "-".  The [Sys_error] exception is not
    caught here but passed to the calling function. *)
val formatter_of_filename : bool -> string -> Format.formatter

(** [pp_any_array pp sep ppf a] prints the elements of the array [a]
    formatted with the [pp] formatting function separated by the
    string [sep] into the formatter [ppf]. *)
val pp_any_array :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a array -> unit

(** [pp_any_list pp sep ppf l] prints the elements of the list [l]
    formatted with the [pp] formatting function separated by the
    string [sep] into the formatter [ppf]. *)
val pp_any_list :
  (Format.formatter -> 'a -> unit) ->
  string -> Format.formatter -> 'a list -> unit

(** [pp_string_list pp sep ppf l] prints the elements of the list of
    strings [l] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_string_list : string -> Format.formatter -> string list -> unit

(** [pp_string_array pp sep ppf a] prints the elements of the array of
    strings [a] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_string_array : string -> Format.formatter -> string array -> unit

(** [pp_int_list pp sep ppf l] prints the elements of the list of
    integers [l] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_int_list : string -> Format.formatter -> int list -> unit

(** [pp_int_array pp sep ppf a] prints the elements of the array of
    integers [a] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_int_array : string -> Format.formatter -> int array -> unit

(** [pp_float_list pp sep ppf l] prints the elements of the list of
    floats [l] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_float_list : string -> Format.formatter -> float list -> unit

(** [pp_float_array pp sep ppf a] prints the elements of the array of
    floats [a] separated by the string [sep] into the formatter
    [ppf]. *)
val pp_float_array : string -> Format.formatter -> float array -> unit

val pp_option : 
  (Format.formatter -> 'a -> unit) -> string -> Format.formatter -> 'a option -> unit

val pp_string_option : string -> Format.formatter -> string option -> unit

val string_of_string_option : string -> string option -> string


(*---------strings-----------*)

(*string filled with n spaces *)
val space_str        :  int -> string 
val space_str_sep    : char -> int -> string 


val to_stream_space : 'a string_stream -> int -> unit
val to_stream_space_sep : char -> 'a string_stream -> int -> unit


(* add spaces to str to reach distance *)
(*if the distance is less than or equal to str then just one space is added*)
(*(used for formatting output) *)
val space_padding_str :  int -> string -> string

val space_padding_str_sep : char -> int -> string -> string

(*--------Named modules----------------------*)

module type NameM = 
  sig
    val name : string
  end

(*----------------reals-----------------*)

(* decimal reals *)
type real = 
    {
     (* real_fraction Ee b*)
     mutable real_fraction    : float;
     mutable real_exponent    : int; 
   }

val real_to_string : real -> string


(*--------------Global Time Limits-------------------*)
(* time limit in seconds *)
(* time_limit can be reassigned, there are number of points where it is checked*)


exception Timeout

(*---------Discount time limits can be checked in all related modules-------*)
(* After Timeout using discount can be incomplete (bit still sound) *)

val assign_discount_time_limit :float -> unit 
val assign_discount_start_time : unit -> unit
val unassign_discount_time_limit : unit -> unit

val check_disc_time_limit : unit -> unit

(* removes duplicates and also order list *)

val list_remove_int_duplicates : int list -> int list 

(*-----------------------*)

module type Ordered = 
  sig
    type t 
    val compare : t -> t -> int
  end

(*------Integer Map/Htbl/Set modules--------------*)


module IntKey :
  sig 
    type t = int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

module IntMap : Map.S with type key = int
module IntHtbl : Hashtbl.S with type key = int
module IntSet  : Set.S with type elt = int

(*----- Pairs of int------ *)

module PairIntKey :
  sig
    type t = int * int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

module PairIntMap : Map.S with type key = (int * int)
module PairIntHtbl : Hashtbl.S with type key = (int * int)
module PairIntSet  : Set.S with type elt = (int * int)
