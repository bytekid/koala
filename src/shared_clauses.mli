open Lib 
open Clause 

val get_all_shared_clauses : unit -> CSet.t
val add_shared_clause : clause -> unit 
val add_shared_clause_list : clause list -> unit 
val add_shared_clause_set : CSet.t -> unit 
val rm_shared_clause : clause -> unit


