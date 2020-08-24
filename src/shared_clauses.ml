open Lib
open Clause

let shared_clauses = ref CSet.empty 
let get_all_shared_clauses () = !shared_clauses
    
let add_shared_clause clause = 
  shared_clauses := CSet.add clause !shared_clauses

let add_shared_clause_list clause_list =
  List.iter add_shared_clause clause_list

let add_shared_clause_set clause_set =
  shared_clauses := CSet.union clause_set !shared_clauses

let rm_shared_clause clause = 
  shared_clauses := CSet.remove clause !shared_clauses

