type result = Satisfiable | Unsatisfiable | Unknown

val do_something_smart : Clause.clause list -> result

val print_empty_clause_result : unit -> unit