type ar_state

val apply_abstraction : Options.abstr_ref_type -> ar_state -> ar_state
val refine : ar_state -> Term.Set.t -> ar_state
val init_ar_env : Logic_interface.clause list -> ar_state
val get_all_clauses : ar_state -> Logic_interface.CSet.t
val get_all_assumptions : ar_state -> Logic_interface.TSet.t
val refine_until_sat : ar_state -> Term.Set.t -> ar_state
val state_after_until_sat : ar_state -> ar_state
val state_to_str : ar_state -> string
