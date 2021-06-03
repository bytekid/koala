type atomic =
  | DiffVars of Var.var * Var.var
  | DiffTop of Var.var * Symbol.symbol

type conjunct = atomic list

type t = conjunct list

exception Is_unsat

val top : t

val bot : t

val atom : atomic -> t

val is_diff_top: atomic -> bool

val is_diff_var: atomic -> bool

val pp_constraint : Format.formatter -> t -> unit

val equal : t -> t -> bool

val unsat : (Symbol.t * int) list -> t -> bool

val conj1 : conjunct -> t -> t

val conj : t -> t -> t

val substituted_sat : Subst.subst -> t -> bool

val substitute : Subst.subst -> t -> t

val rename : Var.renaming -> t -> t

val vars : t -> Var.t list

val project : Var.t list -> t -> t

val implies : t -> t -> bool

val negate : Var.var list -> t -> Subst.subst list

val fresh_vars : Var.t list -> Var.t -> int -> Var.var list
