open Lib
open Logic_interface

(*----- debug modifiable part-----*)

let dbg_flag = false

type dbg_gr = 
  | D_trace

let dbg_gr_to_str = function 
  | D_trace -> "trace"

let dbg_groups =
  [
   D_trace; 
 ]


let module_name = "implied_units"

(*----- debug fixed part --------*)

let () = Lib.dbg_flag_msg dbg_flag module_name

let dbg group str_lazy =
  Lib.dbg_out_pref dbg_flag dbg_groups group dbg_gr_to_str module_name str_lazy

let dbg_env group f =
  Lib.dbg_env_set dbg_flag dbg_groups group f

(*----- debug -----*)


exception Impl_Unit of term


let get_all_ass_implied_lit_but_first asserted_lit = 
  let impl_lits = ref [] in 
  dbg D_trace (lazy ("asseretd lit: "^(Term.to_string asserted_lit)));
  try 
    begin

        let first_impl = 
          try
            Prop_solver_exchange.get_next_ass_implied_unit ~solver_in:Prop_solver_exchange.solver_sim  (* skip asserted *)
          with 
            Not_found ->  
              (
               (* can happen if  asserted_lit is implied without assumptions *)
               let compl_asserted_lit = add_compl_lit asserted_lit in 
               match (Prop_solver_exchange.fast_solve ~solver_in:Prop_solver_exchange.solver_sim [compl_asserted_lit]) with
               | PropSolver.FUnsat ->

                   raise (Impl_Unit(asserted_lit))

               | PropSolver.FSat | PropSolver.FUnknown ->
                   (
                    failwith "get_all_ass_implied_lit_but_first: asserted_lit is not in the impl units"
                   )
              )
        in
        
        (if (not (asserted_lit == first_impl))
        then 
          failwith ("get_all_ass_implied_lit_but_first: asseted literal in not the first implied: "
                    ^("assereted: "^(Term.to_string asserted_lit)^" first implied: "^(Term.to_string first_impl))
                   )
        );
        while true 
        do 
          try
            let next_unit = Prop_solver_exchange.get_next_ass_implied_unit ~solver_in:Prop_solver_exchange.solver_sim in
            dbg D_trace (lazy ("next_unit: "^(Term.to_string next_unit)));
            Term.type_check next_unit;
            impl_lits:= next_unit::(!impl_lits)
          with 
            Term.Type_check_failed -> ()
        done; 
        !impl_lits
    end
  with     
    Not_found -> !impl_lits
    

let all_implied_lits lit = 
  match (Prop_solver_exchange.fast_solve ~solver_in:Prop_solver_exchange.solver_sim [lit]) with
  | PropSolver.FUnsat ->
      (
       let compl_lit = add_compl_lit lit in 
       raise (Impl_Unit(compl_lit))
      )
  | PropSolver.FSat | PropSolver.FUnknown ->
      (get_all_ass_implied_lit_but_first lit)

