/*----------------------------------------------------------------------(C)-*/
/* Copyright (C) 2006-2010 Konstantin Korovin and The University of Manchester. 
   This file is part of iProver - a theorem prover for first-order logic.

   iProver is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   iProver is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  
   See the GNU General Public License for more details.
   You should have received a copy of the GNU General Public License
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         */
/*----------------------------------------------------------------------[C]-*/

/*
  
  Created: 2011-12-07 Christoph Sticksel

 */

extern "C" {

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

}

#define DEBUG

/* -D flags in mtl/template.mk */
#define __STDC_LIMIT_MACROS
#define __STDC_FORMAT_MACROS

/* includes from simp/Main.cc */
#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include <utils/System.h>
#include <utils/ParseUtils.h>
#include <utils/Options.h>
#include <core/Dimacs.h>
#include <simp/SimpSolver.h>

/* Define lifted booleans as OCaml integers */
#define Val_l_True Val_int(0)
#define Val_l_False Val_int(1)
#define Val_l_Undef Val_int(2)

/* 'a option = None */
#define Val_none Val_int(0)

/* 'a option = Some of 'a */
static inline value Val_some( value v )
{   
    CAMLparam1 (v);
    CAMLlocal1 (some);
    some = caml_alloc(1, 0);
    Store_field (some, 0, v);
    CAMLreturn (some);
}

/* Switch to MiniSat namespace */
using namespace Hhlmuc;

/* Custom OCaml operations for MiniSat literal 
   
 None of the default operations are defined. 

 TODO: think about defining some of them 
 - finalisation is not needed
 - comparing and hashing would be nice 
 - serialisation is not needed 

*/
static struct custom_operations minisat_lit_custom_ops = {
    identifier: "Hhlmuc::Lit",
    finalize:    custom_finalize_default,
    compare:     custom_compare_default,
    hash:        custom_hash_default,
    serialize:   custom_serialize_default,
    deserialize: custom_deserialize_default
};

/* Copy a MiniSat literal into a newly allocated OCaml custom tag */
static inline value copy_minisat_lit( Lit *lit )
{
    CAMLparam0();
    CAMLlocal1(v);
    v = caml_alloc_custom( &minisat_lit_custom_ops, sizeof(Lit), 0, 1);
    memcpy( Data_custom_val(v), lit, sizeof(Lit) );
    CAMLreturn(v);
}


/* Create and return a Haifa-HLMUC solver instance 

   external hhlmuc_create_solver : unit -> hhlmuc_solver = "hhlmuc_create_solver" 

   The solver is created in the C++ heap, OCaml gets only a pointer in
   an Abstract_tag.

*/
extern "C" value hhlmuc_create_solver(value unit)
{

  // Declare parameters 
  CAMLparam1 (unit);

  // Initialise solver instance 
  Solver* solver = new Solver;
  // SimpSolver* solver = new SimpSolver;

  // Allocate abstract datatype for instance 
  value res = caml_alloc(2, Abstract_tag);

  // First field is pointer to core manager
  Store_field(res, 0, (value) solver); 

  // Second field is number of variables on last solve call
  Store_field(res, 1, (value) 0); 

#ifdef DEBUG
  fprintf(stderr, "Created new hhlmuc instance\n");
#endif

  // Return instance 
  CAMLreturn(res);

}

/* Add a variable to Haifa-HLMUC

   external hhlmuc_add_var : hhlmuc_solver -> int -> unit = "hhlmuc_add_var"

   Variables are integers, the first is 0. Integers do not have to be
   allocated for OCaml.

   Each variable has to be allocated by calling newVar().
   hhlmuc_create_lit does this on literal creation if the variable
   has not been allocated.

 */
extern "C" value hhlmuc_add_var (value solver_in, value var_id_in)
{  

  // Declare parameters 
  CAMLparam2 (solver_in, var_id_in);
  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);
  int var_id = Int_val(var_id_in);

  // Declare variable in MiniSat
  while (var_id + 1 >= solver->nVars()) solver->newVar();

  // Return 
  CAMLreturn(Val_unit);

}

/* Create and return a literal of a variable 

   external hhlmuc_create_lit : hhlmuc_solver -> int -> bool -> hhlmuc_lit = "hhlmuc_create_lit" 

   Variables are integers, the first is 0. Use true for a positive
   literal and false for a negative one.

   A literal has to be created with the mkLit function, it is a custom
   datatype stored on the OCaml heap.

 */
extern "C" value hhlmuc_create_lit(value solver_in, value lit_sign_in, value lit_var_in)
{
  
  // Declare parameters 
  CAMLparam3 (solver_in, lit_sign_in, lit_var_in);
  CAMLlocal1 (res);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  bool lit_sign = Bool_val(lit_sign_in);
  int lit_var = Int_val(lit_var_in);

  // First declare variable in MiniSat
  while (lit_var >= solver->nVars()) solver->newVar();

  // Must use mkLit to create literals 
  Lit lit = mkLit(lit_var, lit_sign);

#ifdef DEBUG
  fprintf(stderr, 
	  "Created literal %d from %s%d\n", 
	  toInt(lit), 
	  lit_sign ? "" : "~", 
	  lit_var);
#endif

  // Allocate and copy MiniSat literal to OCaml
  res = copy_minisat_lit(&lit);

  // Return literal
  CAMLreturn(res);

}

/* Assert a clause given as a list of literals, return false if the
   clause set immediately becomes unsatisfiable, true otherwise.

   external hhlmuc_add_clause : hhlmuc_solver -> hhlmuc_lit list -> bool = "hhlmuc_add_clause" 

*/
extern "C" value hhlmuc_add_clause(value solver_in, value clause_in)
{	

  // Declare parameters 
  CAMLparam2 (solver_in, clause_in);
  CAMLlocal1(head);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  head = clause_in;

  // Clause to be asserted
  vec<Lit> lits;
  lits.clear();

#ifdef DEBUG
  fprintf(stderr, "Asserting other clause ");
#endif

  // Iterate list of literals
  while (head != Val_emptylist) 
    {

      // Get head element of list 
      value lit_in = Field(head, 0);

      // Get MiniSat literal from value
      Lit* lit = (Lit*) Data_custom_val(lit_in);

#ifdef DEBUG
      fprintf(stderr, "%s%d ", 
	      sign(*lit) ? "" : "~",
	      var(*lit));
#endif

      // Add literal to clause 
      lits.push(*lit);

      // Continue with tail of list
      head = Field(head, 1);

    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

#ifdef DEBUG
  fprintf(stderr, "GetLastUid = %d\n", Clause::GetLastUid());
#endif

  // Add clause to solver, mark as not interesting 
  if (solver->addClause_(lits, false))
    {

#ifdef DEBUG
      fprintf(stderr, "GetLastUid = %d\n", Clause::GetLastUid());
#endif

      // Not immediately unsatisfiable 
      CAMLreturn (Val_true);

    }
  else
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable with added clause\n");
#endif

#ifdef DEBUG
      fprintf(stderr, "GetLastUid = %d\n", Clause::GetLastUid());
#endif

      // Immediately unsatisfiable with added clause
      CAMLreturn (Val_false);

    }

}

/* Assert a clause, given as a list of literals, as an interesting
   constraint clause. Return both a flag if the clause is immediately
   unsatisfiable and a possibly undefined unique id for the clause.
   
   The unique id is [None] if the clause was simplified or if it is
   unsatisfiable. A return value of [(false, None)] means the clause
   is immediately unsatisfiable, if [(true, None)] is returned, the
   clause is already satisfied, otherwise the return value is [(true,
   Some id)].
   
   external hhlmuc_add_clause_with_id : hhlmuc_solver -> hhlmuc_lit list -> bool * Some int = "hhlmuc_add_clause_with_id" 

*/
extern "C" value hhlmuc_add_clause_with_id(value solver_in, value clause_in)
{	

  // Declare parameters 
  CAMLparam2(solver_in, clause_in);
  CAMLlocal2(head, res);

  // Allocate for OCaml pair 
  res = caml_alloc(2, 0);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  head = clause_in;

  // Clause to be asserted
  vec<Lit> lits;
  lits.clear();

#ifdef DEBUG
  fprintf(stderr, "Asserting interesting clause ");
#endif

  // Iterate list of literals
  while (head != Val_emptylist) 
    {

      // Get head element of list 
      value lit_in = Field(head, 0);

      // Get MiniSat literal from value
      Lit* lit = (Lit*) Data_custom_val(lit_in);

#ifdef DEBUG
      fprintf(stderr, "%s%d ", 
	      sign(*lit) ? "" : "~",
	      var(*lit));
#endif

      // Add literal to clause 
      lits.push(*lit);

      // Continue with tail of list
      head = Field(head, 1);

    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Get uid before adding clause 
  int last_uid = Clause::GetLastUid();

#ifdef DEBUG
  fprintf(stderr, "GetLastUid = %d\n", last_uid);
#endif

  // Add clause to solver, mark as interesting 
  if (solver->addClause_(lits, true))
    {

      // Get uid after adding clause 
      int clause_uid = Clause::GetLastUid();

#ifdef DEBUG
      fprintf(stderr, "GetLastUid = %d\n", clause_uid);
#endif

      if (last_uid == clause_uid)
	{

	  // Clause set is not immediately unsatisfiable
	  Store_field(res, 0, Val_true);

	  // Clause was not added, does not have a uid
	  Store_field(res, 1, Val_none);

	  // Return pair (true, None) as result 
	  CAMLreturn(res);

	}
      else
	{

	  // Clause set is not immediately unsatisfiable
	  Store_field(res, 0, Val_true);

	  // Clause was added with uid
	  Store_field(res, 1, Val_some(Val_int(clause_uid)));

	  // Return pair (true, Some clause_uid) as result 
	  CAMLreturn(res);

	}
      
    }
  else
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable with added clause\n");
#endif

      // Clause set is immediately unsatisfiable
      Store_field(res, 0, Val_false);
      
      // Clause was not added, does not have a uid
      Store_field(res, 1, Val_none);
      
      // Immediately unsatisfiable with added clause
      CAMLreturn (res);

    }

}


/* Test the given clause set for satisfiability. Return true if
   satisfiable, false if unsatisfiable.

   external hhlmuc_solve : hhlmuc_solver -> bool = "hhlmuc_solve" 

*/
extern "C" value hhlmuc_solve(value solver_in)
{
    
  // Declare parameters 
  CAMLparam1(solver_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

#ifdef DEBUG
  fprintf(stderr, "Solving without assumptions\n");
#endif

#ifdef DEBUG
  fprintf(stderr, "Previous size of model: %d, updating to %d\n",
	  (int) Field(solver_in, 1),
	  solver->nVars());
#endif

  // Update number of variables
  Store_field(solver_in, 1, (value) solver->nVars()); 

  // Run MiniSat
  bool res = solver->solve();

  // Return result
  CAMLreturn(Val_bool(res));
}


/* Test the given clause set for satisfiability when the given
   literals are to be made true. Return l_True = 0 if the clause set
   is satisfiable with assumptions, l_Undef = 2 if the clause set is
   immediately unsatisfiable without assumptions and l_False = 1 if
   the clause set is unsatisfiable with assumptions.

   external hhlmuc_solve_assumptions : hhlmuc_solver -> hhlmuc_lit list -> lbool = "hhlmuc_solve_assumptions" 

*/
extern "C" value hhlmuc_solve_assumptions(value solver_in, value assumptions_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, assumptions_in);
  CAMLlocal1(head);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  head = assumptions_in;

  // Assumptions for solving
  vec<Lit> lits;
  lits.clear();

  // Only if satisfiable after simplifications
  if (solver->simplify())
    {

#ifdef DEBUG
      fprintf(stderr, "Assuming ");
#endif

      // Iterate list of literals
      while (head != Val_emptylist) 
	{
	  
	  // Get head element of list 
	  value lit_in = Field(head, 0);
	  
	  // Get MiniSat literal from value
	  Lit* lit = (Lit*) Data_custom_val(lit_in);
	  
#ifdef DEBUG
	  fprintf(stderr, "%s%d ", 
		  sign(*lit) ? "" : "~",
		  var(*lit));
#endif
	  
	  // Add literal to assumptions
	  lits.push(*lit);
	  
	  // Continue with tail of list
	  head = Field(head, 1);
	  
	}
      
#ifdef DEBUG
      fprintf(stderr, "\n");
#endif

#ifdef DEBUG
      fprintf(stderr, "Previous size of model: %d, updating to %d\n",
	      (int) Field(solver_in, 1),
	      solver->nVars());
#endif
      
      // Update number of variables
      Store_field(solver_in, 1, (value) solver->nVars()); 
      
      // Solve with literal assumptions
      if (solver->solve(lits))
	{
	  
#ifdef DEBUG
	  fprintf(stderr, "Satisfiable under assumptions\n");
#endif

	  // Satisfiable under assumptions
	  CAMLreturn(Val_l_True);

	}

      else
	{

#ifdef DEBUG
	  fprintf(stderr, "Unsatisfiable under assumptions\n");
#endif

	  // Unsatisfiable under assumptions
	  CAMLreturn(Val_l_False);

	}

    }

  else  
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable without assumptions\n");
#endif

      // Unsatisfiable without assumptions
      CAMLreturn(Val_l_Undef);
    }
	
}

/* Test the given clause set for satisfiability in a limited search
   when the given literals are to be made true.

   This is similar to hhlmuc_solve_assumptions above, but the search
   is limited to the given number of conflicts. 

   Return None if satisfiability could not be determined under the
   conflict limit. Return Some l_True = Some 0 if the clause set is
   satisfiable with assumptions, Some l_Undef = Some 2 if the clause
   set is immediately unsatisfiable without assumptions and Some
   l_False = Some 1 if the clause set is unsatisfiable with
   assumptions.

   external hhlmuc_fast_solve : hhlmuc_solver -> hhlmuc_lit list -> int -> lbool option = "hhlmuc_fast_solve"

*/
extern "C" value hhlmuc_fast_solve(value solver_in, value assumptions_in, value max_conflicts_in)
{

  // Declare parameters 
  CAMLparam3 (solver_in, assumptions_in, max_conflicts_in);
  CAMLlocal1(head);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  int max_conflicts = Int_val(max_conflicts_in);

  head = assumptions_in;

  // Assumptions for solving
  vec<Lit> lits;
  lits.clear();

  // Only if satisfiable after simplifications
  if (solver->simplify())
    {

#ifdef DEBUG
      fprintf(stderr, "Assuming ");
#endif

      // Iterate list of literals
      while (head != Val_emptylist) 
	{
	  
	  // Get head element of list 
	  value lit_in = Field(head, 0);
	  
	  // Get MiniSat literal from value
	  Lit* lit = (Lit*) Data_custom_val(lit_in);
	  
#ifdef DEBUG
	  fprintf(stderr, "%s%d ", 
		  sign(*lit) ? "" : "~",
		  var(*lit));
#endif
	  
	  // Add literal to assumptions
	  lits.push(*lit);
	  
	  // Continue with tail of list
	  head = Field(head, 1);
	  
	}
      
#ifdef DEBUG
      fprintf(stderr, "\n");

      if (!lits.size()) fprintf(stderr, "No assumptions\n");
#endif

      // Set budget for number of conflicts
      solver->setConfBudget(max_conflicts);

#ifdef DEBUG
      fprintf(stderr, "Previous size of model: %d, updating to %d\n",
	      (int) Field(solver_in, 1),
	      solver->nVars());
#endif
      
      // Update number of variables
      Store_field(solver_in, 1, (value) solver->nVars()); 
      
      // Solve with literal assumptions 
      lbool res = solver->solveLimited(lits);

      if (res == l_True) 
	{
#ifdef DEBUG
	  fprintf(stderr, "Satisfiable with assumptions (fast solve)\n");
#endif

	  CAMLreturn(Val_some(Val_l_True));
	}

      if (res == l_False) 
	{
#ifdef DEBUG
	  fprintf(stderr, "Unsatisfiable with assumptions (fast solve)\n");
#endif

	  CAMLreturn(Val_some(Val_l_True));
	}

      if (res == l_Undef) 
	{
#ifdef DEBUG
	  fprintf(stderr, "Unknown (fast solve)\n");
#endif

	  CAMLreturn(Val_none);
	}
      
    }

  else
    {

#ifdef DEBUG
      fprintf(stderr, "Unsatisfiable without assumptions (fast solve)\n");
#endif

      // Unsatisfiable without assumptions
      CAMLreturn(Val_some(Val_l_Undef));
      
    }

}


/* Return an unsatisfiable core 

   external hhlmuc_unsat_core : hhlmuc_solver -> int list = "hhlmuc_unsat_core"
 */
extern "C" value hhlmuc_unsat_core(value solver_in)
{

#ifdef DEBUG
  fprintf(stderr, "Entering hhlmuc_model_value\n");
#endif

  // Declare parameters 
  CAMLparam1 (solver_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  // Initialise return value to empty list
  CAMLlocal2(res, cons);
  res = Val_emptylist;
  
  // Vector of Uids for unsat core
  vec<uint32_t> vecUids;

  // Get unsat core from solver
  solver->GetUnsatCore(vecUids);
  
#ifdef DEBUG
  fprintf(stderr, "Clauses in unsat core: ");
#endif
  
  // Iterate clauses in unsat core backwards to preserve order
  for (int nInd = vecUids.size() - 1; nInd >= 0; --nInd)
    {

#ifdef DEBUG
      fprintf(stderr, "%d ", (int) vecUids[nInd]);
#endif

      // Allocate for new list elements
      cons = caml_alloc(2, 0);

      // Head of list is uid of clause in unsat core
      Store_field(cons, 0, Val_int((int) vecUids[nInd]));

      // Tail of list is previous list 
      Store_field(cons, 1, res);

      // Continue with constructed list 
      res = cons;
      
    }

#ifdef DEBUG
  fprintf(stderr, "\n");
#endif

  // Return list
  CAMLreturn(res);

}


/* Return the truth value of the literal in the current model: Some
    true if the literal is true, Some false if the literal is false
    and None if the literal value is undefined

  external hhlmuc_model_value : hhlmuc_solver -> hhlmuc_lit -> int = "hhlmuc_model_value"

*/
extern "C" value hhlmuc_model_value (value solver_in, value lit_in)
{

#ifdef DEBUG
  fprintf(stderr, "Entering hhlmuc_model_value\n");
#endif

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  Lit* lit = (Lit*) Data_custom_val(lit_in);

#ifdef DEBUG
  if (solver == NULL) fprintf(stderr, "solver is NULL\n", var(*lit));
  if (lit == NULL) fprintf(stderr, "lit is NULL\n", var(*lit));
#endif
      
  // Variable not present in last solve call?
  if (var(*lit) >= (int) Field(solver_in, 1))
    {

#ifdef DEBUG
      fprintf(stderr, "Variable %d not in model, set to l_Undef\n", var(*lit));
#endif
      
      // Return undefined without reading from model
      CAMLreturn(Val_l_Undef);
      
    }
  else
    {

#ifdef DEBUG
      fprintf(stderr, "Reading model value of variable %d\n", var(*lit));
#endif
      
      lbool val = solver->modelValue(*lit);

#ifdef DEBUG
      fprintf(stderr, "Model value %s%d: %s (%d)\n", 
	      sign(*lit) ? "" : "~",
	      var(*lit),
	      val == l_True ? "l_True" : (val == l_False ? 
					  "l_False" : 
					  "l_Undef"),
	      toInt(val));
#endif

      if (val == l_True) 
	{ 
	  CAMLreturn(Val_l_True);
	}
      else if (val == l_False) 
	{ 
	  CAMLreturn(Val_l_False);
	}
      else
	{
	  CAMLreturn(Val_l_Undef);
	}
      
    }

}

/* Return the propositional variable in the literal

   external hhlmuc_lit_var : hhlmuc_solver -> hhlmuc_lit -> int = "hhlmuc_lit_to_int"

*/
  extern "C" value hhlmuc_lit_var(value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  Lit* lit = (Lit*) Data_custom_val(lit_in);
  
  value res = Val_int(var(*lit));
  CAMLreturn(res);

}


/* Return the sign of the literal, true for a positive and false
   for a negative literal 
   
   external hhlmuc_lit_sign : hhlmuc_solver -> hhlmuc_lit -> bool = "hhlmuc_lit_to_int"
    
*/
extern "C" value hhlmuc_lit_sign(value solver_in, value lit_in)
{

  // Declare parameters 
  CAMLparam2 (solver_in, lit_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  Lit* lit = (Lit*) Data_custom_val(lit_in);
  
  value res = Val_bool(sign(*lit));
  CAMLreturn(res);

}


/* Return the number of propositional variables

  external hhlmuc_stat_vars : hhlmuc_solver -> int = "hhlmuc_stat_vars" 

*/
extern "C" value hhlmuc_stat_vars(value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  // Read number of variables 
  int vars = solver->nVars();

  // Return integer
  value res = Val_int(vars);
  CAMLreturn(res);

}


/* Return the number of clauses
  
  external hhlmuc_stat_clauses : hhlmuc_solver -> int = "hhlmuc_stat_clauses" 
*/
extern "C" value hhlmuc_stat_clauses(value solver_in)
{

  // Declare parameters 
  CAMLparam1 (solver_in);

  Solver* solver = (Solver*) Field(solver_in, 0);
  // SimpSolver* solver = (SimpSolver*) Field(solver_in, 0);

  // Read number of clauses 
  int vars = solver->nClauses();

  // Return integer
  value res = Val_int(vars);
  CAMLreturn(res);

}
