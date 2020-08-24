/*----------------------------------------------------------------------(C)-*/
/* Copyright (C) 2006-2010 Konstantin Korovin and The University of Manchester. 
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
   along with iProver.  If not, see <http://www.gnu.org/licenses/>.         */
/*----------------------------------------------------------------------[C]-*/

#include <stdlib.h>

//#define c_l_True 1
//#define c_l_False 0
//#define c_l_Undef -1

extern "C" {
#define True 1
#define False 0
#define Undef -1
#define Unsat 0
#define Sat 1
#define UnsatAssump -1
#define Unknown -2

typedef void *lit_c ;
typedef void *solver_c;
typedef int Var;
}

extern "C" int temp (void); 

extern "C" solver_c solver_new(void);

extern "C" void addVar (solver_c s,Var var_id);

//lit_c lit_var (Var var, bool polarity);
extern "C" lit_c lit_var (Var var_id, int polarity);

//----------------------------------------------------------
// for adding clause we need to 
// init_clause, add_lit_clause, add_clause
//----------------------------------------------------------
extern "C" void init_clause (solver_c s);
extern "C" void add_lit_clause (solver_c s, lit_c lit);

//bool add_clause (solver_c s);
extern "C" int add_clause (solver_c s);
//----------------------------------------------------------


//bool solve (solver_c s);
extern "C" int solve (solver_c s);

//----------------------------------------------------------
// for (fast) solving under assumption we need to
// init_assumptions, add_lit_assumption,  solve_assumptions
//----------------------------------------------------------
//out:  Unsat without assumpt, UnsatAssump under assumpt, Sat under Assumpt

extern "C" void init_assumptions (solver_c s);
extern "C" void add_lit_assumption (solver_c s, lit_c lit);
//bool solve_assumptions (solver_c s);
extern "C" int solve_assumptions (solver_c s);

//bool fast_solve_assumptions (solver_c s);
//c_l_True, c_l_False, c_l_Undef
extern "C" int fast_solve_assumptions (solver_c s);
//----------------------------------------------------------

extern "C" int lit_model_val (solver_c s, lit_c lit);
