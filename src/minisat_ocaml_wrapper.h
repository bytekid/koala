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

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

extern "C" value C_create_solver(value unit);
extern "C" value C_create_lit(value v, value solver_In,value sign_In);
extern "C" value C_add_clause(value clause_In, value solver_In);
extern "C" value C_solve(value solver_In);
extern "C" value C_solve_assumptions(value solver_In, value assumptions);
extern "C" value C_fast_solve(value solver_In, value assumptions);
extern "C" value C_get_lit_val (value solver_In, value lit_In)
