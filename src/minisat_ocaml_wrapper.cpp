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

extern "C"{

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

#include "minisat_c_wrapper.hpp"
}
//#include "minisat_ocaml_wrapper.h"

//typedef void *lit_c ;
//typedef void *solver_c;
//
//#define True 1
//#define False 0
//#define Undef -1
//#define Unsat 0
//#define Sat 1
//#define UnsatAssumpt -1
//#define Unknown -2


extern "C" value C_create_solver(value unit)
{
  CAMLparam1 (unit);
  solver_c s =  solver_new ();
  value val = alloc(1, Abstract_tag);
  Field(val,0) = (value) s; 
  CAMLreturn(val);
}

extern "C" value C_add_var (value solver_In, value var_id_In)
{  
  CAMLparam2 (solver_In, var_id_In);
  solver_c   s = (solver_c) Field(solver_In, 0);
  int var_id = Int_val(var_id_In);
  addVar (s,var_id);
  CAMLreturn(Val_unit);

}


extern "C" value C_create_lit(value v, value solver_In,value sign_In)
{
  CAMLparam3(v, solver_In,sign_In);
  solver_c   s = (solver_c) Field(solver_In, 0);
  int var_id = Int_val(v);
  //  printf("minisat_ocaml_wrapper: new lit var id: %i\n",var_id);
  //assume true == True, false == False
  int sign = Bool_val(sign_In);
  addVar (s,var_id);
  lit_c lit = lit_var (var_id, sign);
  value val = alloc(1, Abstract_tag);
  Field(val,0) = (value) lit; 
  CAMLreturn(val);
}

extern "C" value C_important_lit (value solver_In, value lit_in)
{
    CAMLparam2 (solver_In, lit_in);
    CAMLreturn(Val_unit);
}

//swap clause_In solver_In
extern "C" value C_add_clause(value clause_In, value solver_In)
{	
    CAMLparam2 (clause_In, solver_In);
    solver_c s = (solver_c) Field(solver_In, 0);
    int size = Wosize_val(clause_In);
    init_clause (s);
    int i;
    for (i = 0; i < size; i++)
      {
	value caml_val =  Field(clause_In, i);
	lit_c lit = (lit_c) Field(caml_val,0);
	add_lit_clause(s, lit);
      }
    if (add_clause(s))      
      {
	CAMLreturn (Val_bool(1));
      }
    else 
      {CAMLreturn (Val_bool(0));}
    
}


//currently reset is implemented only in PicoSAT
extern "C" value C_solve(value solver_In, value reset)
{
  CAMLparam2(solver_In,reset);
    solver_c s = (solver_c) Field(solver_In, 0);
    int result = solve(s);
    CAMLreturn(Val_bool(result));
}

//currently reset is implemented only in PicoSAT
extern "C" value C_solve_assumptions(value solver_In, value assumptions, value reset)
{
  CAMLparam3 (solver_In, assumptions,reset);
  solver_c s = (solver_c) Field(solver_In, 0);
  int size = Wosize_val(assumptions);
  init_assumptions (s);
  int i;
  for (i = 0; i < size; i++)
    {
      value caml_val =  Field(assumptions, i);
      lit_c lit = (lit_c) Field(caml_val,0);
      add_lit_assumption (s, lit);
    }
  int result = solve_assumptions (s);
  CAMLreturn(Val_int(result));
}

// Change to real fast solve
extern "C" value C_fast_solve(value solver_In, value assumptions)
{
  CAMLparam2 (solver_In, assumptions);
  solver_c s = (solver_c) Field(solver_In, 0);
  int size = Wosize_val(assumptions);
  init_clause (s);
  int i;
  for (i = 0; i < size; i++)
    {
      value caml_val =  Field(assumptions, i);
      lit_c lit = (lit_c) Field(caml_val,0);
      add_lit_assumption (s, lit);
    }
  int result = fast_solve_assumptions (s);
  CAMLreturn(Val_int(result));
}

  
//add checks
extern "C" value C_get_lit_val (value solver_In, value lit_In)
{
  CAMLparam2(solver_In,lit_In);
  solver_c s = (solver_c) Field(solver_In, 0);
  lit_c lit = (lit_c) Field(lit_In, 0);
  int result = lit_model_val (s,lit);
  CAMLreturn(Val_int(result));
}
