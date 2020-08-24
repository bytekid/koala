

#include "lglib.h"
//#include "solver.h" 
#include "vec.h" //from minisat
#include <assert.h>
#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>


typedef int  bool;
static const bool  true      = 1;
static const bool  false     = 0;

typedef char               lbool;
static const lbool l_Undef   =  0;
static const lbool l_True    =  1;
static const lbool l_False   = -1;
// returned when an error occured (should never happen..)
static const lbool l_Err     = -13;



struct solver_model {
    LGL  *lgl;
    veci model;
  //simplification solver     
    bool sim;
}; 

typedef struct solver_model solver;


int model_var (int lit)
{
  return (abs(lit)-1);//we count from 0 in model and vars a counted from 1
}

int mvar_to_var (int var)
{return var+1;}//var = model var +1


int lit_sign (int lit)
  //sign true if it is a negative lit
{return (lit < 0);}

int model_size (solver* s) 
{return  veci_size(&s->model);}


value C_create_solver(value is_sim_In)
{
  CAMLparam1(is_sim_In);

//use the same solver for simplifications, ignore is_sim_In
  solver* s = (solver*)safe_malloc(sizeof(solver));
  bool is_sim = Bool_val(is_sim_In);
  if(is_sim)
    {
      s->sim = true;
    }
  else
    {
      s->sim = false;
    }

  s->lgl = lglinit ();
  veci_new(&s->model);


  //DEBUG 
  // FILE *trace_file;
  // trace_file = fopen("lgl.trace","w");
  //  lglwtrapi (s->lgl,trace_file);
  //

  lglsetopt(s->lgl,"verbose",0);
  lglsetopt(s->lgl,"phase",0);
    //scdpd_miter_full-range.cnf

    //minisat: MC1 bound 3 UNSAT after 29.484s BMC1 bound 4 UNSAT after 73.016s BMC1 bound 5 UNSAT after 181.933s
    //phase -1:BMC1 bound 3 UNSAT after 47.318s BMC1 bound 4 UNSAT after 98.067s BMC1 bound 5 UNSAT after 152.924s BMC1 bound 6 UNSAT after 221
    //phase 0: BMC1 bound 3 UNSAT after 25.761s BMC1 bound 4 UNSAT after 70.702s BMC1 bound 5 UNSAT after 139.671s BMC1 bound 6 UNSAT after 181.668s BMC1 bound 7 UNSAT after 214.556s
   // phase 0: BMC1 bound 2 UNSAT after 77.202s
  // 

  lglsetopt(s->lgl,"flipping",0);
  value val = alloc(1, Abstract_tag);
  Field(val,0) = (value) s; 
  CAMLreturn(val);
}

//value C_solver_reset(value solver_In)
//{
//  CAMLparam1(solver_In);
//  solver * s = (solver *)Field(solver_In, 0);
  
//}

//add_var       : solver -> var_id -> unit = "C_add_var"

value C_add_var(value solver_In, value var_In)
{// do nothing for lgl
  CAMLparam2 (solver_In,var_In);
   solver * s = (solver *)Field(solver_In, 0);
   int var_id = Int_val(var_In);

   int max_var = lglmaxvar (s->lgl);
  //  fprintf(stderr, "var_id = %i, max_var_before = %i ", var_id, max_var);
  int i=0;
  for (i = 0; i < (var_id - max_var); i++)
    {
      //lgl 
      int next_var= lglincvar (s->lgl);
      lglfreeze (s->lgl,next_var);

      //model
      veci_push(&s->model,l_False);
    }
  //  {solver_setnvars(solver,var_id+1);
  //if (solver->size <= var_id)
  //  {solver_setnvars(solver,var_id+1);}
  CAMLreturn(Val_unit);
}


value C_create_lit(value v, value solver_In,value sign_In)
{
  CAMLparam3(v, solver_In,sign_In);

  solver* s = (solver *)Field(solver_In, 0);
  int  var_id = Int_val(v);
  if (var_id <= 0)
    {fprintf(stderr,"Var_id = %i \n", var_id);
     fflush(stderr);
     exit(EXIT_FAILURE); 
    }
  bool sign = Bool_val(sign_In);

  int max_var = lglmaxvar (s->lgl);
  //  fprintf(stderr, "var_id = %i, max_var_before = %i ", var_id, max_var);
  int i=0;
  for (i = 0; i < (var_id - max_var); i++)
    {
      //lgl 
      int next_var= lglincvar (s->lgl);
      lglfreeze (s->lgl,next_var);
      
      //model
      veci_push(&s->model,l_False);
    }
  
  //sover->size is the number of defined vars 
  // 
  //  {solver_setnvars(solver,var_id+2);}
  // printf("  Var_id: %i \n", var_id);
  // printf(" create_lit (Var_id:) solver->size =%i \n", solver->size);
  // fflush(stdout);
  // if (solver->size <= var_id)
  // {solver_setnvars(solver,var_id+1);}

  int lgl_lit = (sign ? var_id : -var_id);
  CAMLreturn(Val_int(lgl_lit));
}


value C_important_lit (value solver_In, value lit_in)
{
    CAMLparam2 (solver_In, lit_in);
    CAMLreturn(Val_unit);
}

value C_add_clause(value clause_In, value solver_In)
{	
    CAMLparam2 (clause_In, solver_In);

    solver * s = (solver *)Field(solver_In, 0);
	
    int size = Wosize_val(clause_In);
    //  int arr[size];
    int i, lit ;
 
    for (i = 0; i < size; i++)
      {
      lit = Int_val(Field(clause_In, i));
      lgladd (s->lgl, lit);
      //we need to freeze all lits since they may occur in future clauses/assumptions
      //we assume all lits are added and frozen already
      //      lglfreeze (solver, lit);
      //      fprintf(stderr,"%i ",lit);   
      }
    lgladd (s->lgl,0); //end of clause
    //fprintf(stderr,"%i\n",0);   

    if (lglinconsistent(s->lgl) != 0){
      // fprintf(stdout,"Inconsistent solver \n");
	CAMLreturn (Val_bool(false));
    }
    //    fprintf(stdout,"Added clause\n ");
    CAMLreturn (Val_bool(true));
}


/*
value C_get_lit_val (value solver_In, value lit_In, value sign_In)
{
  //    CAMLparam2(solver_In, lit_In);
  CAMLparam3(solver_In,lit_In,sign_In);

  SolverM * solver_mem = (SolverM *)Field(solver_In, 0);
  solver  * solver = solver_mem -> solver_ptr;
  bool sign = Bool_val(sign_In);
  int var = lit_var(Int_val(lit_In));


    int* model = veci_begin(&solver->model);
    int model_size = veci_size(&solver->model);
    //  lbool* model = solver->assigns;
    //	fprintf(stdout, "model_size=%i, var_id = %i \n",model_size,var);
    if (var >= model_size)
      {
	fprintf(stderr, "ERROR C_get_lit_val: var has not been defined model_size=%i, var_id = %i \n",model_size,var);
	fflush(stderr);
	fprintf(stdout, "ERROR C_get_lit_val: var has not been defined  \n");
	fflush(stdout);
	exit(EXIT_FAILURE); 
    }


  lbool var_val = model[var];

  if (var_val == l_True)
    {
      if(sign == true)
	{
	  CAMLreturn(Val_int(1));
	}
      
      else
	
	  {
	    CAMLreturn(Val_int(0));
	  }
    }
  
  else 
    if (var_val == l_False)      
      {	
	if(sign == true)
	  {
	    CAMLreturn(Val_int(0));
	  }
	else
	  {
	    CAMLreturn(Val_int(1));
	  }
	
      }
    else      
      if (var_val == l_Undef)
	{
	  CAMLreturn(Val_int(-1));
	}
      else
	{
	  CAMLreturn(Val_int(-2));
	}  
}

*/


value C_get_lit_val (value solver_In, value lit_In)
{
     CAMLparam2(solver_In, lit_In);
     // CAMLparam3(solver_In,lit_In,sign_In);

  solver * s = (solver *)Field(solver_In, 0);
  int lit = Int_val(lit_In);
  int mvar = model_var(lit);
  int* model = veci_begin(&s->model);
  int msize = model_size(s);
  bool sign = lit_sign (lit);

  if (mvar >= msize)
      {
	fprintf(stderr, "ERROR C_get_lit_val: var has not been defined model_size=%i, var_id = %i \n",msize,mvar);
	fflush(stderr);
	fprintf(stdout, "ERROR C_get_lit_val: var has not been defined  \n");
	fflush(stdout);
	exit(EXIT_FAILURE); 
    }


  lbool var_val = model[mvar];

  //fprintf(stderr, "model_size=%i, lit=%i, mvar = %i, sign=%i, var_val=%i \n",msize,lit,mvar,sign,var_val);  

  if (var_val == l_True)
    {
      //     if(sign == true)
      if (!sign)
	{
	  CAMLreturn(Val_int(l_True));
	}
      
      else	
	  {
	    CAMLreturn(Val_int(l_False));
	  }
    }
  
  else 
     if (var_val == l_False)      
       {	
	 if(!sign)
	   {
	     CAMLreturn(Val_int(l_False));
	   }
	 else
	   {
	     CAMLreturn(Val_int(l_True));
	   }
	
       }
     else      
       if (var_val == l_Undef)
	 {
	   CAMLreturn(Val_int(l_Undef));
	 }
       else
	 {
	   CAMLreturn(Val_int(l_Err)); // should not happen
	 }  
}

/*
  // lbool var_val = model[var];
  // int max_var = lglmaxvar (s->lgl);
  // if (abs(lit) > max_var) 
  // { fprintf(stderr,"Lit %i is greater than max_var=%i\n", lit, max_var);
  //   exit(EXIT_FAILURE); 
  //  }
  // fprintf(stderr,"lit= %i,max_var=%i\n",lit,max_var);
  // if (lglinconsistent(solver) != 0){
  //  fprintf(stdout,"Deref from inconsistent solver \n");
  // }

  // can be very expensive to check sat each time! ?
  //  if (lglsat(solver) == LGL_SATISFIABLE) 
    {
      int res = lglderef (solver,lit);
  // lglderef return values which coincide with l_True = 1, l_False = -1 , l_Undef =0
  // in case the var was not defined returns a default value (l_False )
      CAMLreturn(Val_int(res));
    }
  else // unsat make a default value l_False 
    {CAMLreturn(Val_int(l_False));}
}
*/

//currently reset is implemented only in PicoSAT
value C_solve(value solver_In, value reset)
{
  CAMLparam2(solver_In,reset);

    solver * s = (solver *)Field(solver_In, 0);
    
      
    // fprintf(stdout,"Solver res: %i\n",res);
	  
    if (lglinconsistent (s->lgl))
      //unsat
      CAMLreturn(Val_bool(false));
 
    int res = lglsat(s->lgl);
    // fprintf(stdout,"After Solve:\n");
    // fflush(stdout);
    if (res == LGL_UNSATISFIABLE)
      CAMLreturn(Val_bool(false));
  
    if (res == LGL_SATISFIABLE)
      {
	//	if (lglchanged(s->lgl))
	  {
	    //copy model
	    int i;
	    int msize = model_size(s);
	    veci_resize(&s->model,0);
	    //	    fprintf(stderr, "Model\n");
	    for (i = 0; i < msize; i++) 	  
	         {

		int var = mvar_to_var(i);
		int var_val = lglderef(s->lgl,var);
		//DEBUG
		//	int max_var = lglmaxvar (s->lgl);
		//	fprintf(stderr, "v%i= %i, ", var,var_val);
	
		veci_push(&s->model,var_val);
              }
	    lglsetphases(s->lgl);
	    //   fprintf(stderr, "Model\n");
	  }
	CAMLreturn(Val_bool(true));    
      }
  
    {fprintf(stderr,"Lingeling: unknown solver result: %i \n", res);
      fflush(stderr);
      exit(EXIT_FAILURE); 
    }
}


//currently reset is implemented only in PicoSAT
value C_solve_assumptions(value solver_In, value assumptions,value reset)
{
  CAMLparam3 (solver_In, assumptions,reset);
  solver * s = (solver *)Field(solver_In, 0);
  int i , lit ;
  int size = Wosize_val(assumptions); 	
  for (i = 0; i < size; i++)
    {
      lit = Int_val( Field(assumptions, i) );		
	//	fprintf(stderr,"assume %i\n",lit);
      lglassume (s->lgl, lit); //assume
	lglfreeze (s->lgl, lit); //freeze
	
    }
  
  if (lglinconsistent (s->lgl))
    //unsat without assumptions
    CAMLreturn(Val_int(l_Undef));
 
  int res = lglsat(s->lgl);
  
  if (res == LGL_UNSATISFIABLE)
    CAMLreturn(Val_int(l_False));
  
    if (res == LGL_SATISFIABLE)
      {
	//	if (lglchanged(s->lgl))
	  {
	    //copy model
	    int i;
	    int msize = model_size(s);
	    veci_resize(&s->model,0);
	    // fprintf(stderr,"Model\n");
	    for (i = 0; i < msize; i++) 
	      {


		int var = mvar_to_var(i);
		int var_val = lglderef(s->lgl,var);
		//DEBUG
		//		int max_var = lglmaxvar (s->lgl);
		//	fprintf(stderr, "max_var = %i, var=%i, var_val = %i\n", max_var, var,var_val);
		//		fprintf(stderr, "v%i= %i\n ", var,var_val);	
		veci_push(&s->model,var_val);

              }
	    lglsetphases(s->lgl);
	  }
	CAMLreturn(Val_bool(l_True));    
      }
  
    fprintf(stderr,"Lingeling: unknown solver result: %i \n", res);
    fflush(stderr);
    exit(EXIT_FAILURE); 
}


   
value C_fast_solve(value solver_In, value assumptions)
{
  CAMLparam2 (solver_In, assumptions);
   solver * s = (solver *)Field(solver_In, 0);
   int i , lit ;
   int size = Wosize_val(assumptions);
  
    //    printf ("Debug: Change C_fast_solve: remove solved check!\n ");
    //	    fflush(stdout);
    //     lbool   solver_out_without_ass = solver_solve(solver,0,0);
    // if (solver_out_without_ass == l_True)
    //  {	

   if (lglinconsistent (s->lgl))
    //unsat without assumptions
     CAMLreturn(Val_int(l_Undef));
 
	
   for (i = 0; i < size; i++)
     {
       lit = Int_val( Field(assumptions, i) );		
       //	fprintf(stderr,"assume %i\n",lit);
       lglassume (s->lgl, lit); //assume
       lglfreeze (s->lgl, lit); //freeze
     }

   //    int old_clim = lglgetopt (solver, "clim");
    // unit porpagation: conflict limit 0
   //   lglsetopt (solver, "clim", 0);
   // int res = lglsat(solver);
   //  lglsetopt (solver, "clim", old_clim);
   int res= lglsimp(s->lgl,0);


   if ((res == LGL_SATISFIABLE) || (res == LGL_UNKNOWN))
      //sat under assumprions or unknown
      CAMLreturn(Val_int(l_True));

    if (res == LGL_UNSATISFIABLE)
      //unsat under assumprions
      CAMLreturn(Val_int(l_False));
 
    {fprintf(stderr,"Lingeling: unknown solver result: %i \n", res);
      fflush(stderr);
      exit(EXIT_FAILURE); 
    }
}
   




/* value C_add_clause(value clause_In, value solver_In)
{	
    CAMLparam2 (clause_In, solver_In);

    SolverM * solver_mem   = (SolverM *)Field(solver_In, 0);
    solver * solver  = solver_mem -> solver_ptr;
    veci   * lits = solver_mem -> vector_ptr;
	
    int size = Wosize_val(clause_In);
    //  int arr[size];
    int i , temp ;
    veci_resize(lits,0);
    
    for (i = 0; i < size; i++)
    {
      temp = Int_val( Field(clause_In, i) );		
      veci_push(lits, temp);
    }
	
	
    lit* begin = (lit *)veci_begin(lits);
    int n = veci_size(lits);
    if (!solver_addclause(solver, begin, begin+n)){
	
	CAMLreturn (Val_bool(0));
    }
 
    CAMLreturn (Val_bool(1));
}

*/

 /*
value C_get_number(value solver_In)
{
    CAMLparam1(solver_In);
    SolverM * s = (SolverM *)Field(solver_In, 0);
    solver * s1 =s -> solver_ptr;
    int i = solver_nvars(s1);
    int m  = solver_nclauses(s1);
    CAMLreturn ( Val_unit ); 
}


value C_print_array(value clause_In)
{
    CAMLparam1(clause_In);
    int size = Wosize_val(clause_In);
    int arr[size];
    
    int i , temp ;
    for (i = 0; i < size; i++)
    {
	temp = Int_val( Field(clause_In, i) );
	if (temp > 0) 
	    arr[i] = temp << 1;
	else
	    arr[i] = temp * (-2) + 1;	
    }

    CAMLreturn ( Val_unit ); 
}
 */


 //end extern "C"
