/*----------------------------------------------------------------------(C)-*/
/* Copyright (C) 2006-2016 Konstantin Korovin and The University of Manchester. 
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

#include "Solver.hpp"

extern "C"{
const int l_true  = toInt(l_True);
const int l_false = toInt(l_False);
const int l_undef = toInt(l_Undef);


  //#define c_l_True 1
  //#define c_l_False 0

#define True 1
#define False 0
#define Undef -1
#define Unsat 0
#define Sat 1
#define UnsatAssumpt -1
#define Unknown -2



// type Var   is int
typedef void *lit_c;
typedef void *solver_c;
}

//const Lit lit_True  (0, false);
//const Lit lit_False (0, true); 


class Solver_ext : public Solver { 
public:
  vec<Lit> lits;
  int propagation_limit;
  int propagation_counter;
  Solver_ext  (): Solver() {
    propagation_limit=10000000;
    propagation_counter=0;
    //   polarity_mode = polarity_false;
    //remove_satisfied = false;
    //    expensive_ccmin  = false; //rises seg fault...
    /*    newVar(true,false); 
	  addClause(lit_True); */
  };
    //    ~solver_ext () 

//KK fast solve (unit propagation...)
  Clause*  limited_propagate(void);
  lbool fast_search(int nof_conflicts, int nof_learnts);
  int fast_solve(const vec<Lit>& assumps);
};


/*______________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/

Clause* Solver_ext::limited_propagate()
{
    Clause* confl     = NULL;
    int     num_props = 0;

    while ((qhead < trail.size()) && (propagation_counter < propagation_limit))
      {
	propagation_counter++;	
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Clause*>&  ws  = watches[toInt(p)];
        Clause         **i, **j, **end;
        num_props++;

        for (i = j = (Clause**)ws, end = i + ws.size();  i != end;){
            Clause& c = **i++;

            // Make sure the false literal is data[1]:
            Lit false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            Lit first = c[0];
            if (value(first) == l_True){
                *j++ = &c;
            }else{
                // Look for new watch:
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[toInt(~c[1])].push(&c);
                        goto FoundWatch; }

                // Did not find watch -- clause is unit under assignment:
                *j++ = &c;
                if (value(first) == l_False){
                    confl = &c;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                }else
                    uncheckedEnqueue(first, &c);
            }
        FoundWatch:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


lbool Solver_ext::fast_search(int nof_conflicts, int nof_learnts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;

    starts++;

    bool first = true;

    for (;;){
        Clause* confl = limited_propagate();
        if (confl != NULL){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            first = false;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);
            assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
                uncheckedEnqueue(learnt_clause[0]);
            }else{
                Clause* c = Clause::Clause_new(learnt_clause, true);
                learnts.push(c);
                attachClause(*c);
                claBumpActivity(*c);
                uncheckedEnqueue(learnt_clause[0], c);
            }

            varDecayActivity();
            claDecayActivity();

        }else{
            // NO CONFLICT

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (nof_learnts >= 0 && learnts.size()-nAssigns() >= nof_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
	      /*     decisions++;
                next = pickBranchLit(polarity_mode, random_var_freq);

                if (next == lit_Undef)
                    // Model found:
		    
                   return l_True;
	      */ 
	      return Unknown;
            }

            // Increase decision level and enqueue 'next'
            assert(value(next) == l_Undef);
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}



int Solver_ext::fast_solve(const vec<Lit>& assumps)
{  
  int ret_val = Unknown;
  //      return Unknown;   
  propagation_limit = 2*(assumps.size());
  propagation_counter = 0;
  conflict.clear();  
  
  if (!ok) return Unsat;
  
  assumps.copyTo(assumptions);
  
  double  nof_conflicts =   restart_first;
  double  nof_learnts   =  nClauses() * learntsize_factor;
  // double  nof_learnts   = 1;
  // double  nof_conflicts = 2;
   lbool   status        = l_Undef;
   
  status = fast_search((int)nof_conflicts, (int)nof_learnts);
  propagation_counter = 0;

  if (status == l_False){
    ret_val= UnsatAssumpt; 
    if (conflict.size() == 0)
      {ok = false;
	ret_val= Unsat; 
      }
  }
   
  /*
  // KK only unit propagate  
  while (decisionLevel() < assumptions.size()){
    // Perform user provided assumption:
    Lit p = assumptions[decisionLevel()];
    if (value(p) == l_True){
      // Dummy decision level:
      newDecisionLevel();
    }else if (value(p) == l_False){   
        analyzeFinal(~p, conflict);
      ret_val = UnsatAssumpt;
      break;
    }else{
      if (value(p) == l_Undef)
	{
	  newDecisionLevel();
	  uncheckedEnqueue(p);  
	}
    }
  }
  
  if (!(ret_val == UnsatAssumpt)){
    if (!(propagate()==NULL))
      {    
	if (conflict.size() == 0)
	  {ok = false;
	    ret_val = Unsat;
	  }
	else 
	  {ret_val = UnsatAssumpt;}
      }
    else
      {  //if (status == l_True){    
	ret_val = Unknown;
      }
     
 }     
  */
  cancelUntil(0);
  return ret_val;
}


int bool_to_int (bool b)
{
  if (b)     
    return True;
  else
    return False;
}

int int_to_bool (int i)
{
  if (i== True) 
    return true; 
  else 
    {assert (i==False);
      return false;
    }
}

int lit_val_int_to_int (int lit_val)
{
  if (lit_val == l_true) 
    {
      return True;
    }
  else
    {
      if (lit_val == l_false)
	return False;
      else
	{assert (lit_val == l_undef);
	  return Undef;
	}
    }
}


extern "C" solver_c solver_new(void)
{ Solver_ext* solver = new Solver_ext;
  //  printf("\n polarity : %i\n", solver->polarity_mode);
  //fflush(stdout);
  return (solver_c) solver;
}

extern "C" void addVar (solver_c s,int var_id)
{
  Solver_ext* solver = (Solver_ext*) s;
  //add polarity
  //  printf("new var: %i \n",var_id);
 while (var_id+1 >= solver->nVars()) solver->newVar();
}

extern "C" lit_c lit_var (Var var_id, int polarity)
{ 
  // printf("c_wrapper: before lit_var var_id:%i \n", var_id);
  Lit * cpp_lit = int_to_bool(polarity) ?  new Lit(var_id) : new Lit(var_id,true);
  //  printf("c_wrapper: after lit_var var_id: %i \n", var(*cpp_lit));
  //  fflush(stdout);
  return (lit_c) cpp_lit;
}

// before adding clause we need to initialise the lits
extern "C" void init_clause (solver_c s)
{ //printf("c_wrapper: init_clause\n");
  Solver_ext* solver = (Solver_ext*) s;
  solver->lits.clear();
}

extern "C" void add_lit_clause (solver_c s, lit_c lit)
{
  Solver_ext* solver = (Solver_ext*) s;
  //  printf("c_wrapper: add_lit_clause, number vars: %i, val_0 %i, val_1 %i, val_2 %i \n",solver->nVars(),toInt(solver->value(0)),toInt(solver->value(1)),toInt(solver->value(2)));
  Lit* litp = (Lit*) lit;
  Lit lit_cpp = *litp;

  //  printf("%s%d\n", sign(lit_cpp) ? "-" : "+", var(lit_cpp)+1);
  //    printf("%s%d\n", sign(lit_cpp) ? "-" : "+", var(lit_cpp));
  //    fflush(stdout);
  //  printf("c_wrapper: add_lit_clause var_id:%d ", var(lit_cpp)+1);
  solver->lits.push(lit_cpp);
}

//return false if immediate unsat after adding the clause
extern "C" int add_clause (solver_c s)
{
  Solver_ext* solver = (Solver_ext*) s;
  return bool_to_int (solver->addClause(solver->lits));
}

extern "C" int solve (solver_c s)
{
  Solver_ext* solver = (Solver_ext*) s;
  return bool_to_int(solver->solve());
}



// before adding assumptions we need to initialise the lits
extern "C" void init_assumptions (solver_c s)
{
  Solver_ext* solver = (Solver_ext*) s;
  solver->lits.clear();
}

extern "C" void add_lit_assumption (solver_c s, lit_c lit)
{
  Solver_ext* solver = (Solver_ext*) s;
  Lit* litp = (Lit*) lit; 
  solver->lits.push(*litp);
}

extern "C" int solve_assumptions (solver_c s)
{

  Solver_ext* solver = (Solver_ext*) s;
  bool top_sat = solver->simplify();
  if (top_sat)
    {
      if (solver->solve(solver->lits)) 
	return Sat;
      else
	return UnsatAssumpt;
    }
  else
    return Unsat;
}
/*
//change to real fast solve
extern "C" int fast_solve_assumptions (solver_c s)
{

  Solver_ext* solver = (Solver_ext*) s;
  bool top_sat = solver->simplify();
  if (top_sat)
    {
      if (solver->solve(solver->lits)) 
	return Sat;
      else
	return UnsatAssumpt;
    }
  else
    return Unsat;
}
*/


extern "C" int fast_solve_assumptions (solver_c s)
{
  Solver_ext* solver = (Solver_ext*) s;
  bool top_sat = solver->simplify();
  
  if (top_sat)
    {   
      return solver->fast_solve(solver->lits);
    }
  else
    return Unsat;
  
}


extern "C" int lit_model_val (solver_c s, lit_c lit)
{
  Solver_ext* solver = (Solver_ext*) s;
  Lit* litp = (Lit*) lit; 
  Lit lit_cpp = *litp;
  return  lit_val_int_to_int(toInt(solver->modelValue (lit_cpp)));
}

