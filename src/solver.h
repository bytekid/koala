/**************************************************************************************************
MiniSat -- Copyright (c) 2005, Niklas Sorensson
http://www.cs.chalmers.se/Cs/Research/FormalMethods/MiniSat/

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/
// Modified to compile with MS Visual Studio 6.0 by Alan Mishchenko

#ifndef solver_h
#define solver_h

#ifdef _WIN32
#define inline __inline // compatible with MS VS 6.0
#endif

#include "vec.h"

//=================================================================================================
// Simple types:

// does not work for c++
typedef int  bool;
static const bool  true      = 1;
static const bool  false     = 0;

typedef int                lit;
typedef char               lbool;

//#ifdef _WIN32
//#typedef signed __int64     uint64;   // compatible with MS VS 6.0
//#else
//typedef unsigned long long uint64;
//#endif

static const int   var_Undef = -1;
static const lit   lit_Undef = -2;

static const lbool l_Undef   =  0;
static const lbool l_True    =  1;
static const lbool l_False   = -1;

// returned when an error occured (should never happen..)
static const lbool l_Err     = -13;

//KK l_Not_Assigned is technical value used in solver_addclause
//static const lbool l_Not_Assigned =  -2;

static inline lit  toLit   (int v) { return v + v; }
static inline lit  lit_neg (lit l) { return l ^ 1; }
static inline int  lit_var (lit l) { return l >> 1; }
static inline int  lit_sign(lit l) { return (l & 1); }


//=================================================================================================
// Public interface:

struct solver_t;
typedef struct solver_t solver;

extern solver* solver_new(void);
extern void    solver_delete(solver* s);

extern bool    solver_addclause(solver* s, lit* begin, lit* end);
extern bool    solver_simplify(solver* s);

// l_False -- unsat under assumptions
// l_Undef -- unsat already without assumtions
// l_True  -- sat under assuptions
extern int    solver_solve(solver* s, lit* begin, lit* end);

// KK
// l_False -- unsat under assumptions
// l_Undef -- unsat even without assumtions
// l_True  -- unkown (fast solve sat under assuptions)
extern int    fast_solve(solver* s, lit* begin, lit* end);

extern int     solver_nvars(solver* s);
extern int     solver_nclauses(solver* s);
extern int     solver_nconflicts(solver* s);

extern void    solver_setnvars(solver* s,int n);

// returns next implied unit
// lit_Undef if there is no new implied units
extern lit     solver_next_unit(solver* s);

struct stats_t
{
   unsigned long long   starts, decisions, propagations, inspects, conflicts;
   unsigned long long   clauses, clauses_literals, learnts, learnts_literals, max_literals, tot_literals;
};
typedef struct stats_t stats;

//=================================================================================================
// Solver representation:

struct clause_t;
typedef struct clause_t clause;

struct solver_t
{

   bool     sim;           // if sim==true the solver is a simplifiaction solver 
                           // fast_solve is efficient, solve can be not,  
                           // else is a normal inc. solver where solve is efficient 
                           // fast_solve is not efficint and model is supported

    int      size;          // nof variables 
    int      cap;           // size of varmaps
    int      qhead;         // Head index of queue.
    int      qtail;         // Tail index of queue.

    // clauses
    vecp     clauses;       // List of problem constraints. (contains: clause*)
    vecp     learnts;       // List of learnt clauses. (contains: clause*)

    // activities
    double   var_inc;       // Amount to bump next variable with.
    double   var_decay;     // INVERSE decay factor for variable activity: stores 1/decay. 
    float    cla_inc;       // Amount to bump next clause with.
    float    cla_decay;     // INVERSE decay factor for clause activity: stores 1/decay.

    vecp*    wlists;        // 
    double*  activity;      // A heuristic measurement of the activity of a variable.
    lbool*   assigns;       // Current values of variables.
    int*     orderpos;      // Index in variable order.
    clause** reasons;       //
    int*     levels;        //
    lit*     trail;

    clause*  binary;        // A temporary binary clause
    lbool*   tags;          //
    veci     tagged;        // (contains: var)
    veci     stack;         // (contains: var)

    veci     order;         // Variable order. (heap) (contains: var)
    veci     trail_lim;     // Separator indices for different decision levels in 'trail'. (contains: int)
    veci     model;         // If problem is solved, this vector contains the model (contains: lbool).

 
    int      root_level;    // Level of first proper decision.
    int      simpdb_assigns;// Number of top-level assignments at last 'simplifyDB()'.
    int      simpdb_props;  // Number of propagations before next 'simplifyDB()'.
    double   random_seed;
    double   progress_estimate;
    int      verbosity;     // Verbosity level. 0=silent, 1=some progress report, 2=everything

  stats    stats;

  //KK 
  // if status is true then the set of clauses in the solver is satisfied by 
  // the current model (note all literals are always have some value in the model) 
  // in this case we do not need to run the solver when solve 
  // when solve with assumtions we check if status is true and 
  // the assumtions are true in the model, then return true else we run the solver


  //  veci    current_units;   //contains learnt unit clauses 
                            //at the next run they are enqueded and propagated first
                            //and current_units are reset
  int units_head; //units head

  bool       status; 
};

#endif
