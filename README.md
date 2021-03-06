# Koala

Koala is a prototype theorem prover for first-order logic developed by Sarah Winkler.

It implements the Semantically Guided Goal-Sensitive Reasoning (SGGS) method
by Maria Paola Bonacina and David A. Plaisted.
The software uses some code of iProver:
http://www.cs.man.ac.uk/~korovink/iprover/
which is kindly made available by Konstantin Korovin under GPL.
However, we obviously take responsibility for all potential errors in Koala.

Just like iProver, Koala is implemented in OCaml and licensed under GNU GPL.

## Installation

We assume OCaml v4.04 >= is installed. 

1) ./configure
2) make 

will produce executable: koalaopt


-1) "make clean"     to remove created objects and executable files
-2) "make clean_all" to remove created objects and executable files, cleaning
   external libraries (if there are errors during compilation try this first).

## Usage 

$ koalaopt --time_out_real 300. problem.p
       
where problem.p is a CNF problem in the TPTP format; or to output the derivation:

$ koalaopt  --dbg_backtrace true problem.p

 (Please use CNF problems as input; the translation from FOF is not (yet) done
 automatically.)
