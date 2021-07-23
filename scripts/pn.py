import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import re
import sys

def axiom(c):
  return "cnf(some,axiom, (\n  " + c +"\n ))."

if __name__ == "__main__":
  n = int(sys.argv[1])
  problem = ""
  neg = ""
  vars = ""
  for i in range(0,n):
    clause = neg
    cj = "0"
    for j in range(0,n):
      lit = "p" + str(i) + "(" + vars + cj + ")"
      clause = clause + (" | " if clause else "") + lit
      cj = "s(" + cj + ")"
    print(axiom(clause))
    vars = vars + "X" + str(j)
    neg = "~ p" + str(i) + "(" + vars + ")"
    vars = vars + ", "
