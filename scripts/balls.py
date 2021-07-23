import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import re
import sys

def axiom(c):
  return "cnf(some,axiom, (\n  " + c +"\n ))."

base = "cnf(two_whites_out_one_black_in,axiom,\n\
    ( p(X,s(Y))\n\
    | ~ p(s(s(X)),Y) )).\n\
  cnf(two_blacks_out_one_black_in,axiom,\n\
    ( p(X,s(Y))\n\
    | ~ p(X,s(s(Y))) )).\n\
  cnf(two_different_balls_out_one_white_in,axiom,\n\
    ( p(s(X),Y)\n\
    | ~ p(s(X),s(Y)) )).\n\
  cnf(goal_state,negated_conjecture,\n\
    ( ~ p(s(n0),n0) )).\n"

def sn(n):
  t = "n0"
  for i in range(0,n):
    t = "s(" + t + ")"
  return t

if __name__ == "__main__":
  n = int(sys.argv[1])
  clause = ""
  for i in range(3,n):
    pow = 2 ** i
    lit = "p(" + sn(pow) + ", " + sn(pow - 1) + ")"
    clause = clause + "\n | " if clause else clause
    clause = clause + lit
  print(axiom(clause) + "\n")
  print(base)

