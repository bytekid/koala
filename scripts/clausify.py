import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import re
import sys
import json

SAT = 1
UNSAT = 2
UNKNOWN = -1
TIMEOUT = 3
text = {1: "SAT", 2: "UNSAT", -1: "UNKNOWN", 3: "TIMEOUT"}

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def get_problems():
  f = open("bounded.txt", "r")
  return [l.strip() for l in f.readlines() if len(l.strip()) > 0]

def clausify(p, pinput, fs):
  cnffile = "cnfs/" + p + ".p"
  if isfile(cnffile):
    return

  cmd = "/home/bytekid/tools/E/eprover --cnf --no-preprocessing "
  bashCommand = "./sandbox 60 " + cmd + " " + pinput
  print(bashCommand)
  process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
  out, err = process.communicate()
  if err:
    print(err)
  else:
    f = open(cnffile, "a")
    for l in out.splitlines():
      if l and not l[0] == '#':
         f.write(l+"\n\n")
    f.close()

if __name__ == "__main__":
  features = get_problem_features()
  for f in features.keys():
    if not "=" in f: # typed/arithmetic problems
      pinput = "Problems/" + f[:3] + "/" + f + ".p"
      clausify(f, pinput, features[f])