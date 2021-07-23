import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import re
import sys
import json

timeout_interval = 60

SAT = 1
UNSAT = 2
CSAT = 3
THM = 4
CAXS = 5
UNKNOWN = -1
TIMEOUT = -2
text = {1: "SAT", 2: "UNSAT", 3: "CSAT", 4: "THM", 5:"CAXS", -1: "UNKNOWN", -2: "TIMEOUT"}

def rating(problem):
  m = re.search("Rating\s+:\s+(\d+)\.(\d+)\s", problem)
  return float(m.groups()[0] + "." + m.groups()[1]) if m else -1

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def get_problems(list):
  f = open(list, "r")
  return [l.strip() for l in f.readlines() if len(l.strip()) > 0]

def run_sggs(p, f):
  pfile = open(f, "r")
  if "($false)" in pfile.read():
    return UNSAT # clausification may return trivial stuff
  cmd = "./koalaboom "
  bashCommand = ("./sandbox %d %s %s" % (timeout_interval, cmd, f))
  print(bashCommand)
  process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
  out, err = process.communicate()
  if "TIMEOUT" in out:
    return p + " TIMEOUT"
  for l in out.splitlines():
    if "stratified" in l:
      return p + " " + l 
  return ""

def check(p_fs):
  p, fs = p_fs
  orig_filename = "/home/bytekid/benchmarks/bigtable4sarah/Problems/" + p[:3] + "/" + p + ".p"
  cnf_filename = "cnfs/" + p + ".p"
  return run_sggs(p, cnf_filename)

def accumulate(results):
  for r in results:
    print r

if __name__ == "__main__":
  features = get_problem_features()
  jobs = []
  for p in features.keys()[:10]:
    jobs.append((p, features[p]))
  
  numprocs = multiprocessing.cpu_count() - 2
  print("use %d procs" % numprocs)
  pool = multiprocessing.Pool(numprocs)
  total_tasks = len(jobs)
  results = pool.map_async(check, jobs)
  pool.close()
  pool.join()
  accumulate(results.get())