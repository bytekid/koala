import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import re
import sys
import random
import json

timeout_interval = 300

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

def get_results():
  f = open("data/results.json", "r")
  res = json.loads(f.read())
  f.close()
  return res

def write_results(jdata):
  wfile = "data/results.json"
  f = open(wfile, "w")
  f.write(json.dumps(jdata,indent=2,sort_keys=True) + "\n")
  f.close()

def get_problems(list):
  f = open(list, "r")
  return [l.strip() for l in f.readlines() if len(l.strip()) > 0]


def problem_stats(out):
  m = re.search("# steps:\s+(\d+)", out)
  if not m:
    print("no steps " + outfile)
  steps = int(m.groups()[0]) if m else 0
  m = re.search("# extensions:\s+(\d+)", out)
  e = int(m.groups()[0]) if m else 0
  m = re.search("# conflicts:\s+(\d+)", out)
  cf = int(m.groups()[0]) if m else 0
  m = re.search("# generated clauses:\s+(\d+)", out)
  cl = int(m.groups()[0])
  m = re.search("# deleted clauses:\s+(\d+)", out)
  d = int(m.groups()[0]) if m else 0
  m = re.search("max trail length:\s+(\d+)", out)
  tl = int(m.groups()[0]) if m else 0
  m = re.search("time:\s+(\d+.\d+)", out)
  t = float(m.groups()[0]) if m else 0
  # more time details
  m = re.search("extension clauses:\s+(\d+.\d+)", out)
  t_ec = float(m.groups()[0]) if m else 0
  m = re.search("splits:\s+(\d+.\d+)", out)
  t_sp = float(m.groups()[0]) if m else 0
  m = re.search("ground instances:\s+(\d+.\d+)", out)
  t_gi = float(m.groups()[0]) if m else 0
  return {
    "steps": steps,
    "conflicts": cf,
    "generated clauses": cl,
    "deleted clauses": d,
    "trail length": tl,
    "extensions": e,
    "time": t,
    "time extensions": t_ec,
    "time splits": t_sp,
    "time instances": t_gi}

def run_sggs(p, f):
  pfile = open(f, "r")
  if "($false)" in pfile.read():
    resrec = { "success": "SUC", "result": text[UNSAT], "timeout": timeout_interval}
    return UNSAT, (p, resrec) # clausification may return trivial stuff
  outfile = "sggsruns/" + p + ".txt"
  cmd = "./koalaopt --dbg_backtrace true "
  print(p)
  sys.stdout.flush()
  if True or not os.path.exists(outfile):
    bashCommand = ("./sandbox %d %s %s" % (timeout_interval, cmd, f))
    print(bashCommand)
    process = subprocess.Popen(bashCommand.split(), stdout=subprocess.PIPE)
    out, err = process.communicate()
    if err:
      print(err)
    elif "Satisfiable" in out or "Unsatisfiable" in out:
      f = open(outfile, "w")
      f.write(out)
      f.close()
  else:
    f = open(outfile, "r")
    out = f.read()
  scode = "SUC" if "atisfiable" in out else "TMO" if "TIMEOUT" in out else "UNK"
  print(p + ": " + scode)
  sys.stdout.flush()
  #if scode == "SUC":
  #  print("new acquirement " + p)
  result = SAT if "Satisfiable" in out else UNSAT if "Unsatisfiable" in out \
    else TIMEOUT if "TIMEOUT" in out else UNKNOWN
  resrec = { "success": scode, "result": text[result], \
    "timeout": timeout_interval, "stats": problem_stats(out)}
  return result, (p, resrec)

def check(p_fs):
  p, fs = p_fs
  orig_filename = "Problems/" + p[:3] + "/" + p + ".p"
  cnf_filename = "cnfs/" + p + ".p"  
  f = open(orig_filename, "r")
  problem = f.read()
  status = "% Status   : "
  sat = SAT if status + "Satisfiable" in problem else \
    UNSAT if status + "Unsatisfiable" in problem else \
    THM if status + "Theorem" in problem else \
    CSAT if status + "CounterSatisfiable" in problem else \
    CAXS if status + "ContradictoryAxioms" in problem else UNKNOWN
  assert(sat or ("Unsatisfiable" in problem))
  cnt = fs["vampire_axiom_clauses"]
  print("%s is %s  (%.2f) %d" % (p, text[sat], rating(problem), cnt))
  res, (p, rrec) = run_sggs(p, cnf_filename)
  if (res >= 0) and (res != sat and not(res == UNSAT and sat == THM) \
    and not(res == SAT and sat == CSAT) and not(res == UNSAT and sat == CAXS)):
    print(text[res] + " " + text[sat] + " unsound!!!")
  print("  " + text[res])
  return res, (p, rrec)

def accumulate(results, old_results):
  res = {}
  rrecs = {}
  for (r, (p, rrec)) in results:
    res[r] = res[r] + 1 if r in res else 1
    old_results[p] = rrec
  for r in res.keys():
    print("%d %s" % (res[r], text[r]))
  write_results(old_results)

if __name__ == "__main__":
  list = str(sys.argv[1])
  ps = get_problems(list)
  features = get_problem_features()
  old_results = get_results()

  random.shuffle(ps)
  jobs = []  
  for p in ps:
    already_done = p in old_results
    suc = old_results[p]["success"] if already_done else ''
    tmo = old_results[p]["timeout"] if already_done else 0
    skip = suc == 'SUC' or (suc == 'TMO' and tmo >= timeout_interval)
    if not skip:
      jobs.append((p, features[p]))
  
  numprocs = multiprocessing.cpu_count() - 1
  print("use %d procs" % numprocs)
  print("%d jobs" % len(jobs))
  pool = multiprocessing.Pool(numprocs)
  total_tasks = len(jobs)
  results = pool.map_async(check, jobs)
  pool.close()
  pool.join()
  accumulate(results.get(), old_results)
  old_results = get_results()
  