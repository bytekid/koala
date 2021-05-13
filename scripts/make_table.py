import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import json
import sys
sys.path.append('.')
import re
import shutil

def get_problems(list):
  f = open(list, "r")
  return [l.strip() for l in f.readlines() if len(l.strip()) > 0]

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def get_problem_properties():
  f = open("data/properties.json", "r")
  return json.loads(f.read())

def write_koala_results(fs):
  f = open("data/results.json", "w")
  f.write(json.dumps(fs,indent=2,sort_keys=True) + "\n")

def get_koala_results():
  f = open("data/results.json", "r")
  return json.loads(f.read())

def problem_stats(outfile):
  f = open(outfile, "r")
  out = f.read()
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
  return {"steps": steps, "conflicts": cf, "generated clauses": cl, \
    "deleted clauses": d, "trail length": tl, "time": t, "extensions": e}

property_names = [
  "is_ground", "is_epr", "is_stratified", "is_monadic", "is_guarded",
  "is_2var",  "is_pvd",
  "is_ackermann", "is_sort_pvd", "is_restrained", "is_sort_restrained", 
  "is_controlled"]
latex_property_names = {
  "is_ground" : "ground", "is_epr" : "EPR", "is_stratified" : "stratified", 
  "is_monadic" : "monadic", "is_guarded" : "guarded",
  "is_2var" : "${\\sf FO}^2$",  "is_pvd" : "PVD",
  "is_ackermann" : "Ackermann", "is_sort_pvd" : "sort-refined PVD", 
  "is_restrained" : "restrained", "is_sort_restrained" : "sort-restrained", 
  "is_controlled" : "controlled"
}

stat_keys = ["steps", "conflicts", "extensions", "generated clauses", "deleted clauses", "trail length", "time"]
suc_keys = [ "SUC", "SAT", "UNSAT", "TMO", "UNK", "count" ]
keys = suc_keys + stat_keys

if __name__ == "__main__":
  problems = get_problems(str(sys.argv[1]))
  features = get_problem_features()
  properties = get_problem_properties()
  results = get_koala_results()

  count = {}
  for n in property_names:
    count[n] = {}
    for k in keys:
      count[n][k] = 0

  for p in problems:
    res = results[p]
    props = properties[p]
    props["is_controlled"] = props["is_neg_controlled"] or props["is_pos_controlled"]
    stats = None
    succeeded = ("SUC" == res["success"])

    for n in property_names:
      if props[n]:
        count[n]["count"] += 1
        count[n][res["success"]] += 1
        if succeeded:
          count[n][res["result"]] += 1

    if succeeded:
      koala_result_file = "sggsruns/"+p+".txt"
      if isfile(koala_result_file):
        stats = problem_stats(koala_result_file)
        for n in property_names:
          if props[n]:
            for k in stat_keys:
              count[n][k] += stats[k]
      else:
        print(koala_result_file + " is missing")
  s=""
  for n in property_names:
    s += latex_property_names[n] + " & " + str(count[n]["count"])
    print("%s & %d &" % (n, count[n]["count"]))
    cnt = count[n]
    for k in suc_keys:
      #s += " & " + str(cnt[k])
      print("  %s: %d" % (k, cnt[k]))
    suc = cnt["SUC"]
    for k in stat_keys:
      print("  %s: %.2f" % (k, float(cnt[k]) / suc))
      if k != "time":
        s += " & " + str(int(float(cnt[k]) / suc))
    s += "\\\\\n"
  print(s)
