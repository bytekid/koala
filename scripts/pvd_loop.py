import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import json
import sys
sys.path.append('.')
import expr, data, tptp
from expr import Visitor, Var, Fun
from stratified import is_pvd, is_pvd1, is_guarded, is_stratified, is_epr

MAX_SIZE = 800
  
def fold_left(func, init, seq):
  acc = init
  for i in seq:
    acc = func(acc, i)
  return acc

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def literals(f):
  if f.is_literal():
    return [f]
  else:
    assert(isinstance(f, expr.Binop))
    return literals(f.left) + literals(f.right)

def check(p, tptp_properties, verbose = False):
  not_applicable = ""
  if (tptp_properties["vampire_axiom_clauses"] + tptp_properties["vampire_axiom_formulas"] +\
     tptp_properties["vampire_goal_clauses"] > MAX_SIZE) or tptp_properties["vampire_subformulas"] > 1000:
    not_applicable = "too large"
  if tptp_properties["vampire_equality_atoms"] > 0:
    not_applicable = "equality"
  #print(p)
  sys.stdout.flush()
  res = {"error": not_applicable, "success": False}
  if not not_applicable:
    ofilename = "Problems/" + p[:3] + "/" + p + ".p"
    filename = "cnfs/" + p + ".p"
    content = data.get_problem(filename)
    if not content.strip():
      return {"error": "empty", "success": False}

    rf = open("boundedx.txt", "r")
    restrained_list = rf.read()
    
    formulas = tptp.parse_problem(content, verbose)
    #print("parsed")
    fs = [c.formula for c in formulas]
    lss = [literals(c) for c in fs]
    strat = is_stratified(fs)
    res["is_epr0"] = tptp_properties["vampire_max_fun_arity"] == 0 and \
      tptp_properties["num_exists"] == 0 and tptp_properties["num_forall"] == 0
    res["is_epr"] = is_epr(fs)
    if res["is_epr"] and not strat:
      print("EPR but not stratified: " + p)
    if res["is_epr0"] and not res["is_epr"]:
      print("EPR0 but not EPR: " + p)
    res["is_guarded"] = is_guarded(lss)
    res["is_stratified"] = strat
    res["is_restrained"] = (p in restrained_list)
    res["is_pvd"] = is_pvd(lss)
    #res["is_pvd1"] = is_pvd1(lss)
    res["success"] = res["is_pvd"]
    content = data.get_problem(ofilename)
    status = "% Status   : "
    sat = "SAT" if status + "Satisfiable" in content else \
      "UNSAT" if status + "Unsatisfiable" in content else \
      "THM" if status + "Theorem" in content else \
      "CSAT" if status + "CounterSatisfiable" in content else \
      "CAXS" if status + "ContradictoryAxioms" in content else "?"
    res["status"] = sat
    if strat:
      print(p + " " + sat)

  return res

if __name__ == "__main__":
  features = get_problem_features()
  fs = {}
  for f in features.keys():
    if not "=" in f:# and"SYN05" in f:
      fs[f] = check(f, features[f])

  usable = [c for c in fs if fs[c]["success"]]
  print("%d total" % len(fs))
  print("%d not in CNF" % len([f for f in fs if "not in cnf" == fs[f]["error"]]))
  print("%d too large" % len([f for f in fs if "too large" == fs[f]["error"]]))
  print("%d equality" % len([f for f in fs if "equality" == fs[f]["error"]]))
  print("%d stratified problems" % len(usable))
  print("<table>")
  print("<tr><th class=\"thead\">problem</th><th class=\"thead\">status</th><th class=\"thead\">rating</th>")
  print("<th class=\"thead\">properties</th><th></th></tr>")
  for u in usable:
    dom = u[0:3]
    href = "http://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=" + dom + "&File=" + u + ".p"
    print("<tr>")
    print("<td class=\"system\"><a href=\"%s\">%s</a></td>" % (href, u))
    print("<td>%s</td>" % fs[u]["status"])
    print("<td>%s</td>" % features[u]["rating"])
    # other properties
    epr = "EPR" if features[u]["vampire_max_fun_arity"] == 0 else ""
    ground = "ground" if features[u]["num_variables"] == 0 else ""
    mon = "monadic" if features[u]["vampire_max_pred_arity"] <= 1 else ""
    two_var = "2var" if features[u]["vampire_max_variables_in_clause"] <= 2 and features[u]["vampire_max_fun_arity"] <= 0 else ""
    guarded = "guarded" if fs[u]["is_guarded"] else ""
    strat = "stratified" if fs[u]["is_stratified"] else ""
    restr = "restrained" if fs[u]["is_restrained"] else ""
    none = "<!--none-->" if not(epr or mon or two_var or guarded or ground or strat or restr) else ""
    props = [epr, mon, two_var, guarded, ground, restr, none, strat]
    props = [p for p in props if p]
    ps = fold_left(lambda s, p: s + (", " if s else "") + p, "", props)
    print("<td>%s</td>" % ps)
    sggs = "sggsruns/" + u + ".txt"
    print("<td><?php if (file_exists(\"%s\")) { ?><a href=\"%s\">sggs run</a><?php } ?></td>" % (sggs, sggs))
    print("</tr>")
  print("</table>")
  r = sum([features[u]["rating"] for u in usable]) / 117.0
  print("average rating %.2f" % r)