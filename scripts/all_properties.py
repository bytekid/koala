import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import json
import sys
sys.path.append('.')
import expr, data, tptp
from stratified import is_guarded, is_pvd, is_stratified, args, non_stratified_part, is_epr, is_ackermann
from restrained import check_ground, fold_left, literals, is_pvd_restrained_splittable
from controlled import is_controlled
from expr import Visitor, Var, Fun, Cnf
from pyparsing import ParseException
import shutil
import re

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def get_problem_properties():
  f = open("data/properties.json", "r")
  return json.loads(f.read())

def write_dec_properties(fs):
  f = open("data/decidability.json", "w")
  f.write(json.dumps(fs,indent=2,sort_keys=True) + "\n")

def problem_stats(outfile):
  f = open(outfile, "r")
  out = f.read()
  m = re.search("# steps:\s+(\d+)", out)
  steps = m.groups()[0] if m else 0
  m = re.search("# conflicts:\s+(\d+)", out)
  cf = m.groups()[0] if m else 0
  m = re.search("# generated clauses:\s+(\d+)", out)
  cl = m.groups()[0] if m else 0
  m = re.search("max trail length:\s+(\d+)", out)
  tl = m.groups()[0] if m else 0
  return {"steps": steps, "conflicts": cf, "clauses": cl, "trail length": tl}

property_names = [
  "pos_restrained", "neg_restrained", "is_guarded", "is_stratified", "is_pvd",
  "is_ackermann", "is_ground", "is_epr", "is_monadic", "is_2var", "is_sort_pvd",
  "is_pos_controlled", "is_neg_controlled", "is_sort_restrained", "is_pvd_restrained_splittable",
  "is_pos_horn", "is_neg_horn", "is_horn"]

def check(p, props, verbose = False):
  not_applicable = ""
  MAX_SIZE = 500
  in_cnf = props["vampire_axiom_clauses"] > 0
  if props["vampire_axiom_clauses"] > MAX_SIZE:
    not_applicable = "too large"
  elif props["vampire_equality_atoms"] > 0:
    not_applicable = "equality"
  elif props["num_type_connectives"] > 0:
    not_applicable = "type connectives"
  res = {"error": not_applicable, "success": False}
  if not not_applicable:
    filename = "Problems/" + p[:3] + "/" + p + ".p" if in_cnf else "cnfs/" + p + ".p"
    content = data.get_problem(filename)
    if len([l for l in content.splitlines() if "cnf(" in l]) > MAX_SIZE:
      res = {"error": "too large", "success": False}
    else:
      try:
        formulas = tptp.parse_problem(content, verbose)
        ((bndp, bndn), success, technique), msg = check_ground(p, formulas)
        fs = [c.formula for c in formulas]
        lss = [literals(c) for c in fs] 
        res["pos_restrained"] = bndp
        res["neg_restrained"] = bndn
        res["is_restrained"] = bndp or bndn
        res["success"] = success
        res["is_guarded"] = is_guarded(lss)
        res["is_stratified"] = is_stratified(fs)
        res["is_ackermann"] = is_ackermann(lss)
        res["is_pvd_restrained_splittable"] = is_pvd_restrained_splittable(fs)
        res["is_pvd"] = is_pvd(lss)
        res["technique"] = technique
        res["flipped"] = msg
        res["is_ground"] = props["num_variables"] == 0
        res["is_epr"] = is_epr(fs)
        res["is_monadic"] = props["vampire_max_pred_arity"] <= 1
        res["is_2var"] = props["vampire_max_variables_in_clause"] <= 2 and props["vampire_max_fun_arity"] <= 0
        (pos_horn, pos_contr), (neg_horn, neg_contr) = is_controlled(p, formulas)
        res["is_pos_horn"] = pos_horn
        res["is_neg_horn"] = neg_horn
        res["is_horn"] = neg_horn or pos_horn
        res["is_pos_controlled"] = pos_contr
        res["is_neg_controlled"] = neg_contr
        res["is_controlled"] = neg_contr or pos_contr
        if res["is_pvd_restrained_splittable"]  and not (res["is_pvd"] or res["is_restrained"]):
          print (" SPLITTING advantage")
        if res["is_stratified"]:
          res["is_sort_pvd"] = True
          res["is_sort_restrained"] = True
        else:
          non_strat = non_stratified_part(fs)
          if res["is_restrained"]:
            res["is_sort_restrained"] = True
          else:
            non_strat_cnf = [Cnf("x", 0, f) for f in non_strat]
            ((bndp, bndn), success2, _), _ = check_ground(p, non_strat_cnf, mode="sort-restrained")
            res["is_sort_restrained"] = success2
          if res["is_pvd"]:
            res["is_sort_pvd"] = True
          else:
            res["is_sort_pvd"] = is_pvd([literals(c) for c in non_strat])
        koala_out = "sggsruns/" + p + ".txt"
        if os.path.exists(koala_out):
          res["koala stats"] = problem_stats(koala_out)
        else:
          res["koala stats"] = None
      except ParseException:
        res = {"error": "parse error", "success": False}
        print("parse error on " + p)
      # need original file for status
      filename = "Problems/" + p[:3] + "/" + p + ".p"
      content = data.get_problem(filename)
      res["status"] = "SAT" if "% Status   : Satisfiable" in content else \
        "UNSAT" if "% Status   : Unsatisfiable" in content else \
        "THM" if "% Status   : Theorem" in content else \
        "CSAT" if "% Status   : CounterSatisfiable" in content else "UNK"
      res["rating"] = props["rating"]

  return res

def property_details(prop, us, exclude):
  avg = lambda l: sum(l)/len(l) if len(l) > 0 else 0
  prop_pos = [u for u in us if u[prop]]
  s = prop + ": " + str(len(prop_pos)) + "\n"
  s += "avg rating: " + str(avg([u["rating"] for u in prop_pos])) + "\n"
  for p in property_names + ["is_restrained", "is_controlled"]:
    s += p + ": " + str(len([u for u in prop_pos if u[p]]))  + "\n"
  other_crit = 0
  for sys in prop_pos:
    for p in property_names:
      if p not in exclude + [prop] and sys[p]:
        other_crit += 1
        break
  s += "none: " + str(len(prop_pos) - other_crit)
  print("<!-- " + s + "-->")

if __name__ == "__main__":
  features = get_problem_features()
  properties = get_problem_properties()

  fs = {}
  for f in features.keys():
    if not ("=" in f): # and "SYN0" in f:
      print(f + ": " + str(f in properties))
      if f in properties and \
        (properties[f]["error"] in ["equality"]): #  "error" not in properties[f] or 
        fs[f] = properties[f] 
      else:
        fs[f] = check(f, features[f])
  
  write_dec_properties(fs)
  
  usable = [c for c in fs if not fs[c]["error"] ]
  print("<!--%d total" % len(fs))
  print("%d not in CNF" % len([f for f in fs if "not in cnf" == fs[f]["error"]]))
  print("%d too large" % len([f for f in fs if "too large" == fs[f]["error"]]))
  print("%d equality" % len([f for f in fs if "equality" == fs[f]["error"]]))
  print("%d positively bounded" % len([f for f in usable if fs[f]["pos_restrained"]]))
  print("%d negatively bounded" % len([f for f in usable if fs[f]["neg_restrained"]]))
  print("%d successes-->" % len(usable))
  print("<table border=\"1\" cellpadding=\"1\" cellspacing=\"0\">")
  print("<tr><th class=\"thead\">problem</th><th class=\"thead\">status</th><th class=\"thead\">rating</th>")
  pth = lambda s: "<th class=\"thead\">" + s + "</th>"
  ptd = lambda b: "<td>" + ("1" if b else "0") + "</td>"
  pheads = fold_left(lambda acc, p: str(acc) + pth(p), "", property_names)
  print(pheads + "<th></th><th>TRS</th><th></th></tr>")
  for u in usable:
    dom = u[0:3]
    href = "http://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=" + dom + "&File=" + u + ".p"
    print("<tr>")
    print("<td class=\"system\"><a href=\"%s\">%s</a></td>" % (href, u))
    print("<td>%s</td>" % fs[u]["status"])
    print("<td>%s</td>" % fs[u]["rating"])
    # other properties
    props = [ ptd(fs[u][p]) for p in property_names ]
    ps = fold_left(lambda s, p: s + p, "", props)
    print(ps)
    # koala result
    sggs = "sggsruns/" + u + ".txt"
    if os.path.exists(sggs):
      print("<td><?php if (file_exists(\"%s\")) { ?><a href=\"%s\">sggs run</a><?php } ?></td>" % (sggs, sggs))
    else:
      print("<td></td>")
    #if p["koala stats"]:
    #  s = p["koala stats"]
    #  print("<td>%d</td><td>%d</td><td>%d</td><td>%d</td>" % (s["steps"], s["clauses"], s["conflicts"], s["trail length"]))
    #else:
    #  print("<td></td>")
    # restraining TRS
    trsfilename = "trss/" + u + ".trs"
    if isfile(trsfilename):
      print("<td><a href=\"%s\">TRS</a></td>" % (trsfilename))
    else:
      print("<td><em>empty</em></td>")
    print("<td>%s</td>" % fs[u]["flipped"])
    print("</tr>")
  count = lambda s: "<td>" + str(len([ u for u in usable if fs[u][s]])) + "</td>"
  counts = fold_left(lambda s, p: s + p, "", [ count(p) for p in property_names ])
  print("<tr><td></td><td></td><td></td>" + counts + "<td></td></tr>")

  sggs_decides = lambda p: p["is_ground"] or p["is_pvd"] or p["is_stratified"] or p["pos_restrained"] or \
    p["neg_restrained"] or p["is_sort_pvd"] or p["is_sort_restrained"] or p["is_pos_controlled"] or p["is_neg_controlled"]
  sggs_dec_count = len([ u for u in usable if sggs_decides(fs[u])])
  print("<tr><td>sggs decidable</td><td></td><td></td><td>" + str(sggs_dec_count) + "</td><td></td></tr>")
  decidable = lambda p: sggs_decides(p) or p["is_monadic"] or p["is_2var"] or p["is_guarded"] or p["is_ackermann"]
  dec_count = len([ u for u in usable if decidable(fs[u])])
  print("<tr><td> decidable</td><td></td><td></td><td>" + str(dec_count) + "</td><td></td></tr>")
  restr_count = len([ u for u in usable if fs[u]["neg_restrained"] or fs[u]["pos_restrained"]])
  contr_count = len([ u for u in usable if fs[u]["is_neg_controlled"] or fs[u]["is_pos_controlled"]])
  horn_count = len([ u for u in usable if fs[u]["is_horn"]])
  print("<!-- restrained: %d  controlled: %d horn %d -->" % (restr_count, contr_count, horn_count))
  usable_problems = [fs[u] for u in usable]
  horn = ["is_pos_horn", "is_neg_horn", "is_horn"]
  property_details("is_restrained", usable_problems, ["pos_restrained", "neg_restrained", "is_sort_restrained"] + horn)
  property_details("is_controlled", usable_problems, ["is_pos_controlled", "is_neg_controlled"] + horn)
  property_details("is_sort_pvd", usable_problems, horn)
  property_details("is_sort_restrained", usable_problems, horn)
  print("</table>")

  # 