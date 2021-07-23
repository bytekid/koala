import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import json
import sys
sys.path.append('.')
import expr, data, tptp
from stratified import is_guarded, is_pvd, is_stratified, args
from expr import Visitor, Var, Fun, Cnf
import shutil

MAX_TRS_COUNT = 100

def get_problem_features():
  f = open("data/features.json", "r")
  return json.loads(f.read())

def literals(f):
  if f.is_literal():
    return [f]
  else:
    assert(isinstance(f, expr.Binop))
    return literals(f.left) + literals(f.right)
  
def fold_left(func, init, seq):
  acc = init
  for i in seq:
    acc = func(acc, i)
  return acc

def forall(pred, seq):
  return fold_left(lambda v, l: v and pred(l), True, seq)

def exists(pred, seq):
  return fold_left(lambda v, l: v or pred(l), False, seq)

def find(pred, seq):
  return fold_left(lambda v, l: l if pred(l) else v, None, seq)

def cross(lss):
  return fold_left(lambda rss, ls: [ rs + [l] for rs in rss for l in ls], [[]], lss)

def all_ground(ls):
  return forall(lambda l: l.is_ground(), ls)

def covered(ls, is_pos):
  poss = [l for l in ls if l.is_positive()]
  negs = [l for l in ls if not l.is_positive()]
  (cover, to_cover) = (negs, poss) if is_pos else (poss, negs)

  def covered(lp):
    return exists(lambda ln: lp.vars().issubset(ln.vars()), cover)

  return forall(lambda lp: lp.is_ground() or covered(lp), to_cover)

def all_all_pos_all_ground(cs):
  non_gnd = [ls for ls in cs if not all_ground(ls)]
  vars_pos_in_neg = forall(lambda c: covered(c, True), non_gnd)
  return vars_pos_in_neg

def all_all_neg_all_ground(cs):
  non_gnd = [ls for ls in cs if not all_ground(ls)]
  vars_neg_in_pos = forall(lambda c: covered(c, False), non_gnd)
  return vars_neg_in_pos

def atom(l):
  return l if isinstance(l, expr.Fun) or l.is_positive() else l.arg

def is_strat(cs):
  return is_stratified(cs)

### create TRSs
def rules_for_clause(ls, is_pos, covered):
  poss = [l for l in ls if l.is_positive()]
  negs = [l for l in ls if not l.is_positive()]
  (cover, to_cover) = (negs, poss) if is_pos else (poss, negs)
  to_cover = [l for l in to_cover if not l.is_ground()] 

  def covering(lp):
    return [ln for ln in cover if lp.vars().issubset(ln.vars())]

  trs = []
  if covered:
    if not(forall(lambda l: covering(l) != [], to_cover)):
      return None
    trs = [[(l,lp) for l in covering(lp)] for lp in to_cover]
  else:
    trs = [[(l,lp) for l in cover] for lp in to_cover]
  return trs

def run_ttt2(f):
  cmd1 = "./sandbox 10 /home/bytekid/tools/ghm/ttt2 " + f
  cmd2 = "java -ea -jar ../aprove/aprove.jar -m wst -t 10 " + f

  def run(cmd, tool):
    #print(cmd)
    sys.stdout.flush()
    process = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
    out, err = process.communicate()
    if err:
      print(err)
    if "MAYBE" in out:
      print("MAYBE" + f)
    technique = tool + " "
    if "LPO" in out:
      technique = technique + "LPO"
    elif "KBO" in out:
      technique = technique + "KBO"
    elif "Matrix" in out:
      technique = technique + "Matrix"
    return "YES" in out, technique

  r1, t1 = run(cmd1, "TTT2")
  if r1:
    return r1, t1
  return run(cmd2, "AProVE")

def is_permutative(l,r):
  def all_vars(ts):
    return forall(lambda v: isinstance(v, expr.Var), ts)
  var_args = all_vars(l.args) and all_vars(r.args)
  return l.name == r.name and var_args and l.vars() == r.vars()

def check_trs(p, i, trs, nonground = False):
  if not trs: # empty
    return (True, "trivial"), False
  trs = list(set(trs))
  vars = set([v for (l, r) in trs for v in set(l.vars()).union(set(r.vars()))])
  var_str = fold_left(lambda s, v: s + " " + v, "", vars)
  trs_str = "(VAR " + var_str + ")\n"
  trs_str = trs_str + "(RULES \n"
  for (l,r) in trs:
    l = atom(l)
    r = atom(r)
    increasing = l in r.subterms()
    op = "->=" if is_permutative(l,r) or increasing else "->"
    trs_str = trs_str + str(l) + " " + op + " " + str(r) + "\n"
  trs_str = trs_str + ")\n"
  #print("  TRS %d" % len(trs))
  filename = "trss/" + p + "_restrained.trs"
  rfile = open(filename, "w")
  rfile.write(trs_str)
  rfile.close()
  return run_ttt2(filename), "->=" in trs_str

def get_trss(p, lss, is_pos, covered):
  rss_all = [rules_for_clause(ls, is_pos, covered) for ls in lss]
  if None in rss_all:
    return []
  
  rss = [rs for ls in lss for rsl in rss_all for rs in rsl if rs != []]
  cross_cnt = fold_left(lambda p, l: p * l, 1, [len(rs) for rs in rss ])
  #print("restrained: " + str(cross_cnt))
  if cross_cnt > 10000: # too large
    trss = [[rs[0] for rs in rss]] # just one TRS
  else:
    trss = cross([rs for rs in rss])[:MAX_TRS_COUNT] # check at most 100 TRSs
  return trss
  
def mk_gen(syms):
  rs = []
  gen = expr.Fun("gen", [])
  for (f, a) in syms:
    rs.append((gen, expr.Fun(f, [gen for i in range(0,a)])))
  return rs

def check_non_ground_polarity(p, lss, is_pos):
  trss = get_trss(p, lss, is_pos, covered=False)
  #print("try %s non-ground, %d trss" % (p, len(trss)))
  proven = False
  technique = "nonground"
  i = 0
  ts = set([t for c in lss for l in c for t in args(l)])
  syms = set([fa for t in list(ts) for fa in t.syms()])
  trs_gen = mk_gen(syms)
  for (i, trs) in enumerate(trss[:20]):
    (proven, technique), _ = check_trs(p, i, trs + trs_gen, nonground=True)
    if proven:
      #print("%s: %d trss NG proven at %d %s" % (p, len(trss), i, "(empty)" if trs == [] else ""))
      sys.stdout.flush()
      break
  return proven, technique

def check_non_ground(p, lss):
  pv,t = check_non_ground_polarity(p, lss, True)
  if pv:
    return (pv,t)
  return check_non_ground_polarity(p, lss, False)


def check_trss(p, lss, is_pos):
  trss = get_trss(p, lss, is_pos, covered=True)
  proven = False
  technique = ""
  for (i, trs) in enumerate(trss[:50]):
    (proven, technique), is_rel = check_trs(p, i, trs)
    if proven:
      #print("%s: %d trss proven at %d %s %s" % (p, len(trss), i, \
      #  "(empty)" if trs == [] else "(rel)" if is_rel else "", technique))
      break
  return proven, technique

# given clauses cs, check whether all-positive or all-negative ground
def check_ground_fixed(p, cs, flipped = False):
  fs = [c.formula for c in cs]
  lss = [literals(c) for c in fs]
  proven = False
  technique = ""
  if all_all_pos_all_ground(lss):
    proven, technique = check_trss(p, lss, True)
  if not proven and all_all_neg_all_ground(lss):
    proven, technique = check_trss(p, lss, False)
  #if not proven:
  #  proven, technique = check_non_ground(p, lss)
  
  bounded = (all_all_pos_all_ground(lss), all_all_neg_all_ground(lss))
  return (bounded, proven, technique)

# flip predicate p in f
def flip_formula(p, f):
  def flip(f):
    if isinstance(f, expr.Binop):
      return expr.Binop(f.op, flip(f.left), flip(f.right))
    elif isinstance(f, expr.Unop):
      if isinstance(f.arg, expr.Pred):
        if f.arg.name == p:
          return f.arg 
        else:
          return f
      else:
        print("unexpected for CNF")
        assert(False)
    elif isinstance(f, expr.Pred):
      if f.name == p:
        return expr.Unop("~", f) 
      else:
        return f
    else:
      print("unexpected for CNF")
      assert(False)
  
  fflip = flip(f.formula)
  return expr.Cnf(f.name, f.kind, fflip)

def check_ground(p, formulas, mode = "restrained"):
  res = check_ground_fixed(p, formulas)
  preds = [ atom(l).name for c in formulas for l in literals(c.formula) ]
  if res[1] or len(preds) > 50: # success
    return res, ""
  
  for pred in list(set(preds)):
    formulas_flipped = [ flip_formula(pred,f) for f in formulas]
    res_p_flipped = check_ground_fixed(p, formulas_flipped, flipped = True)
    if res_p_flipped[1]: # success
      if mode != "restrained":
        print("success flipping %s!" % pred)
      return res_p_flipped, "flipped " + pred
  return res, ""

def check(p, tptp_properties, verbose = False):
  not_applicable = ""
  MAX_SIZE = 500
  in_cnf = tptp_properties["vampire_axiom_clauses"] > 0
  #if not in_cnf:
  #  not_applicable = "not in cnf"
  if tptp_properties["vampire_axiom_clauses"] > MAX_SIZE:
    not_applicable = "too large"
  elif tptp_properties["vampire_equality_atoms"] > 0:
    not_applicable = "equality"
  #print(p)
  res = {"error": not_applicable, "success": False}
  if not not_applicable:
    filename = "Problems/" + p[:3] + "/" + p + ".p" if in_cnf else "cnfs/" + p + ".p"
    content = data.get_problem(filename)
    if not content or "negated_conjecture, ($false))." in content:
      res = {"error": "empty", "success": False}
    elif len([l for l in content.splitlines() if "cnf(" in l]) > MAX_SIZE:
      res = {"error": "too large", "success": False}
    else:
      #print(p + ": " + filename)
      formulas = tptp.parse_problem(content, verbose)
      ((bndp, bndn), success, technique, guarded, pvd, strat), msg = check_ground(p, formulas)
      res["pos_bounded"] = bndp
      res["neg_bounded"] = bndn
      res["success"] = success
      res["is_guarded"] = guarded
      res["is_stratified"] = strat
      res["is_pvd"] = pvd
      res["technique"] = technique
      res["flipped"] = msg
      #if success:
      #  print("SUCCESS")
      # need original file for status
      filename = "Problems/" + p[:3] + "/" + p + ".p"
      content = data.get_problem(filename)
      res["status"] = "SAT" if "% Status   : Satisfiable" in content else \
        "UNSAT" if "% Status   : Unsatisfiable" in content else \
        "THM" if "% Status   : Theorem" in content else \
        "CSAT" if "% Status   : CounterSatisfiable" in content else "UNK"

  return res


class PredicateVisitor(Visitor):
  def __init__(self):
    self.preds = set([])

  def visit_pred(self, p):
    self.preds.add(p.name)

def preds(cs):
  visitor = PredicateVisitor()
  for c in cs:
    c.accept(visitor)
  return visitor.preds

def split_disjoint(cs):
  if len(cs) == 0:
    return [([], [])]
  
  are_disjoint = lambda ps1, ps2: len(ps1.intersection(ps2)) == 0

  c = cs[0]
  ps = preds([c])
  splits_without_c = split_disjoint(cs[1:])
  splits = []
  for (cs1, cs2) in splits_without_c:
    if are_disjoint(preds(cs2), ps):
      splits += [(cs1 + [c], cs2)]
    if are_disjoint(preds(cs1), ps):
      splits += [(cs1, cs2 + [c])]
  return splits

def is_pvd_restrained_splittable(cs):
  if len(cs) > 30:
    return False

  def is_restrained(cs):
    ((bndp, bndn), success, _), _ = check_ground("xyz", [Cnf("",0,c) for c in cs])
    return bndp or bndn
 
  splits = split_disjoint(cs)
  for (cs1, cs2) in splits:
    if len(cs1) == 0 or len(cs2) == 0:
      continue
    ls1 = [literals(c) for c in cs1]
    ls2 = [literals(c) for c in cs2]
    if is_pvd(ls1) and is_restrained(cs2):
      print("SPLITTABLE")
      print("PVD")
      print([str(c) for c in cs1])
      print("RESTRAINED")
      print([str(c) for c in cs2])
      return True
    if is_pvd(ls2) and is_restrained(cs1):
      print("SPLITTABLE")
      print("PVD")
      print([str(c) for c in cs2])
      print("RESTRAINED")
      print([str(c) for c in cs1])
      return True
  return False
  

if __name__ == "__main__":
  features = get_problem_features()
  fs = {}
  for f in features.keys():
    if not ("=" in f):
      fs[f] = check(f, features[f])
  
  usable = [c for c in fs if fs[c]["success"]]
  print("<!-- %d total" % len(fs))
  print("%d not in CNF" % len([f for f in fs if "not in cnf" == fs[f]["error"]]))
  print("%d too large" % len([f for f in fs if "too large" == fs[f]["error"]]))
  print("%d equality" % len([f for f in fs if "equality" == fs[f]["error"]]))
  print("%d positively bounded" % len([f for f in usable if fs[f]["pos_bounded"]]))
  print("%d negatively bounded" % len([f for f in usable if fs[f]["neg_bounded"]]))
  print("%d successes -->" % len(usable))
  print("<table>")
  print("<tr><th class=\"thead\">problem</th><th class=\"thead\">status</th><th class=\"thead\">rating</th>")
  print("<th class=\"thead\">restrained</th><th>TRS</th><th class=\"thead\">properties</th><th></th><th></th></tr>")
  for u in usable:
    dom = u[0:3]
    href = "http://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=" + dom + "&File=" + u + ".p"
    print("<tr>")
    print("<td class=\"system\"><a href=\"%s\">%s</a></td>" % (href, u))
    print("<td>%s</td>" % fs[u]["status"])
    print("<td>%s</td>" % features[u]["rating"])
    # restrained
    bnd = "positive" if fs[u]["pos_bounded"] else "negative"
    trsfilename = "trss/" + u + ".trs"
    print("<td>%s</td>" % (bnd))
    if isfile(trsfilename):
      print("<td><a href=\"%s\">TRS</a></td>" % (trsfilename))
    else:
      print("<td><em>empty</em></td>")
    # other properties
    epr = "EPR" if features[u]["vampire_max_fun_arity"] == 0 else ""
    ground = "ground" if features[u]["num_variables"] == 0 else ""
    mon = "monadic" if features[u]["vampire_max_pred_arity"] <= 1 else ""
    two_var = "2var" if features[u]["vampire_max_variables_in_clause"] <= 2 and features[u]["vampire_max_fun_arity"] <= 0 else ""
    guarded = "guarded" if fs[u]["is_guarded"] else ""
    pvd = "PVD" if fs[u]["is_pvd"] else ""
    strat = "stratified" if fs[u]["is_stratified"] else ""
    none = "<!--none-->" if not(epr or mon or two_var or guarded or ground or pvd or strat) else ""
    #print("%s: %d (%s) (%.2f)  %s %d %s" % (u, bnd, fs[u]["technique"], features[u]["rating"], features[u]["source"], features[u]["vampire_axiom_clauses"], fs[u]["status"]))
    props = [epr, mon, two_var, guarded, ground, pvd, strat, none]
    props = [p for p in props if p]
    ps = fold_left(lambda s, p: s + (", " if s else "") + p, "", props)
    print("<td>%s</td>" % ps)
    sggs = "sggsruns/" + u + ".txt"
    print("<td><?php if (file_exists(\"%s\")) { ?><a href=\"%s\">sggs run</a><?php } ?></td>" % (sggs, sggs))
    print("<td>%s</td>" % fs[u]["flipped"])
    print("</tr>")
  #r = sum([features[u]["rating"] for u in usable]) / 117.0
  #print("average rating %.2f" % r)
  print("</table>")

  # 