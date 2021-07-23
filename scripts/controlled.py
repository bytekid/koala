import os, subprocess, multiprocessing, sys
import time
from os import listdir
from os.path import isfile, join
import json
import sys
sys.path.append('.')
import expr, data, tptp
from expr import Visitor, Var, Fun
from stratified import args
import shutil

MAX_TRS_COUNT = 100

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

def is_horn(ls):
  return len([l for l in ls if l.is_positive()]) <= 1

def is_neg_horn(ls):
  return len([l for l in ls if not l.is_positive()]) <= 1

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

def subset_vars(r, l):
  return r.vars().issubset(l.vars())

### create TRSs
def rules_for_clause(ls, is_pos):
  if forall(lambda l: l.is_positive(), ls) or \
     forall(lambda l: not l.is_positive(), ls):
     return [] # only mixed clauses are relevant since narrowing is used

  poss = [l for l in ls if l.is_positive()]
  negs = [l for l in ls if not l.is_positive()]
  (cover, to_cover) = (negs, poss) if is_pos else (poss, negs)
  #to_cover = [l for l in to_cover if not l.is_ground()]
  #cover = [l for l in cover if not l.is_ground()]

  trs = [(l,lp) for l in cover for lp in to_cover]
  return trs

def ruless_for_clause(ls, is_pos):
  poss = [l for l in ls if l.is_positive()]
  negs = [l for l in ls if not l.is_positive()]
  (cover, to_cover) = (negs, poss) if is_pos else (poss, negs)
  to_cover = [l for l in to_cover if not l.is_ground()] 

  def covering(lp):
    return [ln for ln in cover if lp.vars().issubset(ln.vars())]

  if exists(lambda l: len(covering(l)) == 0, to_cover):
    return None # some literal cannot be convered
  return [[(l,lp) for l in covering(lp)] for lp in to_cover]

def get_combinations_trss(p, lss, is_pos):
  rss_all = [ruless_for_clause(ls, is_pos) for ls in lss]
  if None in rss_all:
    return []
  
  rss = [rs for ls in lss for rsl in rss_all for rs in rsl if rs != []]
  cross_cnt = fold_left(lambda p, l: p * l, 1, [len(rs) for rs in rss ])
  #print("controlled: " + str(cross_cnt))
  if cross_cnt > 2000: # too large
    trss = [[rs[0] for rs in rss]] # just one TRS
  else:
    trss = cross([rs for rs in rss])[:20] # all combinations of rules, but at most 50 TRSs
  return trss

def run_ttt2(f, relative):
  cmd = "./sandbox 10 /home/bytekid/tools/ghm/ttt2 " + f
  cmd2 = "java -ea -jar ../aprove/aprove.jar -m wst -t 10 " + f
  #print(cmd)
  sys.stdout.flush()
  process = subprocess.Popen(cmd.split(), stdout=subprocess.PIPE)
  out, err = process.communicate()
  if err:
    print(err)
  if "MAYBE" in out:
    print("MAYBE" + f)
  if "YES" in out:
    return True, "TTT2"
  if relative: # AproVE does not like the relative format currently used
    return False, ""
  
  process = subprocess.Popen(cmd2.split(), stdout=subprocess.PIPE)
  out, err = process.communicate()
  success = "YES" in out
  if not success:
    os.remove(f)
  return success, "AProVE"
  


def is_permutative(l,r):
  def all_vars(ts):
    return forall(lambda v: isinstance(v, expr.Var), ts)
  var_args = all_vars(l.args) and all_vars(r.args)
  return l.name == r.name and var_args and l.vars() == r.vars()

def check_trs(p, trs, trs_rel):
  if not trs: # empty
    return True, "trivial"

  trs = list(set(trs))
  vars = set([v for (l, r) in trs for v in set(l.vars()).union(set(r.vars()))])
  var_str = fold_left(lambda s, v: s + " " + v, "", vars)
  trs_str = "(VAR " + var_str + ")\n"
  trs_str = trs_str + "(RULES \n"
  trs_sub = []
  for (l,r) in trs:
    (l,r) = atom(l), atom(r)
    if (l,r) in trs_sub or l == r:
      continue
    trs_sub.append((l,r))
    trs_str = trs_str + str(l) + " -> " + str(r) + "\n"
  for (l,r) in trs_rel:
    trs_str = trs_str + str(l) + " ->= " + str(r) + "\n"
  trs_str = trs_str + ")\n"
  relative = len(trs_rel) > 0
  filename = "trss/" + p + "_controlled.trs"
  rfile = open(filename, "w")
  rfile.write(trs_str)
  rfile.close()
  res, tool = run_ttt2(filename, relative)
  return res, tool
  
def mk_gen(syms):
  rs = []
  gen = expr.Fun("gen", [])
  for (f, a) in syms:
    rs.append((gen, expr.Fun(f, [gen for i in range(0,a)])))
  return rs

def check_non_ground_polarity1(p, lss, trs, is_pos):
  sys.stdout.flush()
  proven = False
  tool = ""
  ts = set([t for c in lss for l in c for t in args(l)])
  syms = set([fa for t in list(ts) for fa in t.syms()])
  trs_gen = mk_gen(syms)
  proven, tool = check_trs(p, trs, trs_gen)
  return proven, "Rgen " + tool

def check_non_ground_polarity2(p, trs, is_pos):
  
  def is_shallow(t):
    return forall(lambda ti: isinstance(ti, Var) or ti.is_ground(), t.args)

  def left_shallow(trs):
    return forall(lambda l: is_shallow(atom(l[0])), trs)

  if not left_shallow(trs):
    return False, ""

  proven, tool = check_trs(p, trs, [])
  if proven:
    return True, "LF+cT " + tool
  return False, ""

def check_narrow_term_trs(problem, lss, trs, is_pos):
  p, t =  check_non_ground_polarity1(problem, lss, trs, is_pos)
  if p:
    return p,t
  return check_non_ground_polarity2(problem, trs, is_pos)

def check_complete_cover(problem, lss, is_pos):
  trs = [ rl for ls in lss for rl in rules_for_clause(ls, is_pos)]
  return check_narrow_term_trs(problem, lss, trs, is_pos)

def check_controlled(problem, lss, is_pos):
  trss = get_combinations_trss(problem, lss, is_pos)
  proven = False
  technique = ""
  for (i, trs) in enumerate(trss[:MAX_TRS_COUNT]):
    (proven, technique) = check_narrow_term_trs(problem, lss, trs, is_pos)
    if proven:
      break
  return proven, technique

# given clauses cs, check whether all-positive or all-negative ground
#def check_neg_horn(p, cs):
#  fs = [c.formula for c in cs]
#  lss = [literals(c) for c in fs]
#  nlss = [ len([l for l in ls if not l.is_positive()]) > 1 for ls in lss]
#
#  proven = False
#  single_neg = forall(is_neg_horn, lss)
#  if not (single_neg) or True in nlss or len(fs) > 10:
#    return False, "", False, False, False
#   
#  proven, technique = check_complete_cover(p, lss, True)
#  return (proven, "neg horn " + technique, is_guarded(lss), is_pvd(lss), is_strat(fs))

#def check_horn(p, cs):
#  fs = [c.formula for c in cs]
#  lss = [literals(c) for c in fs]
#  nlss = [ len([l for l in ls if not l.is_positive()]) > 1 for ls in lss]
#
#  proven = False
#  horn = forall(is_horn, lss)
#  if not horn or True in nlss or len(fs) > 10:
#    return False, "", False, False, False
#   
#  proven, technique = check_controlled(p, lss, True)
#  return (proven, "horn " + technique, is_guarded(lss), is_pvd(lss), is_strat(fs))

def is_controlled(p, cs):
  lss = [literals(c) for c in [c.formula for c in cs]]
  horn = forall(is_horn, lss)
  neg_horn = forall(is_neg_horn, lss)
  
  is_controlled = False
  is_neg_controlled = False
  if horn:
    is_controlled = check_controlled(p, lss, True)[0]
  if neg_horn:
    is_neg_controlled = check_controlled(p, lss, False)[0]
  return ((horn, is_controlled), (neg_horn, is_neg_controlled))
  

#def check_sggs(p, cs):
#  fs = [c.formula for c in cs]
#  lss = [literals(c) for c in fs]
#  if len(fs) > 20:
#    return False, "", False, False, False
#   
#  proven, technique = check_complete_cover(p, lss, True)
#  return (proven, technique, is_guarded(lss), is_pvd(lss), is_strat(fs))
#
# flip predicate p in f
#def flip_formula(p, f):
#  def flip(f):
#    if isinstance(f, expr.Binop):
#      return expr.Binop(f.op, flip(f.left), flip(f.right))
#    elif isinstance(f, expr.Unop):
#      if isinstance(f.arg, expr.Pred):
#        if f.arg.name == p:
#          return f.arg 
#        else:
#          return f
#      else:
#        assert(False)
#    elif isinstance(f, expr.Pred):
#      if f.name == p:
#        return expr.Unop("~", f) 
#      else:
#        return f
#    else:
#      assert(False)
#  
#  fflip = flip(f.formula)
#  return expr.Cnf(f.name, f.kind, fflip)
#
#def flip_all_formula(f):
#  def flip(f):
#    if isinstance(f, expr.Binop):
#      return expr.Binop(f.op, flip(f.left), flip(f.right))
#    elif isinstance(f, expr.Unop):
#      if isinstance(f.arg, expr.Pred):
#        return f.arg
#      else:
#        assert(False)
#    elif isinstance(f, expr.Pred):
#      return expr.Unop("~", f)
#    else:
#      assert(False)
#  
#  fflip = flip(f.formula)
#  return expr.Cnf(f.name, f.kind, fflip)
#
#def check_narrow_term(p, formulas):
#  res = check_sggs(p, formulas) # check_fixed
#  preds = [ atom(l).name for c in formulas for l in literals(c.formula) ]
#  
#  if res[0] or len(preds) > 50: # success, or too many atoms
#    return res, ""
#  
#  fss = [("all", [ flip_all_formula(f) for f in formulas])]
#  for pred in list(set(preds)):
#    fss.append((pred, [ flip_formula(pred,f) for f in formulas]))
#  
#  for (pred, formulas_flipped) in fss:
#    res_p_flipped = check_sggs(p, formulas_flipped) # check_fixed
#    if res_p_flipped[0]: # success
#      print(" success flipping %s!" % pred)
#      return res_p_flipped, "flipped " + pred
#  return res, ""
#
