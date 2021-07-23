import os, subprocess, multiprocessing, sys
from os import listdir
from os.path import isfile, join
import re
import tptp
import time
from expr import Expr, Term, Formula, Fun, Var, Quantified, Binop, Unop, Pred, \
  TypeExpr, Fof, Cnf, Include, Tff, Ite
from expr import Visitor
from index import FingerprintIndex
import timeout_decorator
import random
from collections import Counter
from numpy import mean
import json


sys.setrecursionlimit(800000)
TIMEOUT = 3600

def get_problem(file_name):
  file = open(file_name, "r")
  res = file.read()
  return res


##################### extract problem properties from TPTP comments ############
def get_properties(problem):
  data = {} 

  m = re.search("Number of formulae\s+:\s+(\d+)\s+\(\s*(\d+)\s+unit", problem)
  if m:
    data["num_formulae"] = int(m.groups()[0])
    data["num_unit"] = int(m.groups()[1])
  
  m = re.search("Number of atoms\s+:\s+(\d+)\s+\(\s*(\d+)\s+equality", problem)
  if m:
    data["num_atoms"] = int(m.groups()[0])
    data["num_equalities"] = int(m.groups()[1])
  
  m = re.search("Maximal formula depth\s+:\s*(\d+)\s+\(\s*(\d+)\s+average", problem)
  if m:
    data["max_formula_depth"] = int(m.groups()[0])
    data["avg_formula_depth"] = int(m.groups()[1])
  
  m = re.search("Maximal term depth\s+:\s*(\d+)\s+\(\s*(\d+)\s+average", problem)
  if m:
    data["max_term_depth"] = int(m.groups()[0])
    data["avg_term_depth"] = int(m.groups()[1])
    
  m = re.search("Number of connectives\s+:\s+(\d+)\s+\(\s*(\d+)\s+~;\s*(\d+)\s+\|;\s*(\d+)\s+&\)", problem)
  if m:
    data["num_connectives"] = int(m.groups()[0])
    data["num_not"] = int(m.groups()[1])
    data["num_|"] = int(m.groups()[2])
    data["num_&"] = int(m.groups()[3])
  m = re.search("\(\s+(\d+)\s+<=>;\s*(\d+)\s+=>;\s*(\d+)\s+<=;\s*(\d+)\s+<~>\)", problem)
  if m:
    data["num_<=>"] = int(m.groups()[0])
    data["num_=>"] = int(m.groups()[1])
    data["num_<="] = int(m.groups()[2])
    data["num_<~>"] = int(m.groups()[3])
  m = re.search("\(\s+(\d+)\s+~\|;\s*(\d+)\s+~&\s*\)", problem)
  if m:
    data["num_~|"] = int(m.groups()[0])
    data["num_~&"] = int(m.groups()[1])
  m = re.search("Number of predicates\s+:\s+(\d+)\s+\(\s+(\d+)\s+propositional;\s+([\d-]+) arity", problem)
  if m:
    data["num_predicates"] = int(m.groups()[0])
    data["num_propositional"] = int(m.groups()[1])
    arity = m.groups()[2] if m else None
    if arity:
      m = re.search("(\d+)-(\d+)", arity)
      if m:
        data["min_pred_arity"] = int(m.groups()[0])
        data["max_pred_arity"] = int(m.groups()[1])
  m = re.search("Number of functors\s+:\s+(\d+)\s+\(\s+(\d+)\s+constant;\s+([\d-]+) arity", problem)
  if m:
    data["num_functions"] = int(m.groups()[0]) 
    data["num_constants"] = int(m.groups()[1]) 
    arity = m.groups()[2] if m else None
    if arity:
      m = re.search("(\d+)-(\d+)", arity)
      if m:
        data["min_fun_arity"] = int(m.groups()[0])
        data["max_fun_arity"] = int(m.groups()[1])
  m = re.search("Number of variables\s+:\s+(\d+)\s+\(([^\)]+)\)", problem)
  if m:
    data["num_variables"] = int(m.groups()[0])
    details = m.groups()[1]
    m = re.search("\s+(\d+)\s+sgn;\s+(\d+)\s+!;\s+(\d+)\s+?", details)
    if m:
      data["num_singleton_vars"] = int(m.groups()[0])
      data["num_forall"] = int(m.groups()[1])
      data["num_exists"] = int(m.groups()[2])
    m = re.search("\s+(\d+)\s+singleton", details)
    if m:
      data["num_singleton_vars"] = int(m.groups()[0])

  m = re.search("Number of clauses\s+:\s+(\d+)\s+\(\s*(\d+)\s+non-Horn;\s*(\d+)\s+unit;\s*(\d+)\s+RR", problem)
  if m:
    data["num_clauses"] = int(m.groups()[0])
    data["num_non_horn_clauses"] = int(m.groups()[1])
    data["num_unit_clauses"] = int(m.groups()[2])
    data["num_rr_clauses"] = int(m.groups()[3])

  m = re.search("Maximal term depth\s+:\s+(\d+)\s+\(\s+(\d+)\s+average", problem)
  if m:
    data["max_term_depth"] = int(m.groups()[0])
    data["avg_term_depth"] = int(m.groups()[1])

  m = re.search("Source\s+:\s+\[([^\]]*)\]", problem)
  data["source"] = m.groups()[0] if m else "?"

  m = re.search("Rating\s+:\s+(\d+)\.(\d+)\s", problem)
  data["rating"] = float(m.groups()[0] + "." + m.groups()[1]) if m else -1

  data["is_EPR"] = 1 if "EPR" in problem else 0

  return data

########################## visitors to obtain properties #######################
class EqCountVisitor(Visitor):
  def __init__(self):
    self.count = 0

  def visit_pred(self, p):
    if p.name in ["=", "!="]:
      self.count = self.count + 1 

class RewriteVisitor(Visitor):
  def __init__(self, lhss, terms, num_clauses, is_epr):
    self.unif_count = 0
    self.match_count = 0
    self.index = FingerprintIndex.make(lhss + terms, num_clauses, is_epr)


  def visit_fun(self, f):
    u = len(self.index.unifiables(f))
    self.unif_count = self.unif_count + u
    if self.index.only_root: # unification and matching are the same
      self.match_count = self.match_count + u
    else:
      self.match_count = self.match_count + len(self.index.matching(f))


class LiteralVisitor:
  def __init__(self):
    self.atoms = [[], []]

  def positive_atoms(self):
    return self.atoms[0]

  def negative_atoms(self):
    return self.atoms[1]

  def eq_atoms(self):
    ep = [ a for a in self.atoms[0] if a.name == "="]
    en = [ a for a in self.atoms[1] if a.name == "="]
    return (ep, en)

  def non_eq_atoms(self):
    ep = [ a for a in self.atoms[0] if a.name != "="]
    en = [ a for a in self.atoms[1] if a.name != "="]
    return (ep, en)

  # approximation of unifiable positive/negative literals, only look at root
  def pred_unifiables_approximation(self):
    neg = self.atoms[1]
    pos = self.atoms[0]
    ncounter = Counter(neg)
    pcounter = Counter(pos)
    unifs = 0
    for pred in ncounter.keys():
      pc = pcounter[pred] if pred in pcounter else 0
      unifs = unifs + ncounter[pred] * pc
    return unifs

  # parity 0: negative
  def visit(self, f, parity = 0):
    if isinstance(f, Pred):
      if f.name != "!=":
        self.atoms[parity].append(f)
      else:
        self.atoms[1 - parity].append(Pred("=", f.args))
    elif isinstance(f, Unop):
      # negation
      self.visit(f.arg, 1 - parity)
    elif isinstance(f, Binop):
      (pos, neg) = (parity, 1 - parity)
      ops = {
        "&" : [(f.left, pos), (f.right, pos)],
        "|" : [(f.left, pos), (f.right, pos)],
        "~&" : [(f.left, neg), (f.right, neg)],
        "~|" : [(f.left, neg), (f.right, neg)],
        "=>" : [(f.left, neg), (f.right, pos)],
        "<=" : [(f.left, pos), (f.right, neg)],
        "<=>" : [(f.left, neg), (f.right, pos), (f.left, pos), (f.right, neg)],
        "<~>" : [(f.left, neg), (f.right, pos), (f.left, pos), (f.right, neg)]
      }
      for arg, par in ops[f.op]:
        self.visit(arg, par)
    elif isinstance(f, Quantified):
      self.visit(f.formula, parity)
    elif isinstance(f, Ite):
      self.visit(f.cond, parity)
      self.visit(f.cond, 1 - parity)
      self.visit(f.left, parity)
      self.visit(f.right, parity)
    elif isinstance(f, TypeExpr):
      pass
    else:
      print(f)
      assert(False)


class QVisitor(Visitor):
  def __init__(self):
    self.last_quantifier = None
    self.alternations = 0
  
  def visit_quantified(self, q):
    if self.last_quantifier and self.last_quantifier != q.quantifier:
      self.alternations = self.alternations + 1 
    self.last_quantifier = q.quantifier

class BooleanVisitor(Visitor):
  def __init__(self):
    self.atoms = []
    self.num_not = 0
    self.binops = {"|": 0,"&": 0,"~|": 0,"~&": 0,"<=": 0,"=>": 0,"<=>": 0,"<~>": 0}
    self.last_quantifier = None

  def visit_pred(self, p):
    self.atoms.append(p.name if p.name != "!=" else "=")
    if p.name == "!=":
      self.num_not = self.num_not + 1

  def visit_binop(self, b):
    self.binops[b.op] = self.binops[b.op] + 1

  def visit_unop(self, b):
    self.num_not = self.num_not + 1

  def count(self):
    return len(self.atoms)

  def predicate_count(self):
    return len(set(self.atoms))

  def equality_count(self):
    return len([a for a in self.atoms if a == "="])

  def connective_count(self):
    return reduce(lambda sum, k: sum + self.binops[k], self.binops.keys(), self.num_not)


class FunCountVisitor(Visitor):
  def __init__(self):
    self.funs = {}
    self.arities = {}

  def visit_fun(self, p):
    f = p.name
    self.arities[f] = len(p.args)
    self.funs[f] = 1 if not (f in self.funs) else self.funs[f] + 1

  def count(self):
    return len(self.funs.values())

  def countConsts(self):
    return len([self.funs[f] for f in self.funs.keys() if self.arities[f] == 0])

  def occurrence_count(self, f):
    return self.funs[f]


def get_depths(all):
  tds = []
  fds = []
  for f in all:
    fds.append(f.depth())
    tds = tds + f.termDepths()
  return (mean(fds), mean(tds), max(fds), max(tds))

class VarCountVisitor(Visitor):
  def __init__(self):
    self.vars = []
    self.rebound_count = 0
    self.var_count = 0
    self.forall_count = 0
    self.exists_count = 0
  
  def visit_var(self, v):
    self.vars.append(v.name)
  
  def visit_quantified(self, q):
    for x in q.vars:
      if x.name in self.vars:
        self.vars.append(x.name + str(self.rebound_count))
        self.rebound_count = self.rebound_count + 1
      if q.quantifier == "!":
        self.forall_count = self.forall_count + 1
      elif q.quantifier == "?":
        self.exists_count = self.exists_count + 1

  def nextFormula(self):
    self.var_count = self.var_count + len(set(self.vars))
    self.vars = []

###### read problems and extract properties ####################################
def is_rewrite_rule(rule):
  l, r = rule
  if isinstance(l, Var):
    return False
  l_vars = l.vars()
  for v in r.vars():
    if not v in l_vars:
      return False
  return True

def compute_properties(p, tptp_properties, verbose = False):
  start = time.time()
  formulas = tptp.parse_problem(p, verbose)
  parse_time = (time.time() - start)
  start = time.time()
  log = ""
  properties = {}
  #print(properties)

  def property(key):
     return tptp_properties[key] if key in tptp_properties else None
  
  # sanity check: compare with TPTP comments
  def compare(counted, in_tptp, what):
    if verbose or (counted != in_tptp and in_tptp != None):
      return ("  " + str(counted) + " (vs " + str(in_tptp) + ") " + what + "\n")
    return ""
 
  cnfs = [f.formula for f in formulas if isinstance(f,Cnf)]
  fofs = [f.formula for f in formulas if isinstance(f,Fof)]
  tffs = [f.formula for f in formulas if isinstance(f,Tff)] # no type formulas
  all = cnfs + fofs + tffs

  properties = tptp_properties.copy()

  ### count clauses/formulas (only one property)
  if "num_formulae" in tptp_properties:
    num_p = tptp_properties["num_formulae"]
    log = log + compare(len(fofs + tffs), num_p, "formulae")
    properties["num_formulae"] = len(all)
  if "num_clauses" in tptp_properties:
    num_p = tptp_properties["num_clauses"]
    log = log + compare(len(cnfs), num_p, "clauses ")
    del properties["num_clauses"]
    properties["num_formulae"] = len(all)

  ### count predicates
  visitor = BooleanVisitor()
  for f in all:
    f.accept(visitor)
  log = log + compare(visitor.count(), property("num_atoms"), "atoms")
  properties["num_atoms"] = visitor.count()
  log = log + compare(visitor.predicate_count(), property("num_predicates"), "predicates")
  properties["num_predicates"] = visitor.predicate_count()
  log = log + compare(visitor.predicate_count(), property("num_equality"), "equalities")
  properties["num_equalities"] = visitor.equality_count()

  num_unit = len([u for u in all if not(isinstance(u, TypeExpr)) and u.is_literal()])
  tptp_unit = property("num_unit")
  if not tptp_unit:
    tptp_unit = property("num_unit_clauses")
  log = log + compare(num_unit, tptp_unit, "units")
  properties["num_units"] = num_unit
  properties["is_UEQ"] = 1 if num_unit == len(all) else 0

  log = log + compare(visitor.connective_count(), property("num_connectives"), "connectives")
  properties["num_connectives"] = visitor.connective_count()
  log = log + compare(visitor.num_not, property("num_not"), "nots")
  properties["num_not"] = visitor.num_not
  log = log + compare(visitor.binops["&"], property("num_&"), "ands")
  properties["num_&"] = visitor.binops["&"]

  log = log + compare(visitor.binops["|"], property("num_|"), "ors")
  properties["num_|"] = visitor.binops["|"]

  log = log + compare(visitor.binops["~&"], property("num_~&"), "nands")
  properties["num_~&"] = visitor.binops["~&"]
  
  log = log + compare(visitor.binops["~|"], property("num_~|"), "nors")
  properties["num_~|"] = visitor.binops["~|"]

  log = log + compare(visitor.binops["<=>"], property("num_<=>"), "iffs")
  properties["num_<=>"] = visitor.binops["<=>"]

  log = log + compare(visitor.binops["=>"], property("num_=>"), "implies")
  properties["num_=>"] = visitor.binops["=>"]
  
  log = log + compare(visitor.binops["<="], property("num_<="), "implies left")
  properties["num_<="] = visitor.binops["<="]

  log = log + compare(visitor.binops["<~>"], property("num_<~>"), "niffs")
  properties["num_<~>"] = visitor.binops["<~>"]

  ### count variables
  visitor = VarCountVisitor()
  for f in all:
    f.accept(visitor)
    visitor.nextFormula()
  log = log + compare(visitor.var_count, property("num_variables"), "variables")
  properties["num_variables"] = visitor.var_count
  log = log + compare(visitor.forall_count, property("num_forall"), "universal variables")
  properties["num_forall"] = visitor.forall_count
  log = log + compare(visitor.exists_count, property("num_exists"), "existential variables")
  properties["num_exists"] = visitor.exists_count

  ### count function symbols
  fvisitor = FunCountVisitor()
  for f in all:
    f.accept(fvisitor)
  n = property("num_functions")
  log = log + compare(fvisitor.count(), n, "function symbols")
  properties["num_functions"] = fvisitor.count()
  c = property("num_constants")
  log = log + compare(fvisitor.countConsts(), c, "constants")
  properties["num_constants"] = fvisitor.countConsts()

  #print("before unification")
  ### count unifiable positive and negative literals (not counting equality)
  vis = LiteralVisitor()
  for f in all:
    vis.visit(f)
  ps, ns = vis.non_eq_atoms()
  ps = [p.rename() for p in ps]
  idx = FingerprintIndex.make(ns, len(all), properties["is_EPR"])
  unifs = 0
  if len(all) < 10000:
    for p in ps:
      unifs = unifs + len(idx.unifiables(p))
  else:
    unifs = vis.pred_unifiables_approximation()
  properties["num_unifiable_pos_neg"] = unifs
  #print("after unification (1)")

  eqs, _ = vis.eq_atoms()
  # collect non-variable terms on one side of equation
  # TODO: take orientability into account?
  if eqs:
    terms = []
    lhss = []
    for e in eqs:
      lhs, rhs = e.args
      if is_rewrite_rule((lhs, rhs)):
        lhss.append(lhs)
      elif isinstance(lhs, Fun):
        terms.append(lhs)
      if is_rewrite_rule((rhs, lhs)):
        lhss.append(rhs)
      elif isinstance(rhs, Fun):
        terms.append(rhs)
    if len(all) < 10000:
      rew_visitor = RewriteVisitor(lhss, terms, len(all), properties["is_EPR"])
      for f in all:
        f.accept(rew_visitor)
      properties["num_match_eq"] = rew_visitor.match_count
      properties["num_unif_eq"] = rew_visitor.unif_count
    else: # very large, approximate by counting root symbol occurrences
      unifs = 0
      for t in terms:
        root = t.name
        unifs = unifs + fvisitor.occurrence_count(root)
      properties["num_match_eq"] = unifs
      properties["num_unif_eq"] = unifs
  else:
    properties["num_match_eq"] = 0
    properties["num_unif_eq"] = 0
  #print("after unification (2)")
  
  # formula/term depth
  if not("max_formula_depth" in properties and "avg_formula_depth" in properties):
    (af, at, mf, mt) = get_depths(all)
    properties["avg_formula_depth"] = af
    properties["avg_term_depth"] = at
    properties["max_formula_depth"] = mf
    properties["max_term_depth"] = mt

  analysis_time = (time.time() - start)
  return (properties, log, parse_time, analysis_time)

def estimate_properties(p, tptp_properties, size, verbose = False):
  properties = {}
  log = ""
  parse_time = -1
  start = time.time()

  def property(key, deflt):
     return tptp_properties[key] if key in tptp_properties else deflt
  
  properties["num_formulae"] = size
  atoms = property("num_atoms", size * 3)
  properties["num_atoms"] = atoms
  properties["num_predicates"] = property("num_predicates", size / 3)
  properties["num_equalities"] = property("num_equalities", 0)
  properties["num_units"] = property("num_unit", 0)
  properties["is_UEQ"] = 1 if properties["num_units"] == size else 0
  properties["num_connectives"] = property("num_not", 0)
  properties["num_not"] = property("num_connectives", 0)
  properties["num_&"] = property("num_&", 0)
  properties["num_|"] = property("num_|", 0)
  properties["num_~&"] = property("num_~&", 0)
  properties["num_~|"] = property("num_~|", 0)
  properties["num_<=>"] = property("num_<=>", 0)
  properties["num_=>"] = property("num_=>", 0)
  properties["num_<="] = property("num_<=", 0)
  properties["num_<~>"] = property("num_<~>", 0)
  properties["num_variables"] = property("num_variables", size)
  properties["num_forall"] = property("num_forall", 0)
  properties["num_exists"] = property("num_exists", 0)
  properties["num_functions"] = property("num_functions", 0)
  properties["num_constants"] = property("num_constants", 0)
  properties["is_EPR"] = property("is_EPR", 0)
  properties["source"] = property("source", "TPTP")
  # wild guess
  if properties["num_not"] > 0:
    p = properties["num_predicates"]
    guess = properties["num_not"] * (atoms - properties["num_not"]) / (p * p)
    properties["num_unifiable_pos_neg"] = guess if guess > atoms else sys.maxint
  else:
    properties["num_unifiable_pos_neg"] = atoms * atoms / 4
  
  if properties["num_equalities"] == 0:
    properties["num_match_eq"] = 0
    properties["num_unif_eq"] = 0
  else:
    properties["num_match_eq"] = properties["num_equalities"] * atoms / 8
    properties["num_unif_eq"] = properties["num_equalities"] * atoms / 4


  analysis_time = (time.time() - start)
  return (properties, log, parse_time, analysis_time)

def all_properties(p, verbose = False):
  ps = get_properties(p)
  #print(ps)
  num_formulae = ps["num_clauses"] if "num_clauses" in ps else ps["num_formulae"]
  num_atoms = ps["num_atoms"] if "num_atoms" in ps else 0
  max_depth = ps["max_formula_depth"] if "max_formula_depth" in ps else 0
  max_tdepth = ps["max_term_depth"] if "max_term_depth" in ps else 0
  
  if False:# and num_formulae > 50000 or num_atoms > 20000 or max_depth > 5000 or max_tdepth > 30:
    print("estimate")
    return estimate_properties(p, ps, num_formulae, verbose)
  else:
    return compute_properties(p, ps, verbose)

def features(data):

  msg = ""
  for k in property_list:
    msg = msg + ("\n  " if len(msg) > 0 else "  ") + k + ": " + str(data[k])
  '''
  s =  reduce(lambda s, k: s + " " + str(data[k]), property_list, "")
  return (s, msg)
  '''
  return json.dumps(data,indent=2), msg

def show_job(job):
  print(str(job["number"]) + ": " + job["problem"])
  print(job["feature_string"])
  if job["logs"]:
    print(job["logs"])
  print(" %.2f + %.2f seconds\n" % (job["parse_time"], job["analysis_time"]))
  sys.stdout.flush()


@timeout_decorator.timeout(TIMEOUT, timeout_exception=StopIteration)
def work(job, verbose=False):
  file_name = job["problem"]
  print("starting " + str(job["number"]) + ": " + file_name + " " + str(os.getpid()))
  sys.stdout.flush()
  try:
    content = get_problem(file_name)
    sys.stdout.flush()
    (data, logs, parse_time, analysis_time) = all_properties(content, verbose)
    fvec, fmsg = features(data)
    job["feature_vector"] = fvec
    job["feature_string"] = fmsg
    job["logs"] = logs
    job["parse_time"] = parse_time
    job["analysis_time"] = analysis_time
    show_job(job)
    base=os.path.basename(file_name)
    parts = os.path.splitext(base)
    rfile = open("features/" + parts[0] + ".txt", "w")
    rfile.write(job["feature_vector"] + "\n")
  except StopIteration:
    print(str(job["number"]) + ": " + file_name + " timed out")
  return job

def do(job, verbose=False):
  try:
    return work(job,verbose)
  except timeout_decorator.TimeoutError:
    print (job["problem"] + " timed out\n")
    job["features"] = []
    job["logs"] = ""
    job["parse_time"] = 0
    job["analysis_time"] = TIMEOUT
    return job

def show(results):
  print("all results:")
  #for job in results:
  #  show_job(job)

def by_bench_parallel(data, num_procs=4):
  jobs = []
  for problem in data:
    parts = os.path.splitext(os.path.basename(problem))
    feature_file = "features/" + parts[0] + ".txt"
    if not (os.path.isfile(feature_file)):
      jobs.append({ "number" : len(jobs), "problem" : problem})
  
  random.shuffle(jobs)
  pool = multiprocessing.Pool(num_procs)
  results = pool.map_async(do, jobs)
  pool.close()
  pool.join()
  show(results.get())
