import sys
sys.path.append('.')
import expr, data, tptp
from collections import defaultdict
from expr import Visitor, Var, Fun, Pred

  
def fold_left(func, init, seq):
  acc = init
  for i in seq:
    acc = func(acc, i)
  return acc

def forall(pred, seq):
  return fold_left(lambda v, l: v and pred(l), True, seq)

def exists(pred, seq):
  return fold_left(lambda v, l: v or pred(l), False, seq)
  
def type_str(t):
  ts, tr = t
  s = ""
  for t in ts:
    s = s + (" x " if s else "") + str(t)
  return s + " -> " + str(tr)

class EPRVisitor(Visitor):
  def __init__(self):
    self.epr = True

  def visit_fun(self, f):
    if len(f.args) > 0:
      self.epr = False


class SortRefinementVisitor(Visitor):
  def __init__(self, cyclic_types, type_visitor):
    self.cyclic_types = cyclic_types
    self.type_visitor = type_visitor

  def visit_binop(self, f):
    f.left.accept(self)
    f.right.accept(self)
    l = f.left.get_cyclic_parts()
    r = f.right.get_cyclic_parts()
    f.set_cyclic_parts(None if not l and not r else l if not r else r if not l else f)
    return True

  def visit_unop(self, u):
    u.arg.accept(self)
    u.set_cyclic_parts(u if u.arg.get_cyclic_parts() else None)
    return True

  def visit_pred(self, p):
    (ts, _) = self.type_visitor.get_type(p)
    has_cyclic = len(set(ts).intersection(self.cyclic_types)) > 0
    p.set_cyclic_parts(p if has_cyclic else None)
    return True


class TypeVisitor(Visitor):
  def __init__(self):
    self.types = {}
    self.type_count = 0
    self.unify = []

  def get_var_type(self, name):
    if name in self.types:
      return self.types[name]
    self.types[name] = (None, self.type_count)
    self.type_count += 1
    #print("  assign %s type %d" % (name, self.types[name][1]))
    return self.types[name]

  def get_fun_type(self, name, arity):
    if name in self.types:
      return self.types[name]
    ts = range(self.type_count, self.type_count + arity)
    self.types[name] = (ts, self.type_count + arity)
    self.type_count = self.type_count + arity + 1
    #print("  assign %s type %s" % (name, type_str(self.types[name])))
    return self.types[name]

  def get_pred_type(self, name, arity):
    if name in self.types:
      return self.types[name]
    ts = range(self.type_count, self.type_count + arity)
    self.types[name] = (ts, None)
    self.type_count += arity
    #print("  assign %s type %s" % (name, type_str(self.types[name])))
    return self.types[name]

  def get_type(self, e):
    if isinstance(e, Var):
      return self.get_var_type(e.name)
    elif isinstance(e, Fun):
      return self.get_fun_type(e.name, len(e.args))
    elif isinstance(e, Pred):
      return self.get_pred_type(e.name, len(e.args))
    else:
      assert(False)

  def visit_pred(self, p):
    (ts, _) = self.get_type(p)
    ats = [ self.get_type(a)[1] for a in p.args]
    self.unify += zip(ts, ats)

  def visit_fun(self, f):
    (ts, _) = self.get_type(f)
    ats = [ self.get_type(a)[1] for a in f.args]
    self.unify += zip(ts, ats)


  def unify_types(self):
    ps = {}
    us = self.unify
    #print(us)
    while us:
      (a,b) = us[0]
      del us[0]
      if a == b:
        continue
      subst = lambda x: b if x == a else x 
      us = [ tuple((subst(c), subst(d))) for (c,d) in us]
      for p in ps:
        ps[p] = subst(ps[p])
      ps[a] = b
    
    def subst_all(typ):
      ts, t = typ
      tsub = ps[t] if t and t in ps else t
      return [ ps[u] if u in ps else u for u in ts], tsub
    
    # substitute type dictionary
    ts = {}
    for f in self.types:
      if self.types[f][0] != None: # not a variable
        ts[f] = subst_all(self.types[f])
        #print("  %s: %s" % (f, type_str(ts[f])))
    self.types = ts
    self.unify = []

def cyclic_types(types):
  edges = defaultdict(list)

  # build graph
  for f in types:
    targs, tres = types[f]
    if not targs or not tres: # predicate, constant or variable
      continue
    for t in targs:
      edges[t].append(tres)
  
  def successors(ns):
    nns = ns
    for n in ns:
      nns = nns.union(set(edges[n]))
    return ns if nns == ns else successors(nns)

  # find cyclic types
  cyclic = set([])
  for n in list(edges.keys()):
    if n in successors(set(edges[n])):
      cyclic.add(n)
  return cyclic

def are_acyclic(types):
  #print("cyclic types ", cyclic_types(types))
  return len(cyclic_types(types)) == 0

def is_epr(cs):
  visitor = EPRVisitor()
  for c in cs:
    c.accept(visitor)
  return visitor.epr
      
def is_stratified(cs):
  visitor = TypeVisitor()
  for c in cs:
    c.accept(visitor)
    visitor.unify_types()
  return are_acyclic(visitor.types)
      
def non_stratified_part(cs):
  tvisitor = TypeVisitor()
  for c in cs:
    c.accept(tvisitor)
    tvisitor.unify_types()
  cts = cyclic_types(tvisitor.types)
  cs2 = []
  svisitor = SortRefinementVisitor(cts, tvisitor)
  for c in cs:
    c.accept(svisitor)
    c2 = c.get_cyclic_parts()
    cs2 = cs2 + [c2] if c2 else cs2
  return cs2

if __name__ == "__main__":
  p = sys.argv[1]
  #print(p)
  #filename = "Problems/" + p[:3] + "/" + p + ".p"
  content = data.get_problem(p)
  cs = [c.formula for c in tptp.parse_problem(content, False)]
  print("stratified: %r " % is_stratified(cs))


def is_guarded(lss):
  def is_weakly_covering(l):
    # every functional subterm of literal l contains all variables in l
    vs = l.vars()
    ts = l.subterms()
    return forall(lambda t: vars(t) == vs if not t.is_var() and len(t.args) > 0 else True, ts)
  
  def vardepth1(l):
    ts = l.args if isinstance(l, expr.Pred) else l.arg.args
    return forall(lambda v: isinstance(v, expr.Var) or len(v.vars()) == 0, ts)

  def ground_clause(ls):
    return forall(lambda l: l.is_ground(), ls)

  for ls in lss:
    if ground_clause(ls):
      continue
    cov = forall(is_weakly_covering, ls)
    # variables in clause
    vs = fold_left(lambda xs, ys: xs.union(ys), set([]), [ l.vars() for l in ls])
    guard = exists(lambda l: (not l.is_positive()) and vardepth1(l), ls)
    fun_has_all_vars = forall(lambda l: vardepth1(l) or l.vars() == vs, ls)
    if not (cov and guard and fun_has_all_vars):
      return False
  
  return True

def is_pos(l):
  assert(isinstance(l, expr.Unop) or isinstance(l, expr.Pred))
  return isinstance(l, expr.Pred)

def is_neg(l):
  assert(isinstance(l, expr.Unop) or isinstance(l, expr.Pred))
  return isinstance(l, expr.Unop) and isinstance(l.arg, expr.Pred)

def args(l):
  assert(isinstance(l, expr.Unop) or isinstance(l, expr.Pred))
  return l.arg.args if isinstance(l, expr.Unop) else l.args


def max_depth(x, ls):
  ds = [t.maxDepth(x) for l in ls for t in args(l)]
  ds = [d for d in ds if d != None]
  return max (ds) if ds != [] else 0

def is_pvd(cs):
  for c in cs:
    c_plus = [ l for l in c if is_pos(l)]
    xs_plus = set([x for l in c_plus for x in l.vars()])
    c_minus = [ l for l in c if is_neg(l)]
    xs_minus = set([x for l in c_minus for x in l.vars()])
    if not (xs_plus.issubset(xs_minus)):
      return False
    for x in list(xs_plus):
      if (max_depth(x, c_plus) > max_depth(x, c_minus)):
        return False
  
  return True

def is_pvd1(cs):

  for c in cs:
    c_plus = [ l for l in c if is_pos(l)]
    xs_plus = set([x for l in c_plus for x in l.vars()])
    c_minus = [ l for l in c if is_neg(l)]
    xs_minus = set([x for l in c_minus for x in l.vars()])
    if not (xs_plus.issubset(xs_minus)):
      return False

    clause_ok = (len(c_minus) == 0)
    for l in c_minus:
      all_ge_depth = True
      for x in list(xs_plus):
        if (max_depth(x, c_plus) > max_depth(x, [l])):
          all_ge_depth = False
      if all_ge_depth:
        clause_ok = True
    if not clause_ok:
      return False
  return True

def is_ackermann_clause(c):
  xs = set([x for l in c for x in l.vars()])
  if len(xs) != 1:
    return (len(xs) == 0)
  else:
    x = xs.pop()
    return (max_depth(x, c) == 1)

def is_ackermann(cs):
  return forall(is_ackermann_clause, cs)
