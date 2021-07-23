from abc import ABCMeta, abstractmethod
from numpy import mean

# expressions
class Expr:
  __metaclass__ = ABCMeta

  @abstractmethod
  def accept(self, visitor):
      pass

  def set_cyclic_parts(self, b):
    self.cyclic_sorts = b

  def get_cyclic_parts(self):
    return self.cyclic_sorts

      
class NotUnifiable(Exception):
  pass
      

class NotMatchable(Exception):
  pass


class Term(Expr):
  def __init__(self):
    pass

  def __str__(self):
    return ""

  def vars(self):
    pass

  def rename(self):
    pass

  def depth(self):
    pass

  @staticmethod
  def compose(sigma, tau): # tau after sigma
    rho = dict([ (x, sigma[x].substitute(tau)) for x in sigma.keys()])
    for y in tau.keys():
      if y not in rho:
        rho[y] = tau[y]
    return rho

  @staticmethod
  def unify_all(ts):
    sub = {}
    while ts:
      s0, t0 = ts[0]
      ts = ts[1:]
      # skip occurs check for speed?
      if isinstance(s0, Var) and (t0.name == s0.name or not (s0.name in t0.vars())):
        assert(isinstance(t0, Var) or isinstance(t0, Fun))
        if isinstance(t0, Var) and t0.name == s0.name:
          continue
        rho = {s0.name : t0}
        #sub = Term.compose(sub, rho)
        ts = [(s.substitute(rho), t.substitute(rho)) for (s,t) in ts]
      elif isinstance(t0, Var) and not (t0.name in s0.vars ()):
        rho = {t0.name : s0}
        #sub = Term.compose(sub, rho)
        ts = [(s.substitute(rho), t.substitute(rho)) for (s,t) in ts]
      elif isinstance(s0, Fun) and isinstance(t0, Fun) and s0.name == t0.name:
          ts = ts + zip(s0.args, t0.args)
      else:
        raise NotUnifiable
    return sub

  def unify(self, t):
    return Term.unify_all([(self, t)])

  @staticmethod
  def match_all(ts):
    sub = {}
    while ts:
      s0, t0 = ts[0]
      ts = ts[1:]
      if isinstance(t0, Var):
        rho = {t0.name : s0}
        #sub = Term.compose(sub, rho)
        ts = [(s, t.substitute(rho)) for (s,t) in ts]
      elif isinstance(s0, Fun) and isinstance(t0, Fun) and s0.name == t0.name:
          ts = ts + zip(s0.args, t0.args)
      else:
        raise NotMatchable
    return sub

  def matches(self, pattern):
    try:
      Term.match_all([(self,pattern)])
      return True
    except NotMatchable:
      return False

  def unifiable(self, t):
    try:
      self.unify(t)
      return True
    except NotUnifiable:
      return False

class Var(Term):
  def __init__(self, c):
    assert(isinstance(c, basestring))
    self.name = c

  def __str__(self):
    return str(self.name)

  def accept(self, visitor):
    visitor.visit_var(self)

  def vars(self):
    return [self.name]

  def is_linear(self):
    return True

  def syms(self):
    return []

  def subterms(self):
    return [self]

  def rename(self):
    return Var("X" + self.name)

  def is_var(self):
    return True

  def substitute(self, rho):
    return rho[self.name] if self.name in rho else self

  def depth(self):
    return 0

  def maxDepth(self, x):
    return 0 if self.name == x else None


class Fun(Term):
  def __init__(self, name, args):
    assert(isinstance(name, basestring))
    self.name =  name
    self.args = args

  def root(self):
    return self.name

  def is_var(self):
    return False

  def __str__(self):
    s = ""
    for a in self.args:
      s = s + ("" if len(s) == 0 else ", ") + str(a)
    return self.name + "(" + s + ")"
  
  def accept(self, visitor):
    stop = visitor.visit_fun(self)
    if not (stop == visitor.STOP_RECURSION):
      for a in self.args:
        a.accept(visitor)

  def vars(self):
    return reduce(lambda vs, a: vs + a.vars(), self.args, [])
  
  def is_linear(self):
    vs = set([])
    for a in self.args:
      avs = set(a.vars())
      if not a.is_linear() or len(avs.intersection(vs)) > 0:
        return False
      vs = vs.union(avs)
    return True
  
  def is_ground(self):
    return len(self.vars()) == 0

  def syms(self):
    return reduce(lambda vs, a: vs + a.syms(), self.args, [(self.name, len(self.args))])

  def subterms(self):
    return reduce(lambda vs, a: vs + a.subterms(), self.args, [self])
    
  def rename(self):
    return Fun(self.name, [a.rename() for a in self.args]) 
    
  def substitute(self, rho):
    return Fun(self.name, [a.substitute(rho) for a in self.args]) 

  def depth(self):
    return 1 + max([a.depth() for a in self.args]) if self.args != [] else 0

  def maxDepth(self, x):
    ds = [a.maxDepth(x) for a in self.args] 
    ds = [d for d in ds if d != None]
    return None if ds == [] else 1 + max(ds)
 

class Formula(Expr):
  def __init__(self):
    pass

  def __str__(self):
    return ""

  @abstractmethod
  def accept(self, visitor):
      pass

  @abstractmethod
  def depth(self):
      pass

  @abstractmethod
  def termDepths(self):
      pass

  def is_literal(self):
    return False


class Pred(Expr):
  def __init__(self, name, args):
    assert(isinstance(name, basestring))
    self.name =  name
    self.args = args

  def root(self):
    return self.name

  def setName(self, n):
    self.name = n

  def __str__(self):
    s = ""
    for a in self.args:
      s = s + ("" if len(s) == 0 else ", ") + str(a)
    return self.name + "(" + s + ")"

  def is_literal(self):
    return True
  
  def accept(self, visitor):
    stop = visitor.visit_pred(self)
    if not (stop == visitor.STOP_RECURSION):
      for a in self.args:
        a.accept(visitor)

  def rename(self):
    return Pred(self.name, [a.rename() for a in self.args])

  def unifiable(self, p):
    if not (isinstance(p, Pred)) or self.name != p.name:
      return False
    try:
      Term.unify_all(zip(self.args, p.args))
      return True
    except NotUnifiable:
      return False

  def depth(self):
    return 0

  def termDepths(self):
    return [ a.depth() for a in self.args]

  def vars(self):
    return set(reduce(lambda xs, ys: xs + ys, [ a.vars() for a in self.args], []))
  
  def is_linear(self):
    vs = set([])
    for a in self.args:
      avs = set(a.vars())
      if not a.is_linear() or len(avs.intersection(vs)) > 0:
        return False
      vs = vs.union(avs)
    return True

  def subterms(self):
    return set(reduce(lambda xs, ys: xs + ys, [ a.subterms() for a in self.args], []))
  
  def is_ground(self):
    return len(self.vars()) == 0

  def is_positive(self):
    return True
    
  def substitute(self, rho):
    return Pred(self.name, [a.substitute(rho) for a in self.args])


class Unop(Formula):

  def __init__(self, op, v):
    self.op = op
    self.arg = v

  def __str__(self):
    op = self.op
    return op + "(" + str(self.arg) + ")"

  def is_literal(self):
    return self.arg.is_literal()

  def accept(self, visitor):
    stop = visitor.visit_unop(self)
    if not (stop == visitor.STOP_RECURSION):
      self.arg.accept(visitor)

  def depth(self):
    return 1 + self.arg.depth()

  def termDepths(self):
    return self.arg.termDepths()

  def vars(self):
    return self.arg.vars()

  def subterms(self):
    return self.arg.subterms()

  def is_ground(self):
    return self.arg.is_ground()

  def is_positive(self):
    assert(self.op == "~")
    return False

class Binop(Formula):

  def __init__(self, op, a, b):
    self.op = op
    self.left = a
    self.right = b

  def __str__(self):
    return "(" + str(self.left) + " " + self.op + " " + str(self.right) + ")"

  def accept(self, visitor):
    stop = visitor.visit_binop(self)
    if not (stop == visitor.STOP_RECURSION):
      self.left.accept(visitor)
      self.right.accept(visitor)

  def depth(self):
    return 1 + max(self.left.depth(), self.right.depth())

  def termDepths(self):
    return self.left.termDepths() + self.right.termDepths()

class Ite(Formula):

  def __init__(self, cond, a, b):
    self.cond = cond
    self.left = a
    self.right = b

  def __str__(self):
    return "ite(" + str(self.cond) + ", " + str(self.left) + ", " +\
      str(self.right) + ")"

  def accept(self, visitor):
    stop = visitor.visit_ite(self)
    if not (stop == visitor.STOP_RECURSION):
      self.cond.accept(visitor)
      self.left.accept(visitor)
      self.right.accept(visitor)

  def depth(self):
    return 1 + max(self.cond.depth(), self.left.depth(), self.right.depth())

  def termDepths(self):
    return self.left.termDepths() + self.right.termDepths() + self.cond.termDepths()


class Quantified(Formula):

  def __init__(self, q, vs, f):
    assert(q == "?" or q == "!")
    self.quantifier = q
    self.vars = [vs] if isinstance(vs, Var) else vs
    self.formula = f

  def __str__(self):
    q = self.quantifier
    f = self.formula
    vs =  reduce(lambda s, v: s + " " + str(v), self.vars, "")
    return "(" + q + vs + ". " + str(f) + ")"

  def is_literal(self):
    return self.formula.is_literal()

  def accept(self, visitor):
    stop = visitor.visit_quantified(self)
    if not (stop == visitor.STOP_RECURSION):
      self.formula.accept(visitor)

  def depth(self):
    return 1 + self.formula.depth()

  def termDepths(self):
    return self.formula.termDepths()


class TypeExpr(Expr):
  def __init__(self):
    pass

  def accept(self, visitor):
    visitor.visit_type(self)

  def __str__(self):
    print("(some type)")


class Cnf:
  def __init__(self, n, k, f):
    self.name = n
    self.kind = k
    self.formula = f

  def __str__(self):
    return str(self.formula)

class Fof:
  def __init__(self, n, k, f):
    self.name = n
    self.kind = k
    self.formula = f

  def __str__(self):
    return str(self.formula)

class Tff:
  def __init__(self, n, k, f):
    self.name = n
    self.kind = k
    self.formula = f

  def __str__(self):
    return str(self.formula)

class Include:
  def __init__(self, n):
    self.file = n


# visitor
class Visitor:
    STOP_RECURSION = True
    @abstractmethod
    def visit_var(self, element):
        pass

    @abstractmethod
    def visit_fun(self, element):
        pass

    @abstractmethod
    def visit_pred(self, element):
        pass

    @abstractmethod
    def visit_quantified(self, element):
        pass

    @abstractmethod
    def visit_binop(self, element):
        pass

    @abstractmethod
    def visit_ite(self, element):
        pass

    @abstractmethod
    def visit_unop(self, element):
        pass

    @abstractmethod
    def visit_type(self, element):
        pass
