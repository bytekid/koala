from abc import ABCMeta, abstractmethod
from expr import *

# expressions
class Letter:
  __metaclass__ = ABCMeta


class A(Letter):
  id = 1000

  def __init__(self):
    pass

  def __str__(self):
    return "A"

  def hash(self):
    return self.id


class B(Letter):
  id = 1001

  def __init__(self):
    pass

  def __str__(self):
    return "B"
  
  def hash(self):
    return self.id


class N(Letter):
  id = 1002

  def __init__(self):
    pass

  def __str__(self):
    return "N"

  def hash(self):
    return self.id


class F(Letter):
  def __init__(self, f):
    self.name = f

  def __str__(self):
    return "F" + self.name

  def hash(self):
    return ord(self.name[0])


class Fingerprint:

  # number positions from 0
  @staticmethod
  def letter_at(t, pos):
    if isinstance(t, Var):
      return A() if pos == [] else B()
    else:
      assert(isinstance(t, Fun) or isinstance(t, Pred))
      if pos == []:
        return F(t.root())
      else:
        i = pos[0]
        pos_rest = pos[1:]
        if i >= len(t.args):
          return N()
        else:
          return Fingerprint.letter_at(t.args[i], pos_rest)

  def __init__(self, term, poss):
    assert(isinstance(term, Term) or isinstance(term, Pred))
    self.letters = [Fingerprint.letter_at(term, p) for p in poss]

class FingerprintIndex:
  def __init__(self, num_clauses, is_epr):
    self.table = {}
    self.tset = []
    self.is_large = num_clauses > 9999
    self.is_very_large = num_clauses > 20000
    self.only_root = self.is_very_large
    if not self.is_large and not is_epr:
      self.poss = [[],[0], [1], [2], [0,0], [0,1], [1,0], [1,1]]
    elif not self.is_very_large:
      self.poss = [[],[0], [1]]
    else:
      self.poss = [[]]

  def add(self, term):
    fp = Fingerprint(term, self.poss)
    table = self.table
    id = ""
    for i,l in enumerate(fp.letters):
      id = l.hash()
      if not (id in table):
        table[id] = {} if i < len(fp.letters) - 1 else []
      table = table[id]
    table.append(term)
    self.tset.append(term)

  @staticmethod
  def make(terms, num_clauses, is_epr):
    idx = FingerprintIndex(num_clauses, is_epr)
    for t in terms:
      idx.add(t)
    return idx

  def matching(self, term):
    fp = Fingerprint(term, self.poss)
    result = []

    def filter(rs):
      return rs if len(rs) > 50 else [ t for t in rs if term.matches(t)]

    def retrieve(tab, tletters):
      if len(tletters) == 0: # base case, tab is result set in leaf of tree
        result.extend(filter(tab))
        return

      def ret(tab, id, lets):
        if id in tab:
          retrieve(tab[id], lets)
      
      tl = tletters[0]
      id = tl.hash()
      tlrest = tletters[1:]
      if isinstance(tl, F):
        ret(tab, id, tlrest)
        ret(tab, A.id, tlrest)
        ret(tab, B.id, tlrest)
      elif isinstance(tl, A):
        ret(tab, A.id, tlrest)
        ret(tab, B.id, tlrest)
      elif isinstance(tl, B):
        ret(tab, B.id, tlrest)
      elif isinstance(tl, N):
        ret(tab, B.id, tlrest)
        ret(tab, N.id, tlrest)

    retrieve(self.table, fp.letters)
    #for t in self.tset:
    #  if term.matches(t) and not t in result:
    #    print(term.toString() + " matches " + t.toString() + " but not returned")
    if term in result:
      result.remove(term)
    return result

  def unifiables(self, term):
    fp = Fingerprint(term, self.poss)
    result = []

    def filter(rs):
      return rs if len(rs) > 50 else [ t for t in rs if term.unifiable(t)]

    def retrieve(tab, tletters):
      if len(tletters) == 0:
        result.extend(filter(tab))
        return

      def ret(tab, id, lets):
        if id in tab:
          retrieve(tab[id], lets)

      def all(tab, lets, but = None):
        for k in tab.keys():
          if not but or k != but:
            retrieve(tab[k], lets)
      
      tl = tletters[0]
      id = tl.hash()
      tlrest = tletters[1:]
      if isinstance(tl, F):
        ret(tab, id, tlrest)
        ret(tab, A.id, tlrest)
        ret(tab, B.id, tlrest)
      elif isinstance(tl, A):
        all(tab, tlrest, but = N.id)
      elif isinstance(tl, B):
        all(tab, tlrest)
      else:
        ret(tab, B.id, tlrest)
        ret(tab, N.id, tlrest)

    retrieve(self.table, fp.letters)
    #for t in self.tset:
    #  if term.unifiable(t) and not t in result:
    #    print(term.toString() + " unifies with " + t.toString() + " but not returned")
    if term in result:
      result.remove(term)
    return result


