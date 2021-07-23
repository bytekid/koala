import re
import sys
import threading
import inspect
from pyparsing import *
from expr import Expr, Formula, Fun, Var, Quantified, Binop, Unop, Pred, Ite, \
  TypeExpr, Fof, Cnf, Include, Tff
import time

# no speedup by memoization as claimed by pyparsing doc
#ParserElement.enablePackrat()
# needed for some large formulas
sys.setrecursionlimit(80000)
threading.stack_size(320 * 1024)

########################## define parser components ############################
# define parser actions

def mk_pred(name, first_arg, rargs):
  return Pred(name, [first_arg] + rargs)

def mk_fun(name, first_arg, rargs):
  return Fun(name, [first_arg] + rargs)

def mk_unop(toks):
  return Unop("~", toks[0][1])

def mk_binop(toks):
  def operand(subexpr):
    return mk_binop(subexpr) if isinstance(subexpr, list) else subexpr
  
  op = toks[1]
  return Binop(op, operand(toks[0]), operand(toks[2]))

def mk_quantified(toks):
  return Quantified(toks[0][0], toks[0][1:-1], toks[0][-1])

def mkPred(name, first_arg, rargs):
  return Pred(name, [first_arg] + rargs)


# define parser components
lpar = Literal("(").suppress()
rpar = Literal(")").suppress()
lbrack = Literal("[").suppress()
rbrack = Literal("]").suppress()
comma = Literal(",").suppress()
dot = Literal(".").suppress()
colon = Literal(":").suppress()
tick = Literal("'").suppress()
quote = Literal("\"").suppress()
sps = ZeroOrMore(White()).suppress()
sp = OneOrMore(White()).suppress()
name = (Word(srange("[a-zA-Z0-9_\-]")) | (tick + SkipTo(tick) + tick))
builtin_preds = (\
  Literal("$greatereq") | \
  Literal("$greater") | \
  Literal("$lesseq") | \
  Literal("$less") | \
  Literal("$is_int") | \
  Literal("$is_rat"))
builtin_funs = (\
  Literal("$product") | \
  Literal("$sum") | \
  Literal("$uminus") | \
  Literal("$difference") | \
  Literal("$ceiling") | \
  Literal("$floor") | \
  Literal("$truncate") | \
  Literal("$round") | \
  Literal("$quotient_f") | \
  Literal("$quotient_e") | \
  Literal("$quotient_t") | \
  Literal("$quotient") | \
  Literal("$remainder_f") | \
  Literal("$remainder_e") | \
  Literal("$remainder_t") | \
  Literal("$to_rat") | \
  Literal("$to_real") | \
  Literal("$to_int"))
pid = Word(alphas.lower(), srange("[a-zA-Z0-9_]")) | builtin_preds | \
  (tick + SkipTo(tick) + tick)
pcid = Word(alphas.lower(), srange("[a-zA-Z0-9_]"))
cid = Word(alphas.lower(), srange("[a-zA-Z0-9_]"))
vid = Word(alphas.upper(), srange("[a-zA-Z0-9_]"))
tvid = Word(alphas.upper(), srange("[a-zA-Z0-9_]"))
fid = Word(alphas.lower(), srange("[a-zA-Z0-9_]")) | builtin_funs | \
  (tick + SkipTo(tick) + tick)
# rough likelihood estimation of keywords
typ = Keyword("type")
kind = (\
  Keyword("axiom") |\
  Keyword("conjecture") |\
  Keyword("negated_conjecture") |\
  Keyword("hypothesis") |\
  typ |\
  Keyword("assumption") |\
  Keyword("corollary") |\
  Keyword("definition") |\
  Keyword("lemma") |\
  Keyword("plain") |\
  Keyword("theorem") |\
  Keyword("unknown"))
infix_pred = oneOf("= !=")
quantifier = oneOf("? !")
unop = Literal("~")
arrow_op = Literal("<=>") | Literal("<=") | Literal("=>") | Literal("<~>")
prop_const = Literal("$").suppress() + (\
  Literal("true").setParseAction(lambda toks: Pred(toks[0], [])) |\
  Literal("false").setParseAction(lambda toks: Pred(toks[0], [])))

type_name = Literal("$int") | Literal("$rat") | Literal("$real") | \
  Literal("$tType") | Word(alphanums+'_') | (tick + SkipTo(tick) + tick)

var = (vid + Optional(colon + sps + type_name.suppress())).\
  setParseAction(lambda toks: Var(toks[0]))

# terms
int_const = Word(srange("[1-9\-]"), nums) | Literal("0")
rat_const = Regex(r"[-]?\d+/\d+")
float_const = Regex(r"[-]?\d+\.\d+([Ee][+-]?\d+)?")
quot = Literal("\"").suppress()
str_const = ((tick + SkipTo(tick) + tick) | (quot + SkipTo(quot) + quot)).\
  setParseAction(lambda toks: "'" + toks[0] + "'")
term = Forward()
term << MatchFirst([\
  (fid + lpar + term + sps + ZeroOrMore(comma + sps + term) + sps + rpar).\
    setParseAction(lambda toks: mk_fun(toks[0], toks[1], toks[2:])),
  tvid.setParseAction(lambda toks: Var(toks[0])),
  (cid  | rat_const  | float_const | int_const | str_const).\
    setParseAction(lambda toks: Fun(toks[0], []))])
var_list = var + ZeroOrMore(comma + sps + var).\
  setParseAction(lambda toks: [t for t in toks])
ite = Literal("$ite").suppress()

'''
atom = MatchFirst([\
  (term + sps + infix_pred + sps + term).\
     setParseAction(lambda toks: Pred(toks[1], [toks[0], toks[2]])),
  (pid + Optional(sps + lpar + sps + term + sps + ZeroOrMore(comma + sps + term) + sps + rpar)).\
     setParseAction(lambda toks: mk_pred(toks[0], toks[1], toks[2:]) if len(toks) > 1 else Pred(toks[0], [])),
  prop_const])

quantified_vars = quantifier + sp + lbrack + var_list + rbrack + sp + colon
# according to TPTP, no precedence between binary operators
formula= infixNotation(atom + sps,
    [
    ("~" | quantified_vars, 1, opAssoc.RIGHT, \
      lambda toks: mk_unop(toks) if toks[0][0] == "~" else mk_quantified(toks)),
    (Literal("&") |  Literal("|") | arrow_op, 2, opAssoc.RIGHT, lambda toks: mk_binop(toks[0])),
    ])
'''
formula0 = Forward()
formula = Forward()
ite_formula = (ite + lpar + formula + comma + sps + formula + comma + sps + \
  formula + rpar).setParseAction(lambda toks: Ite(toks[0], toks[1], toks[2]))
formula0 << MatchFirst([\
  (unop + sp + formula0 + sps).\
     setParseAction(lambda toks: Unop(toks[0], toks[1])),
  (quantifier + sp + lbrack + var_list + rbrack + sp + colon + sps + formula).\
     setParseAction(lambda toks: Quantified(toks[0], toks[1:-1], toks[-1])),
  (lpar + sps + formula + sps + rpar).\
     setParseAction(lambda toks: toks[0]),
  (term + sps + infix_pred + sps + term).\
     setParseAction(lambda toks: Pred(toks[1], [toks[0], toks[2]])),
  (pid + sps + lpar + sps + term + sps + ZeroOrMore(comma + sps + term) + sps + rpar).\
     setParseAction(lambda toks: mkPred(toks[0], toks[1], toks[2:])),
  pcid.setParseAction(lambda toks: Pred(toks[0], [])),
  prop_const,
  ite])

binop = Literal("&") | Literal("|") | arrow_op
formula << \
  (formula0 + sps + Optional(binop + sp + formula + sps)).\
     setParseAction(lambda toks: Binop(toks[1], toks[0], toks[2]) if len(toks) > 1 else toks[0])

comment = (Literal("%") + SkipTo(LineEnd()) + LineEnd()).suppress()

fof = (Literal("fof") + lpar + sps + name + sps + comma + sps + kind + sps + comma + sps + formula + sps + rpar + dot).\
  setParseAction(lambda toks: Fof(toks[1], toks[2], toks[3]))

cnf = (Literal("cnf") + lpar + sps + name + sps + comma + sps + kind + sps + comma + sps + formula + sps + rpar + dot).\
  setParseAction(lambda toks: Cnf(toks[1], toks[2], toks[3]))

tff = ((Literal("tff") + lpar + sps + name + sps + comma + sps + kind + sps + comma + sps + formula + sps + rpar + dot).\
  setParseAction(lambda toks: Tff(toks[1], toks[2], toks[3])) | \
  (Literal("tff") + lpar + sps + name + sps + comma + sps + typ + sps + comma + sps + SkipTo(dot) + dot).\
  setParseAction(lambda toks: Tff(toks[1], toks[2], TypeExpr())))

file_name = Word(srange("[a-zA-Z0-9_/.+\x2D=]")).setParseAction(lambda toks: toks[0])
include = (Literal("include") + lpar + tick + file_name + tick + rpar + dot).\
  setParseAction(lambda toks: Include(toks[1]))

smt = OneOrMore(fof | cnf | tff | include | comment)

def test ():
  cnf.runTests('''
cnf(condensed_detachment,axiom, ( ~ is_a_theorem(implies(X,Y))| ~ is_a_theorem(X)| is_a_theorem(Y) )).

cnf(ic_JLukasiewicz_5,axiom,
    ( is_a_theorem(implies(implies(implies(P,Q),implies(R,S)),implies(implies(S,P),implies(T,implies(R,P))))) )).

cnf(prove_ic_1,negated_conjecture,
    ( ~ is_a_theorem(implies(a,a)) )).
  ''')

def preprocess(s):
  cleaned = ""
  for line in s.splitlines():
    if not line.startswith('%'):
        cleaned = cleaned + line
  return cleaned

def parse_problem(s, verbose):
  s = preprocess(s)
  fs = []
  splitter = "cnf" if "cnf(" in s else "fof"
  if "cnf(" in s or "fof(" in s:
    parts = re.split("^" + splitter, s)
    #print("probably " + str(len(parts)) + " clauses")
    for p in parts:
      p = p.strip()
      if p != "":
        m1 = re.match(r'^include\(', p)
        m2 = re.match(r'^type\(', p)
        if not m1 and not m2:
          p = splitter + p
        #print("part: " + p)
        r = smt.parseString(p)
        cnfs = []
        for c in r:
          cnfs.append(c)
        #print(cnfs[0].toString())
        fs = fs + cnfs
  else:
    fs = smt.parseString(s)
  cs = []
  for f in fs:
    if isinstance(f, Include):
      #print("... include " + f.file)
      axsfile = open(f.file, "r")
      axs = axsfile.read()
      cs = cs + parse_problem(axs, verbose)
    else:
      if verbose:
        print(f.formula)
        print(type(f.formula))
        print(f.toString())
      cs.append(f)
  return cs

if __name__ == "__main__":
  test()
