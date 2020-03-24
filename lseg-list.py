from z3 import *
from lemma_synthesis import *

# functions
next = Function('next', IntSort(), IntSort())
nexty = Function('nexty', IntSort(), IntSort())

fcts = ['next', 'nexty']

# axiom for nexty with ite

# recursive definitions
list = Function('list', IntSort(), BoolSort())
lsegy = Function('lsegy', IntSort(), BoolSort())
listy = Function('listy', IntSort(), BoolSort())

fct_axioms = [next(-1) == -1, nexty(-1) == -1, lsegy(-1) == False]

# axioms for next and prev of nil equals nil as python functions -
# for true model generation
def axiomNextNil(model):
    return model['next'][-1] == -1

def axiomPrevNil(model):
    return model['nexty'][-1] == -1

def axiomLsegNil(model):
    return model['lsegy'][-1] == False

vc_axioms  = [axiomNextNil, axiomPrevNil, axiomLsegNil]

# some general FOL macros
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

# macros for unfolding recursive definitions
def ulist(x):
    return Iff( list(x), IteBool(x == -1, True, list(next(x))) )

def ulsegy(x):
    return Iff( lsegy(x), IteBool(x == y, True, lsegy(nexty(x))) )

def ulisty(x):
    return Iff( listy(x), IteBool(x == -1, True, listy(nexty(x))) )

recdefs_macros = [ulist, ulsegy, ulisty]

# for producing true models: functional versions of recursive definitions
def list_fct(x, model):
    if x == -1:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def lsegy_fct(x, model):
    if x == y:
        return True
    else:
        next_val = model['next'][x]
        return model['lsegy'][next_val]

def listy_fct(x, model):
    if x == -1:
        return True
    else:
        next_val = model['nexty'][x]
        return model['listy'][next_val]

recdefs = [list_fct, lsegy_fct, listy_fct]

# string representation of recursive definition
# TODO: do this in a more systematic way
recdef_str = { list_fct : 'list', lsegy_fct : 'lsegy', listy_fct : 'listy' }

# Z3Py representation of strings (for converting internal model to Z3Py model)
z3_str = { 'list' : list, 'lsegy' : lsegy, 'listy' : listy, 'next' : next, 'nexty' : nexty }

# VC
def pgm(x, y):
    return And( lsegy(x), next(y) == -1 )

def vc(x, y):
    return Implies( pgm(x, y), listy(x) )

x, y, z = Ints('x y z')
deref = [x]
const = [-1]
elems = [-1, *range(2)]

getSygusOutput(elems, fcts, vc_axioms, fct_axioms, recdefs_macros, recdefs,
               recdef_str, deref, const, vc(x, y), z3_str,
               'preamble_lseg-list.sy', 'grammar_lseg-list.sy', 'out_lseg-list.sy')

# TODO: enforce small false model?
