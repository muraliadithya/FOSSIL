from z3 import *
from lemma_synthesis import *

# functions
next = Function('next', IntSort(), IntSort())
next_p = Function('next_p', IntSort(), IntSort())

fcts = ['next', 'next_p']

# some general FOL macros
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

# axiom for nexty with ite
def next_p_fct_axiom(w):
    return IteBool(w == y, next_p(w) == z, next_p(w) == next(w))

# recursive definitions
list = Function('list', IntSort(), BoolSort())
lsegy = Function('lsegy', IntSort(), BoolSort())
list_p = Function('list_p', IntSort(), BoolSort())
lsegy_p = Function('lsegy_p', IntSort(), BoolSort())

fct_axioms = [next(-1) == -1, next_p(-1) == -1, lsegy(-1) == False, lsegy_p(-1) == False]

# axioms for next and prev of nil equals nil as python functions -
# for true model generation
def axiomNextNil(model):
    return model['next'][-1] == -1

def axiomPrevNil(model):
    return model['next_p'][-1] == -1

def axiomLsegNil(model):
    return model['lsegy'][-1] == False

vc_axioms  = [axiomNextNil, axiomPrevNil, axiomLsegNil]

# macros for unfolding recursive definitions
def ulist(x):
    return Iff( list(x), IteBool(x == -1, True, list(next(x))) )

def ulsegy(x):
    return Iff( lsegy(x), IteBool(x == y, True, lsegy(next(x))) )

def ulist_p(x):
    return Iff( list_p(x), IteBool(x == -1, True, list_p(next_p(x))) )

def ulsegy_p(x):
    return Iff( lsegy_p(x), IteBool(x == y, True, lsegy_p(next_p(x))) )

recdefs_macros = [ulist, ulsegy, ulist_p, ulsegy_p]

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

def list_p_fct(x, model):
    if x == -1:
        return True
    else:
        next_val = model['next_p'][x]
        return model['list_p'][next_val]

def lsegy_p_fct(x, model):
    if x == y:
        return True
    else:
        next_val = model['next_p'][x]
        return model['lsegy_p'][next_val]

recdefs = [list_fct, lsegy_fct, list_p_fct, lsegy_p_fct]

# string representation of recursive definition
# TODO: do this in a more systematic way
recdef_str = { list_fct : 'list', lsegy_fct : 'lsegy',
               list_p_fct : 'list_p', lsegy_p_fct : 'lsegy_p' }

# Z3Py representation of strings (for converting internal model to Z3Py model)
z3_str = { 'list' : list, 'lsegy' : lsegy, 'list_p' : list_p, 'lsegy_p' : lsegy_p,
           'next' : next, 'next_p' : next_p }

# VC
def pgm(x, y, z):
    return And( lsegy(x), next(y) == -1, list(z) )

def vc(x, y, z):
    return Implies( pgm(x, y, z), list_p(x) )

x, y, z = Ints('x y z')
deref = [x]
const = [-1, z, y]
elems = [-1, *range(2)]

for i in deref + const:
    fct_axioms += [ next_p_fct_axiom(i) ]

lemma = getSygusOutput(elems, fcts, vc_axioms, fct_axioms, recdefs_macros, recdefs,
                       recdef_str, deref, const, vc(x, y, z), z3_str,
                       'preamble_lseg-list.sy', 'grammar_lseg-list.sy', 'out_lseg-list.sy')

print(lemma)

# TODO: enforce small false model?
