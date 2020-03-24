from z3 import *
from lemma_synthesis import *

# functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())

fcts = ['next', 'prev']
fct_axioms = [next(-1) == -1, prev(-1) == -1]

# axioms for next and prev of nil equals nil as python functions -
# for true model generation
def axiomNextNil(model):
    return model['next'][-1] == -1

def axiomPrevNil(model):
    return model['prev'][-1] == -1

vc_axioms  = [axiomNextNil, axiomPrevNil]

# recursive definitions
list = Function('list', IntSort(), BoolSort())
dlist = Function('dlist', IntSort(), BoolSort())

# some general FOL macros
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

# macros for unfolding recursive definitions
def ulist(x):
    return Iff( list(x), IteBool(x == -1, True, list(next(x))))

def udlist(x):
    return Iff( dlist(x), IteBool( x == -1,
                                   True,
                                   IteBool( next(x) == -1,
                                            True,
                                            And(prev(next(x)) == x, dlist(next(x))) ))
   )

recdefs_macros = [ulist, dlist]

# for producing true models: functional versions of recursive definitions
def list_fct(x, model):
    if x == -1:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def dlist_fct(x, model):
    if x == -1:
        return True
    elif model['next'][x] == -1:
        return True
    else:
        next_val = model['next'][x]
        doubly_linked_cond = model['prev'][next_val] == x
        return doubly_linked_cond and model['dlist'][next_val]

recdefs = [list_fct, dlist_fct]

# string representation of recursive definition
# TODO: do this in a more systematic way
recdef_str = { list_fct : 'list', dlist_fct : 'dlist' }

# Z3Py representation of strings (for converting internal model to Z3Py model)
z3_str = { 'list' : list, 'dlist' : dlist, 'next' : next, 'prev' : prev }

# VC
def pgm(x, ret):
    return IteBool(x == -1, ret == -1, ret == next(x))

def vc(x, ret):
    return Implies( dlist(x),
                    Implies(pgm(x, ret), list(ret)))

x, ret = Ints('x ret')
deref = [x]
const = [-1]
elems = [-1, *range(2)]

getSygusOutput(elems, fcts, vc_axioms, fct_axioms, recdefs_macros, recdefs,
               recdef_str, deref, const, vc(x, ret), z3_str)

# TODO: enforce small false model?
