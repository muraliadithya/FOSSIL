from z3 import *

# functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())

fcts = [next, prev]
fct_axioms = [next(-1) == -1, prev(-1) == -1]

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

recdefs = [ulist, dlist]

# VC
def pgm(x, ret):
    return IteBool(x == -1, ret == -1, ret == next(x))

def vc(x, ret):
    return Implies( dlist(x),
                    Implies(pgm(x, ret), list(ret)))

x, ret = Ints('x ret')
deref = [x]
const = [-1]

# TODO: enforce small false model?

# unfold each recursive definition on x
def unfold_recdefs(sol, x):
   for rec in recdefs:
      sol.add(rec(x))

# Get false model - model where VC is false
def getFalseModel():
   sol = Solver()

   # add axioms next(nil) = nil, prev(nil) = nil
   for ax in fct_axioms:
      sol.add(ax)

   # unfold constants
   for c in const:
      unfold_recdefs(sol, c)

   # unfold dereferenced variables
   for d in deref:
      unfold_recdefs(sol, d)

   # negate VC
   sol.add(Not(vc(x, ret)))

   # check satisfiability and print model in format CVC4 can handle 
   sol.check()
   m = sol.model()
   return m.sexpr()

# return product of two lists of lists
def product(ll1, ll2):
   return [ x + y for x in ll1 for y in ll2 ]

# generate all possible valuations of all functions at src
def getTrueModelsElem(elems, fcts, src):
   models_elt = [[]]
   for fct in fcts:
      fct_eval = [ [fct(src) == tgt] for tgt in elems ]
      models_elt = product(fct_eval, models_elt)
   return models_elt

# generate true models in the form of all posible evaluations of all functions
def getTrueModels(elems):
   models = [[]]
   for elem in elems:
      models_elt = getTrueModelsElem(elems, fcts, elem)
      models = product(models, models_elt)
   return models

print(getFalseModel())
print()
print(len(getTrueModels(range(3))))
