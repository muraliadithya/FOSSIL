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
      print(rec)
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

def getTrueFctConstraints(n, fct):
   all_constraints = []
   for i in range(0, n):
      constraints = [fct(i) == -1]
      for j in range(0, n):
         constraints += [fct(i) == j]
      all_constraints += [constraints]
   return all_constraints

# TODO:
# - generate values 1 to n
# - next(1) = 1 or 2 or 3 or nil
# - loop through ulist on all elsts until fixpoint
def getTrueModels(n):
   all_constraints = {}
   for i in range(0, n):
      for fct in fcts:
         for j in range(0, n):
            print(fct(i) == j)
   return None

def oneStep(ld, l):
   out = []
   for d in ld:
      for p in l:
         d[p[0]] = p[1]
         out += [d]
   return out

def cartesianProduct():
   ld = [{}]
   for 

# print(getFalseModel())
# print()
# print(getTrueModels(5))

print(oneStep([ {0:0}, {0:1} ], [{1:0}, {1:1}]))
