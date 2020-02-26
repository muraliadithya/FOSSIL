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

def add_constraints(sol, x):
   sol.add(ulist(x))
   sol.add(udlist(x))
 
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

# Get false model - model where VC is false
def getFalseModel():
   sol = Solver()

   # add axioms next(nil) = nil, prev(nil) = nil
   for ax in fct_axioms:
      sol.add(ax)

   # unfold constants
   for c in const:
      add_constraints(sol, c)

   # unfold dereferenced variables
   for d in deref:
      add_constraints(sol, d)

   # negate VC
   sol.add(Not(vc(x, ret)))

   # check satisfiability and print model in format CVC4 can handle 
   sol.check()
   m = sol.model()
   return m.sexpr()

def getTrueFctConstraints(n, fct):
   all_constraints = []
   for i in range(0,n):
      constraints = [fct(i) == -1]
      for j in range(0, n):
         constraints += [fct(i) == j]
      all_constraints += [Or(constraints)]
   return all_constraints

# TODO:
# - generate values 1 to n
# - next(1) = 1 or 2 or 3 or nil
# - loop through ulist on all elsts until fixpoint
def getTrueModels(n):
   for fct in fcts:
      print(getTrueFctConstraints(n, fct))

print(getFalseModel())
print()
print(getTrueModels(5))
