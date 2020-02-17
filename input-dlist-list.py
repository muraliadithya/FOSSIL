from z3 import *

# functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())

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

# VC
def pgm(x, ret):
    return IteBool(x == -1, ret == -1, ret == next(x))

def vc(x, ret):
    return Implies( dlist(x),
                    Implies(pgm(x, ret), list(ret)))

# dereferenced terms in vc: { x }
# constants in vc: { -1 }

# TODO: enforce small false model?

# Get false model - model where VC is false
def getFalseModel():
   sol = Solver()

   # add axiom next(nil) = nil
   sol.add(next(-1) == -1)

   # unfold constants
   sol.add(ulist(-1))
   sol.add(dlist(-1))

   x, ret = Ints('x ret')

   # unfold dereferenced variables
   sol.add(ulist(x))
   sol.add(udlist(x))

   # negate VC
   sol.add(Not(vc(x, ret)))

   # check satisfiability and print model in format CVC4 can handle 
   sol.check()
   m = sol.model()
   return m.sexpr()

# TODO:
# - generate values 1 to n
# - next(1) = 1 or 2 or 3 or nil
# - loop through ulist on all elsts until fixpoint
def getTrueModels(n):
   sol = Solver()
   all_constraints = []
   for i in range(0,n):
      constraints = [next(i) == -1]
      for j in range(0, n):
         if i != j:
            constraints += [next(i) == j]
      all_constraints += [Or(constraints)]
   return all_constraints

print(getFalseModel())
print(getTrueModels(3))
