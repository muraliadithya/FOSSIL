import os

import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If, Exists
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.extensions.finitemodel import loadjsonstr

x, y, z = Vars('x y z', fgsort)

# ADT definition of nats
zero = Const('zero', fgsort)
succ = Function('succ', fgsort, fgsort)

# projection function - analogous to tail of list
pred = Function('pred', fgsort, fgsort)

# nat
nat = RecFunction('nat', fgsort, boolsort)
AddRecDefinition(nat, x, If(x == zero, True, nat(pred(x))))

# rec defs
plus = RecFunction('plus', fgsort, fgsort, fgsort)
AddRecDefinition(plus, (x, y), If(x == zero, y, succ(plus(pred(x), y))))

# axioms
AddAxiom(x, pred(succ(x)) == x)
AddAxiom(x, succ(x) != zero)
AddAxiom(x, Implies(x != zero, succ(pred(x)) == x))
# AddAxiom(x, Implies(nat(x), plus(x, zero) == x))
# AddAxiom((x,y), Implies(nat(x), Implies(nat(y), plus(x, succ(y)) == succ(plus(x, y)))))

orig_goal = plus(plus(x, y), z) == plus(x, plus(y, z))

base = plus(plus(zero, y), z) == plus(zero, plus(y, z))

ind_constructor = Implies( plus(plus(x, y), z) == plus(x, plus(y, z)),
                           plus(plus(succ(x), y), z) == plus(succ(x), plus(y, z)) )

ind_destructor = Implies( plus(plus(pred(x), y), z) == plus(pred(x), plus(y, z)),
                          plus(plus(x, y), z) == plus(x, plus(y, z)) )

goal_constructor = And(base, ind_constructor)
goal_destructor = And(base, ind_destructor)


np_solver = NPSolver()
solution = np_solver.solve(goal_constructor)
print('Associativity of addition: Using induction via constructors')
if not solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')
solution = np_solver.solve(goal_destructor)
print('Associativity of addition: Using induction via denstructors')
if not solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')
