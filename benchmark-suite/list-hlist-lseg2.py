import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, SetAdd, EmptySet, IsMember

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y = Vars('x y', fgsort)
nil = Const('nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
hlst = RecFunction('hlst', fgsort, fgsetsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(hlst, x, If(x == nil, fgsetsort.lattice_bottom, SetAdd(hlst(nxt(x)), x)))
AddRecDefinition(lseg, (x, y), If(x == y, True, lseg(nxt(x), y)))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
goal = Implies(lst(x),
               Implies(lst(y), SetIntersect(hlst(x), hlst(y)) == fgsetsort.lattice_bottom),
               Or(lseg(x,y), lseg(y,x)))

# hardcoded lemma
# TODO: fill in lemmas
lemma_params = (x,y)
lemma_body = True
lemmas = {(lemma_params, lemma_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
