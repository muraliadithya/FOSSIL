import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y = Vars('x y', fgsort)
nil, ret = Consts('nil ret', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lseg, (x, y) , If(x == y, True, lseg(nxt(x), y)))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
pgm = If(x == nil, ret == nil, ret == nxt(x))
goal = Implies(lseg(x, y), Implies(y == nil, Implies(pgm, lst(ret))))

# hardcoded lemma
lemma_params = (x,y)
lemma_body = Implies(lseg(x, y), lst(x) == lst(y))
lemmas = {(lemma_params, lemma_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
