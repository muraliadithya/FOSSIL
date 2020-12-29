import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.prover import NPSolver
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y = Vars('x y', fgsort)
nil, ret = Consts('nil ret', fgsort)
nxt = Function('nxt', fgsort, fgsort)
key = Function('key', fgsort, intsort)
slst = RecFunction('slst', fgsort, boolsort)
slseg = RecFunction('slseg', fgsort, fgsort, boolsort)
AddRecDefinition(slst, x, If(x == nil, True,
                             If(nxt(x) == nil, True,
                                And(key(x) <= key(nxt(x)), slst(nxt(x))))))
AddRecDefinition(slseg, (x, y), If(x == y, True,
                                   And(key(x) <= key(nxt(x)), slseg(nxt(x), y))))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
pgm = If(x == nil, ret == nil, ret == nxt(x))
goal = Implies(slseg(x, y), Implies(y == nil, Implies(pgm, slst(ret))))

# hardcoded lemma
lemma_params = (x,y)
lemma_body = Implies(slseg(x, y), slst(x) == slst(y))
lemmas = {(lemma_params, lemma_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
