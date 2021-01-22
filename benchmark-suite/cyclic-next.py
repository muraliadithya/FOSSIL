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
nil = Const('nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
cyclic = RecFunction('cyclic', fgsort, boolsort)
AddRecDefinition(lseg, (x, y) , If(x == y, True,
                                   If(x == nil, False,
                                      lseg(nxt(x), y))))
AddRecDefinition(cyclic, x, And(x != nil, lseg(nxt(x), x)))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
goal = Implies(cyclic(x), cyclic(nxt(x)))

# hardcoded lemmas
# TODO: lemmas not sufficient
lemma_params = (x,y)
lemma1_body = Implies(lseg(x,y), Implies(y != nil, x != nil))
lemma2_body = Implies(lseg(x,y), Implies(y != nil, lseg(x, nxt(y))))
lemmas = {(lemma_params, lemma1_body), (lemma_params, lemma2_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
    
exit(1)
