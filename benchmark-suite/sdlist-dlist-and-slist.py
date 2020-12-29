import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.prover import NPSolver
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from lemsynth.lemsynth_engine import solveProblem

# Declarations
x = Var('x', fgsort)
nil, ret = Consts('nil ret', fgsort)
nxt = Function('nxt', fgsort, fgsort)
prv = Function('prv', fgsort, fgsort)
key = Function('key', fgsort, intsort)
dlst = RecFunction('dlst', fgsort, boolsort)
slst = RecFunction('slst', fgsort, boolsort)
sdlst = RecFunction('sdlst', fgsort, boolsort)
AddRecDefinition(dlst, x, If(x == nil, True,
                             If(nxt(x) == nil, True,
                                And(prv(nxt(x)) == x, dlst(nxt(x))))))
AddRecDefinition(slst, x, If(x == nil, True,
                             If(nxt(x) == nil, True,
                                And(key(x) <= key(nxt(x)), slst(nxt(x))))))
AddRecDefinition(sdlst, x, If(x == nil, True,
                              If(nxt(x) == nil, True,
                                 And(prv(nxt(x)) == x,
                                     And(key(x) <= key(nxt(x)), sdlst(nxt(x)))))))

AddAxiom((), nxt(nil) == nil)
AddAxiom((), prv(nil) == nil)

# Problem parameters
pgm = If(x == nil, ret == nil, ret == nxt(x))
goal = Implies(sdlst(x), Implies(pgm, And(dlst(ret), slst(ret))))

# hardcoded lemma
lemma_params = (x,)
lemma1_body = Implies(sdlst(x), dlst(x))
lemma2_body = Implies(sdlst(x), slst(x))
lemmas = {(lemma_params, lemma1_body), (lemma_params, lemma2_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
