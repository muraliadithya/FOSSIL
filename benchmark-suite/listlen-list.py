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
l = Var('l', intsort)
nil, ret = Consts('nil ret', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
lstlen_bool = RecFunction('lstlen_bool', fgsort, boolsort)
lstlen_int = RecFunction('lstlen_int', fgsort, intsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lstlen_bool, x, If(x == nil, True, lstlen_bool(nxt(x))))
AddRecDefinition(lstlen_int, x, If(x == nil, 0, lstlen_int(nxt(x)) + 1))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
pgm = If(lstlen_int(x) == 1, ret == x, ret == nxt(x))
goal = Implies(lstlen_bool(x), Implies(pgm, lst(ret)))

# hardcoded lemma
lemma_params = (x,)
lemma_body = Implies(lstlen_bool(x), lst(x))
lemmas = {(lemma_params, lemma_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
