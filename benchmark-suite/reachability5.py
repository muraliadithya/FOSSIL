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
c, s, nil = Consts('c s nil', fgsort)
v1 = Function('v1', fgsort, fgsort)
v2 = Function('v2', fgsort, fgsort)
p = Function('p', fgsort, fgsort)
n = Function('n', fgsort, fgsort)

reach = RecFunction('reach', fgsort, boolsort)

# precondition
AddAxiom((), v1(s) == n(v2(s)))

cond = v1(p(x)) != nil
assign1 = v1(x) == n(v1(p(x)))
assign2 = If( v2(p(x)) != c,
              v2(x) == n(v2(p(x))),
              v2(x) == v2(p(x)) )
assign = And(assign1, assign2)
AddRecDefinition(reach, x, If(x == s, True, And(reach(p(x)), And(cond, assign))))

# problem parameters
lhs = v1(x) == nil
rhs = Or(n(v2(x)) == nil, v2(x) == c)
goal = Implies(reach(x), Implies(lhs, rhs))

# hardcoded lemma
lemma_params = (x,)
lemma_body = Implies(reach(x), Or(v1(x) == n(v2(x)), v2(x) == c))
lemmas = {(lemma_params, lemma_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
