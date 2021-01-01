import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.prover import NPSolver
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x, y, z = Vars('x y z', fgsort)
nil = Const('y nil', fgsort)
k = Const('k', intsort)
key = Function('key', fgsort, intsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
minr = Function('minr', fgsort, intsort)
maxr = Function('maxr', fgsort, intsort)
bst = RecFunction('bst', fgsort, boolsort)
hbst = RecFunction('hbst', fgsort, fgsetsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
AddRecDefinition(bst, x, If(x == nil, True,
                            And(0 < key(x),
                                And(key(x) < 100,
                                    And(bst(lft(x)),
                                        And(bst(rght(x)),
                                            And(maxr(lft(x)) <= key(x),
                                                key(x) <= minr(rght(x)))))))))
AddRecDefinition(hbst, x, If(x == nil, fgsetsort.lattice_bottom,
                             SetAdd(SetUnion(hbst(lft(x)), hbst(rght(x))), x)))
AddAxiom((), lft(nil) == nil)
AddAxiom((), rght(nil) == nil)

# Problem parameters
goal = Implies(bst(x), Implies(And(x != nil,
                                   And(IsMember(y, hbst(lft(x))),
                                       IsMember(z, hbst(rght(x))))),
                               key(y) <= key(z)))

# hardcoded lemmas
lemma1_params = (x,y)
lemma1_body = Implies(bst(x), Implies(IsMember(y, hbst(x)), key(y) <= maxr(x)))
lemma2_params = (x,y)
lemma2_body = Implies(bst(x), Implies(IsMember(y, hbst(x)), minr(x) <= key(y)))
lemmas = {(lemma1_params, lemma1_body), (lemma2_params, lemma2_body)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
