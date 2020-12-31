import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.prover import NPSolver
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from lemsynth.lemsynth_engine import solveProblem

# Declarations
x = Var('x', fgsort)
y, nil = Consts('y nil', fgsort)
k = Const('k', intsort)
key = Function('key', fgsort, intsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
minr = Function('minr', fgsort, intsort)
maxr = Function('maxr', fgsort, intsort)
bst = RecFunction('bst', fgsort, boolsort)
leftmost = RecFunction('leftmost', fgsort, fgsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
AddRecDefinition(bst, x, If(x == nil, True,
                            And(0 < key(x),
                                And(key(x) < 100,
                                    And(bst(lft(x)),
                                        And(bst(rght(x)),
                                            And(maxr(lft(x)) <= key(x),
                                                key(x) <= minr(rght(x)))))))))
AddRecDefinition(leftmost, x, If(x == nil, x,
                                 If(lft(x) == nil, x, leftmost(lft(x)))))
AddAxiom((), lft(nil) == nil)
AddAxiom((), rght(nil) == nil)

# TODO: this does not compile. Somthing with the key(y) == minr(x) expression.
# I think it might have to do with x being a variable and y being a constant.
goal = Implies(bst(x), Implies(And(x != nil, y == leftmost(x)), key(y) == minr(x)))

lemmas = {((), True)}

# check validity with natural proof solver
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is valid')
else:
    print('goal is invalid')
