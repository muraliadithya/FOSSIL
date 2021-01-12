import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

# declarations
x = Var('x', fgsort)
nil = Const('nil', fgsort)
k = Const('k', intsort)
key = Function('key', fgsort, intsort)
keys = Function('keys', fgsort, intsetsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
minr = Function('minr', fgsort, intsort)
maxr = Function('maxr', fgsort, intsort)
bst = RecFunction('bst', fgsort, boolsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
AddRecDefinition(bst, x, If(x == nil, True,
                            And(0 < key(x),
                                And(key(x) < 100,
                                    And(bst(lft(x)),
                                        And(bst(rght(x)),
                                            And(maxr(lft(x)) <= key(x),
                                                key(x) <= minr(rght(x)))))))))
AddRecDefinition(keys, x, If(x == nil, fgsetsort.lattice_bottom,
                             SetAdd(SetUnion(keys(lft(x)), keys(rght(x))), key(x))))
AddAxiom((), lft(nil) == nil)
AddAxiom((), rght(nil) == nil)


# vc
goal = Implies(bst(x), Implies(And(IsMember(k, keys(x)), k > key(x), x != nil), IsMember(k, keys(rght(x)))))

# check validity with natural proof solver and no hardcoded lemmas
np_solver = NPSolver()
solution = np_solver.solve(make_pfp_formula(goal))
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')


# hardcoded lemmas
lemma_params = (x,)
lemma_body = Implies(bst(x), Implies(And(IsMember(k, keys(x)), x != nil),
                                     And(minr(x) <= k, k <= maxr(x))))
lemmas = {(lemma_params, lemma_body)}

# check validity of lemmas
solution = np_solver.solve(make_pfp_formula(lemma_body))
if not solution.if_sat:
    print('lemma is valid')
else:
    print('lemma is invalid')

# check validity with natural proof solver
np_solver = NPSolver()
# If this mode is not specified the proof won't go through because the VC does
# not contain rght(x), which needs to be among the terms used for
# instantiation. Can also use manual instantiation mode, but that can't help
# with lemma synthesis.
np_solver.options.instantiation_mode = proveroptions.depth_one_untracked_lemma_instantiation
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal (with lemmas) is valid')
else:
    print('goal (with lemmas) is invalid')