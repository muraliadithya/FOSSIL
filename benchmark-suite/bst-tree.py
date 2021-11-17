import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.prover import NPSolver
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

def notInChildren(x):
    return And(Not(IsMember(x, htree(lft(x)))), Not(IsMember(x, htree(rght(x)))))

# declarations
x = Var('x', fgsort)
nil, ret = Consts('nil ret', fgsort)
key = Function('key', fgsort, intsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
tree = RecFunction('tree', fgsort, boolsort)
minr = RecFunction('minr', fgsort, intsort)
maxr = RecFunction('maxr', fgsort, intsort)
bst = RecFunction('bst', fgsort, boolsort)
htree = RecFunction('htree', fgsort, fgsetsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
AddRecDefinition(tree, x, If(x == nil, True, And(tree(lft(x)), tree(rght(x)))))
AddRecDefinition(tree, x, If(x == nil, True,
                             And(And(And(Not(IsMember(x, htree(lft(x)))),
                                         Not(IsMember(x, htree(rght(x)))))),
                                 SetIntersect(htree(lft(x)), htree(rght(x)))
                                 == fgsetsort.lattice_bottom,
                                 And(tree(lft(x)), tree(rght(x))))))
AddRecDefinition(bst, x, If(x == nil, True,
                            And(0 < key(x),
                                And(key(x) < 100,
                                    And(bst(lft(x)),
                                        And(bst(rght(x)),
                                            And(maxr(lft(x)) <= key(x),
                                                And(key(x) <= minr(rght(x)),
                                                    And(notInChildren(x),
                                                        SetIntersect(htree(lft(x)), htree(rght(x)))
                                                        == fgsetsort.lattice_bottom)))))))))
AddRecDefinition(htree, x, If(x == nil, fgsetsort.lattice_bottom,
                              SetAdd(SetUnion(htree(lft(x)), htree(rght(x))), x)))
AddAxiom((), lft(nil) == nil)
AddAxiom((), rght(nil) == nil)

# vc
pgm = If(x == nil, ret == nil, ret == lft(x))
goal = Implies(bst(x), Implies(pgm, tree(ret)))

# check validity with natural proof solver and no hardcoded lemmas
np_solver = NPSolver()
solution = np_solver.solve(make_pfp_formula(goal))
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')

# hardcoded lemmas
lemma_params = (x,)
lemma_body = Implies(bst(x), tree(x))
lemmas = {(lemma_params, lemma_body)}

# check validity of lemmas
solution = np_solver.solve(make_pfp_formula(lemma_body))
if not solution.if_sat:
    print('lemma is valid')
else:
    print('lemma is invalid')

# check validity with natural proof solver and hardcoded lemmas
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal (with lemmas) is valid')
else:
    print('goal (with lemmas) is invalid')

# lemma synthesis
v = Var('v', fgsort)
lemma_grammar_args = [v, nil]
lemma_grammar_terms = {v, nil, lft(lft(v)), lft(rght(v)), rght(nil)}

name = 'bst-tree'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
