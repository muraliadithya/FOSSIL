import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, SetAdd, EmptySet, IsMember

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

# declarations
x, y = Vars('x y', fgsort)
nil = Const('nil', fgsort)
k = Const('k', intsort)
nxt = Function('nxt', fgsort, fgsort)
key = Function('key', fgsort, intsort)
lst = RecFunction('lst', fgsort, boolsort)
hlst = RecFunction('hlst', fgsort, fgsetsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(hlst, x, If(x == nil, fgsetsort.lattice_bottom, SetAdd(hlst(nxt(x)), x)))
AddAxiom((), nxt(nil) == nil)

# vc
goal = Implies(lst(x), Implies(key(x) != k, Implies(IsMember(y, hlst(x)), lst(y))))

# check validity with natural proof solver and no hardcoded lemmas
np_solver = NPSolver()
solution = np_solver.solve(make_pfp_formula(goal))
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')

# hardcoded lemma
lemma_params = (x,y)
lemma_body = Implies(lst(x), Implies(IsMember(y, hlst(x)), lst(y)))
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
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v1, v2, nil}

name = 'list-hlist-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
