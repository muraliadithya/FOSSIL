import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

# declarations
x, y, z, x_p, y_p = Vars('x y z x_p y_p', fgsort)
nil = Const('nil', fgsort)
k = Const('k', intsort)
nxt = Function('nxt', fgsort, fgsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
lseg_p = RecFunction('lseg_p', fgsort, fgsort, boolsort)
key = Function('key', fgsort, intsort)
AddRecDefinition(lseg, (x, y) , If(x == y, True, lseg(nxt(x), y)))
AddRecDefinition(lseg_p, (x_p, y_p) , If(x_p == y_p, True, lseg_p(If(x_p == y, z, nxt(x_p)), y_p)))
AddAxiom((), nxt(nil) == nil)

# vc
goal = Implies(lseg(x, y), Implies(key(x) != k, lseg_p(x, z)))

# check validity with natural proof solver and no hardcoded lemmas
np_solver = NPSolver()
solution = np_solver.solve(make_pfp_formula(goal))
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')

# hardcoded lemma
lemma_params = (x,y,z)
lemma_body = Implies(lseg(x, y), lseg_p(x, z))
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
v1, v2, v3 = Vars('v1 v2 v3', fgsort)
lemma_grammar_args = [v1, v2, v3]
lemma_grammar_terms = {v1, v2, v3, nxt(v2), nxt(nxt(v1))}

name = 'lseg-next-dynamic'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
