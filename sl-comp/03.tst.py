import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

# declarations
x, y, z = Vars('x y z', fgsort)
nil = Const('nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
hlseg = RecFunction('hlseg', fgsort, fgsort, fgsetsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lseg, (x, y), If(x == nil, False,
                                  If(nxt(x) == y, True,
                                     And(lseg(nxt(x), y)))))
AddRecDefinition(hlseg, (x, y), If(x == nil, fgsetsort.lattice_bottom,
                                   If(nxt(x) == y, SetAdd(fgsetsort.lattice_bottom, x),
                                      SetAdd(hlseg(nxt(x), y), x))))
AddAxiom((), nxt(nil) == nil)

heap_equality = SetAdd(hlseg(x, y), y) == hlseg(x, z)
heap_intersection = SetIntersect(hlseg(x, y), SetAdd(fgsetsort.lattice_bottom, y)) == fgsetsort.lattice_bottom
heap_conds = And(heap_equality, heap_intersection)

lhs_rec = RecFunction('lhs_rec', fgsort, fgsort, fgsort, boolsort)
AddRecDefinition(lhs_rec, (x, y, z), And(lseg(x, y), And(nxt(y) == z, heap_conds)))

goal = Implies(lhs_rec(x, y, z), lseg(x, z))

# check validity with natural proof solver and no hardcoded lemmas
np_solver = NPSolver()
solution = np_solver.solve(make_pfp_formula(goal))
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')

# hardcoded lemma
lemma_params = (x,y)
lemma_body = Implies(lseg(x, y), lst(x) == lst(y))
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
lemma_grammar_terms = {v1, nil, nxt(nil), v2, nxt(v2), nxt(v1), nxt(nxt(v1)), nxt(nxt(nxt(v1)))}

name = 'lseg-nil-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
