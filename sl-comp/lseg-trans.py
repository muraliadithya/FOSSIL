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
x, y, v, z = Vars('x y v z', fgsort)
nil = Const('nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
hlseg = RecFunction('hlseg', fgsort, fgsort, fgsort, boolsort)
AddRecDefinition(lseg, (x, y), If(x == nil, False,
                                  If(nxt(x) == y, True,
                                     lseg(nxt(x), y))))

# v \in hlseg(x, y)
AddRecDefinition(hlseg, (x, y, v), If(x == nil, False,
                                      If(v == x, True, hlseg(nxt(x), y, v))))

AddAxiom((), nxt(nil) == nil)

# Uncomment this line for fixed_depth=1 mode
# config_params['goal_instantiation_mode'] = proveroptions.fixed_depth  # Default depth is 1
# Uncomment these two lines for manual instantiation mode
# config_params['goal_instantiation_mode'] = proveroptions.manual_instantiation
# config_params['goal_instantiation_terms'] = {x, nxt(x)}

goal_heaplet_1a = Implies(hlseg(x, y, v), Implies(lseg(y, z), hlseg(x, z, v)))
goal_heaplet_1b = Implies(lseg(x, y), Implies(y != nil, Implies(lseg(y, z), hlseg(x, z, y))))
goal_heaplet_2 = Implies(hlseg(x, z, v), Implies(lseg(y, z), Or(v == y, hlseg(x, y, v))))

# lemma synthesis
v1, v2, v3, v4 = Vars('v1 v2 v3 v4', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v1, nil, nxt(nil), v2, nxt(v2), nxt(v1), nxt(nxt(v1)), nxt(nxt(nxt(v1)))}

name = 'lseg-nil-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal_heaplet_1a, name, grammar_string)
