import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If, Exists
from z3 import IsSubset, IsMember, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

x, y, tx = Vars('x y tx', fgsort)
hx = Var('hx', intsort)

# ADT definition of lists
nil = Const('nil', fgsort)
cons = Function('cons', intsort, fgsort, fgsort)

# projections for cons
head = Function('head', fgsort, intsort)
tail = Function('tail', fgsort, fgsort)

# list
lst = RecFunction('lst', fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(tail(x))))

# rec defs
append = RecFunction('append', fgsort, fgsort, fgsort)
rev = RecFunction('rev', fgsort, fgsort)
qreva = RecFunction('qreva', fgsort, fgsort, fgsort)
AddRecDefinition(append, (x, y), If(x == nil, y, cons(head(x), append(tail(x), y))))
AddRecDefinition(rev, x, If(x == nil, nil, append(rev(tail(x)), cons(head(x), nil))))
AddRecDefinition(qreva, (x, y), If(x == nil, y, qreva(tail(x), cons(head(x), y))))

# axioms

# lemma
AddAxiom((x, y), append(rev(x), y) == qreva(x, y))

orig_goal = Implies(lst(x), rev(x) == qreva(x, nil))

v = Var('v', fgsort)
lemma_grammar_args = [v, nil]
lemma_grammar_terms = {v, nil}
name = 'rev-rev'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

config_params = {}
# Uncomment this line for fixed_depth=1 mode
# config_params['goal_instantiation_mode'] = proveroptions.fixed_depth  # Default depth is 1
# Uncomment these two lines for manual instantiation mode
config_params['goal_instantiation_mode'] = proveroptions.manual_instantiation
config_params['goal_instantiation_terms'] = {x, head(x), tail(x), nil}
# If you comment out both things above, the goal takes too long to prove

solveProblem(lemma_grammar_args, lemma_grammar_terms, orig_goal, name, grammar_string)
