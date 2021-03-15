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
AddRecDefinition(append, (x, y), If(x == nil, y, cons(head(x), append(tail(x), y))))
AddRecDefinition(rev, x, If(x == nil, nil, append(rev(tail(x)), cons(head(x), nil))))

# axioms
AddAxiom(x, head(cons(hx, x)) == hx)
AddAxiom(x, tail(cons(hx, x)) == x)
AddAxiom(x, cons(hx, x) != nil)

# lemma
AddAxiom((x, y), rev(append(x, cons(y, nil))) == cons(y, rev(x)))

orig_goal = make_pfp_formula(Implies(lst(x), rev(rev(x)) == x))

v = Var('v', fgsort)
lemma_grammar_args = [v, nil]
lemma_grammar_terms = {v, nil}
name = 'rev-rev'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))
solveProblem(lemma_grammar_args, lemma_grammar_terms, orig_goal, name, grammar_string)
