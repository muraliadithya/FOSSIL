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
i = Var('i', fgsort)

# ADT definition of lists
nil = Const('nil', fgsort)
cons = Function('cons', fgsort, fgsort, fgsort)

# ADT definition of nat
zero = Const('zero', fgsort)
succ = Function('succ', fgsort, fgsort)

# projections for cons
head = Function('head', fgsort, fgsort)
tail = Function('tail', fgsort, fgsort)

# projection for nat
pred = Function('pred', fgsort, fgsort)

# less than
le = Function('le', fgsort, fgsort, boolsort)

AddAxiom(x, le(zero, x))
AddAxiom(x, le(x, x))
AddAxiom((x, y), Implies(le(x, y), le(x, succ(y))))

# list
lst = RecFunction('lst', fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(tail(x))))

# rec defs
insort = RecFunction('insort', fgsort, fgsort, fgsort)
sortedl = RecFunction('sortedl', fgsort, boolsort)
sort = RecFunction('sort', fgsort, fgsort)
AddRecDefinition(insort, (i, x), If(x == nil, cons(i, nil),
                                    If(le(i, head(x)),
                                       cons(i, cons(head(x), tail(x))),
                                       cons(x, insort(i, tail(x))))))

AddRecDefinition(sort, x, If(x == nil, x, insort(head(x), tail(x))))

exit(0)




# axioms
AddAxiom(x, head(cons(hx, x)) == hx)
AddAxiom(x, tail(cons(hx, x)) == x)
AddAxiom(x, cons(hx, x) != nil)

# lemma
AddAxiom(x, rev(append(x, cons(hx, nil))) == cons(hx, rev(x)))

orig_goal = make_pfp_formula(Implies(lst(x), rev(rev(x)) == x))

v = Var('v', fgsort)
lemma_grammar_args = [v, nil]
lemma_grammar_terms = {v, nil}
name = 'rev-rev'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))
solveProblem(lemma_grammar_args, lemma_grammar_terms, orig_goal, name, grammar_string)
