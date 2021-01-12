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

x, y = Vars('x y', fgsort)

# ADT definition of nats
zero = Const('zero', fgsort)
succ = Function('succ', fgsort, fgsort)

# projection function - analogous to tail of list
pred = Function('pred', fgsort, fgsort)

# nat
nat = RecFunction('nat', fgsort, boolsort)
AddRecDefinition(nat, x, If(x == zero, True, nat(pred(x))))

# rec defs
plus = RecFunction('plus', fgsort, fgsort, fgsort)
AddRecDefinition(plus, (x, y), If(x == zero, y, succ(plus(pred(x), y))))

# axioms
AddAxiom(x, pred(succ(x)) == x)
AddAxiom(x, succ(x) != zero)
AddAxiom(x, Implies(x != zero, succ(pred(x)) == x))

orig_goal = Implies(nat(x), Implies(nat(y), plus(x, y) == plus(y, x)))

# v1, v2 = Vars('v1 v2', fgsort)
# lemma_grammar_args = [v1, v2, zero]
# lemma_grammar_terms = {v1, v2, zero}

# name = 'peano'
# grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

# solveProblem(lemma_grammar_args, lemma_grammar_terms, orig_goal, name, grammar_string)

# exit(0)

# adt pfp of goal
orig_pfp_goal = make_pfp_formula(orig_goal)
orig_np_solver = NPSolver()
orig_solution = orig_np_solver.solve(orig_pfp_goal)
print('Commutativity of addition: no lemma')
if not orig_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')

# adt pfp of base case lemma: x + zero = x
base_lemma_params = (x,)
base_lemma = Implies(nat(x), plus(x, zero) == x)
base_pfp_goal = make_pfp_formula(base_lemma)
base_np_solver = NPSolver()
base_solution = base_np_solver.solve(base_pfp_goal)
print('Lemma for inductive case: x + zero = x')
if not base_solution.if_sat:
    print(' -- lemma is valid')
else:
    print(' -- lemma is invalid')

# adt pfp of inductive case lemma: x + S y = S (x + y)
ind_lemma_params = (x, y)
ind_lemma = Implies(nat(x), Implies(nat(y), plus(x, succ(y)) == succ(plus(x, y))))
ind_pfp_goal = make_pfp_formula(ind_lemma)
ind_np_solver = NPSolver()
ind_solution = ind_np_solver.solve(ind_pfp_goal)
print('Lemma for inductive case: x + S y = S (x + y)')
if not ind_solution.if_sat:
    print(' -- lemma is valid')
else:
    print(' -- lemma is invalid')

# adding lemmas to solver
lemmas = {(base_lemma_params, base_lemma), (ind_lemma_params, ind_lemma)}
final_np_solver = NPSolver()
final_solution = final_np_solver.solve(orig_pfp_goal, lemmas)
print('Original goal with lemmas assumed:')
if not final_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')
