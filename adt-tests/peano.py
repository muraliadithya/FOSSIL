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
# AddAxiom(x, Implies(nat(x), plus(x, zero) == x))
# AddAxiom((x,y), Implies(nat(x), Implies(nat(y), plus(x, succ(y)) == succ(plus(x, y)))))

thm_to_prove = Implies(nat(x), Implies(nat(y), plus(x, y) == plus(y, x)))
goal = make_pfp_formula(thm_to_prove)
# print(goal)

v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, zero]
lemma_grammar_terms = {v1, v2, zero, plus(v1, v2), succ(v2), plus(v1, succ(v2)), succ(plus(v1, v2)), plus(v1, zero), plus(v2, v1), succ(v1), plus(v2, succ(v1)), succ(plus(v2, v1)), plus(v2, zero), plus(zero, zero), succ(zero), plus(plus(zero, zero), succ(zero)), plus(zero, succ(v2)), plus(v1, plus(zero, zero)), plus(pred(v1), plus(zero, zero)), plus(zero, plus(v2, zero)), plus(pred(v1), plus(zero, v2)), plus(v1, plus(zero, v2)), plus(zero, v2), succ(plus(zero, zero)), plus(v2, v2), plus(plus(v2, v2), succ(v2)), plus(plus(v1, zero), v2), plus(pred(v1), pred(v1)), plus(plus(pred(v1), zero), v2), plus(v1, v1), plus(succ(zero), succ(zero))}

name = 'peano'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

config_params = {}
# Uncomment this line for fixed_depth=1 mode
# config_params['goal_instantiation_mode'] = proveroptions.fixed_depth  # Default depth is 1
# Uncomment these two lines for manual instantiation mode
config_params['goal_instantiation_mode'] = proveroptions.manual_instantiation
config_params['goal_instantiation_terms'] = {x, y, pred(x)}
# If you comment out both things above, the goal takes too long to prove
solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string, config_params)

exit(0)

# proving without lemmas
orig_np_solver = NPSolver()
orig_solution = orig_np_solver.solve(goal)
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
final_np_solver.options.instantiation_mode = proveroptions.manual_instantiation
final_np_solver.options.terms_to_instantiate = {x, y, succ(x), succ(y), pred(x), pred(y)}
final_solution = final_np_solver.solve(goal, lemmas)
print('Original goal with lemmas assumed:')
if not final_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')
