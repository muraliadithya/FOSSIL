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

x, y, z = Vars('x y z', fgsort)

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
mult = RecFunction('mult', fgsort, fgsort, fgsort)
fac = RecFunction('fac', fgsort, fgsort)
qfac = RecFunction('qfac', fgsort, fgsort, fgsort)
AddRecDefinition(plus, (x, y), If(x == zero, y, succ(plus(pred(x), y))))
AddRecDefinition(mult, (x, y), If(x == zero, zero, plus(mult(pred(x), y), y)))
AddRecDefinition(fac, x, If(x == zero, succ(zero), mult(fac(pred(x)), x)))
AddRecDefinition(qfac, (x, y), If(x == zero, y, qfac(pred(x), mult(x, y))))

# axioms
AddAxiom(x, pred(succ(x)) == x)
AddAxiom(x, succ(x) != zero)
AddAxiom(x, Implies(x != zero, succ(pred(x)) == x))

AddAxiom((x, y), mult(x, y) == mult(y, x))
AddAxiom((x, y, z), mult(x, mult(y, z)) == mult(mult(x, y), z))

thm_to_prove = Implies(nat(x), Implies(nat(y), mult(fac(x), y) == qfac(x, y)))
goal = make_pfp_formula(thm_to_prove)
# print(goal)

v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, zero]
lemma_grammar_terms = {v1, v2, zero, succ(pred(v1)), succ(v1), succ(v2), mult(zero, v2), qfac(v2, v2), qfac(fac(v2), fac(v2)), qfac(qfac(v2, v2), mult(zero, v2)), fac(v2), mult(succ(zero), v2), succ(zero), qfac(fac(v2), qfac(zero, v2)), qfac(zero, v2), mult(v2, v2), qfac(v2, fac(v1)), fac(v1), qfac(v2, fac(pred(v1))), fac(pred(v1)), mult(fac(v2), v1), mult(fac(v2), pred(v1)), qfac(v2, v1), mult(qfac(zero, v2), qfac(v2, pred(v1))), mult(v2, zero), mult(qfac(zero, v2), qfac(v2, v1)), qfac(v2, pred(v1)), qfac(qfac(zero, zero), qfac(v2, pred(v1))), qfac(zero, zero), qfac(qfac(zero, zero), qfac(v2, v1)), mult(fac(v2), qfac(v2, v2)), mult(qfac(zero, v2), pred(v1)), mult(qfac(zero, v2), v1), mult(succ(v2), qfac(zero, v2)), mult(v2, pred(v1)), mult(v2, v1), mult(v2, fac(v2)), qfac(v2, zero), succ(qfac(v2, zero)), succ(mult(pred(v1), zero)), fac(zero), mult(v1, zero), succ(mult(v1, zero)), mult(pred(v1), zero), qfac(fac(pred(v1)), pred(v1)), qfac(fac(v1), v1), qfac(fac(zero), fac(v2)), qfac(v1, v2), qfac(pred(v1), v2), mult(v2, qfac(v1, v2)), mult(v2, qfac(pred(v1), v2)), qfac(fac(pred(v1)), qfac(v2, pred(v1))), qfac(fac(v1), qfac(v2, v1)), mult(fac(v2), mult(zero, v2)), qfac(fac(v2), succ(v2)), mult(fac(v2), v2), mult(fac(v1), succ(v2)), mult(fac(pred(v1)), succ(v2))}

name = 'fac'
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
