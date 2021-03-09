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
double = RecFunction('double', fgsort, fgsort)
AddRecDefinition(plus, (x, y), If(x == zero, y, succ(plus(pred(x), y))))
AddRecDefinition(double, x, If(x == zero, zero, succ(succ(double(pred(x))))))

# axioms
AddAxiom(x, pred(succ(x)) == x)
AddAxiom(x, succ(x) != zero)
AddAxiom(x, Implies(x != zero, succ(pred(x)) == x))
# AddAxiom(x, succ(succ(plus(x, x))) == plus(succ(x), succ(x)))

# AddAxiom(x, Implies(nat(x), double(zero) == plus(zero, zero)))
# AddAxiom(x, Implies(nat(x), double(succ(x)) == plus(succ(x), succ(x))))

orig_goal = make_pfp_formula(Implies(nat(x), double(x) == plus(x, x)))

v = Var('v', fgsort)
lemma_grammar_args = [v, zero]
lemma_grammar_terms = {v, zero, plus(succ(pred(v)), succ(pred(v))), plus(succ(v), succ(v)), succ(pred(v)), succ(v), succ(succ(pred(v))), succ(succ(v)), plus(v, v), plus(pred(v), pred(v)), succ(succ(plus(pred(v), pred(v)))), succ(succ(plus(v, v))), succ(plus(pred(v), pred(v))), succ(plus(v, v))}
name = 'double'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))
solveProblem(lemma_grammar_args, lemma_grammar_terms, orig_goal, name, grammar_string)

exit(0)

# adt pfp of goal
orig_np_solver = NPSolver()
orig_solution = orig_np_solver.solve(orig_goal)
print('double: no lemma')
if not orig_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')

exit(0)

# base case lemma: double(0) = 0 + 0
base_case_params = (x,)
base_case = Implies(nat(x), double(zero) == plus(zero, zero))
base_pfp_goal = make_pfp_formula(base_case)
base_np_solver = NPSolver()
base_solution = base_np_solver.solve(base_case)
print('Lemma for base case: double(0) = 0 + 0')
if not base_solution.if_sat:
    print(' -- lemma is valid')
else:
    print(' -- lemma is invalid')

# inductive case lemma: double(x) = x + x -> double(S x) = S x + S x
ind_case_params = (x,)
ind_case = Implies(nat(x), Implies(double(x) == plus(x, x), double(succ(x)) == plus(succ(x), succ(x))))
ind_pfp_goal = make_pfp_formula(ind_case)
ind_np_solver = NPSolver()
ind_solution = ind_np_solver.solve(ind_case)
print('Lemma for inductive case: double(x) = x + x -> double(S x) = S x + S x')
if not ind_solution.if_sat:
    print(' -- lemma is valid')
else:
    print(' -- lemma is invalid')

# adding lemmas to solver
lemmas = {(base_case_params, base_case), (ind_case_params, ind_case)}
final_np_solver = NPSolver()
final_solution = final_np_solver.solve(orig_pfp_goal, lemmas)
print('Original goal with lemmas assumed:')
if not final_solution.if_sat:
    print(' -- goal is valid')
else:
    print(' -- goal is invalid')
