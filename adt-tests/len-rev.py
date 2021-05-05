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

x, y, tx, hx_nil, hx_tx, hxl_txl, txl = Vars('x y tx hx_nil hx_tx hxl_txl txl', fgsort)

hx, hxl = Consts('hx hxl', intsort)

# ADT definition of lists
nil = Const('nil', fgsort)
cons = Function('cons', intsort, fgsort, fgsort)

# projections for cons
head = Function('head', fgsort, intsort)
tail = Function('tail', fgsort, fgsort)

# rec defs
append = RecFunction('append', fgsort, fgsort, fgsort)
rev = RecFunction('rev', fgsort, fgsort)
AddRecDefinition(append, (x, y), If(x == nil, y, cons(head(x), append(tail(x), y))))
AddRecDefinition(rev, x, If(x == nil, nil, append(rev(tail(x)), cons(head(x), nil))))

length = RecFunction('length', fgsort, intsort)
AddRecDefinition(length, x, If(x == nil, 0, length(tail(x)) + 1))

# axioms
AddAxiom(tx, head(cons(hx, tx)) == hx)
AddAxiom(tx, tail(cons(hx, tx)) == tx)

# lemma as axiom: forall x, y. length(append(x, cons(y, nil))) == length(x) + 1
AddAxiom((x, hx_nil), Implies(And(head(hx_nil) == hx, tail(hx_nil) == nil),
                              length(append(x, hx_nil)) == length(x) + 1))

# goal: length(rev(x)) == length(x)
pfp_base = length(rev(nil)) == length(nil)
pfp_ind = Implies(And(hx_tx != nil,
                      And(length(rev(tx)) == length(tx),
                          And(head(hx_tx) == hx, tail(hx_tx) == tx))),
                  length(rev(hx_tx)) == length(hx_tx))
orig_goal = And(pfp_base, pfp_ind)

v = Var('v', fgsort)
lemma_grammar_args = [v, nil]
lemma_grammar_terms = {v, nil}
name = 'rev-rev'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))
solveProblem(lemma_grammar_args, lemma_grammar_terms, orig_goal, name, grammar_string)

# # check validity with natural proof solver and no hardcoded lemmas
# np_solver = NPSolver()
# np_solver.options.instantiation_mode = proveroptions.manual_instantiation
# np_solver.options.terms_to_instantiate = {hx_tx, nil, rev(tx), cons(hx, nil), hxl_txl}
# solution = np_solver.solve(orig_goal)
# if not solution.if_sat:
#     print('goal (no lemmas) is valid')
# else:
#     print('goal (no lemmas) is invalid')

# # hardcoded lemma
# lemma_params = (x, hx_nil)
# lemma_body = Implies(And(head(hx_nil) == hx, tail(hx_nil) == nil),
#                      length(append(x, hx_nil)) == length(x) + 1)
# lemmas = {(lemma_params, lemma_body)}

# # check validity of lemmas
# AddAxiom(tx, head(cons(hxl, tx)) == hxl)
# AddAxiom(tx, tail(cons(hxl, tx)) == tx)
# {rev(txl), append(txl, hx_nil), length(append(nil, hx_nil)), length(append(txl, hx_nil)), cons(hxl, txl), cons(hxl, nil), length(hxl_txl), length(txl)}
# lemma_body_base = Implies(And(head(hx_nil) == hx, tail(hx_nil) == nil),
#                           length(append(nil, hx_nil)) == length(nil) + 1)
# lemma_body_ind = Implies(Implies(And(head(hx_nil) == hx, tail(hx_nil) == nil),
#                                  length(append(txl, hx_nil)) == length(txl) + 1),
#                          Implies(And(head(hx_nil) == hx, tail(hx_nil) == nil),
#                                  Implies(And(head(hxl_txl) == hxl, tail(hxl_txl) == txl),
#                                          length(append(hxl_txl, hx_nil)) == length(hxl_txl) + 1)))
# lemma_body_goal = And(lemma_body_base, lemma_body_base)
# solution = np_solver.solve(lemma_body_goal)
# if not solution.if_sat:
#     print('lemma is valid')
# else:
#     print('lemma is invalid')

# check validity with natural proof solver and hardcoded lemmas
# solution = np_solver.solve(orig_goal, lemmas)
# if not solution.if_sat:
#     print('goal (with lemmas) is valid')
# else:
#     print('goal (with lemmas) is invalid')

# exit(0)
