import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

import naturalproofs.AnnotatedContext as AnnCtx
import naturalproofs.proveroptions
from naturalproofs.uct import intsort, intsetsort, boolsort
from naturalproofs.uct import min_intsort, override_fgsort
# Redeclare the foreground sort
List = z3.Datatype('List')
List.declare('nil')
List.declare('cons', ('head', intsort.z3sort), ('tail', List))
List = List.create()
nil = List.nil
cons = List.cons
head = List.accessor(1, 0)
tail = List.accessor(1, 1)
new_annctx = override_fgsort(List)
AnnCtx.default_annctx = new_annctx
from naturalproofs.uct import fgsort, fgsetsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from naturalproofs.pfp import make_induction_obligation
from naturalproofs.prover import NPSolver

# declarations
x = Var('x', fgsort)

is_sorted = RecFunction('isSorted', fgsort, boolsort)
AddRecDefinition(is_sorted, x, If(x == nil, True,
                                  If(tail(x) == nil, True,
                                     And(head(x) <= head(tail(x)), is_sorted(tail(x))))))
keys = RecFunction('keys', fgsort, intsetsort)
AddRecDefinition(keys, x, If(x == nil, intsetsort.lattice_bottom, SetAdd(keys(tail(x)), head(x))))
# Can't use definitions with mixed fg and bg sorts, so we artificially make the integer argument
# into a one-element list and use head(k) instead of k.
k = Var('k', fgsort)
# ADT list membership
# mem = RecFunction('mem', intsort, List, boolsort)
mem = RecFunction('mem', fgsort, fgsort, boolsort)
AddRecDefinition(mem, (k, x), If(x == nil, False,
                                 If(head(k) == head(x), True,
                                    If(head(k) < head(x), False, mem(k, tail(x))))))


# theorem
# make the fact that k is a one-element list part of the assumptions
goal = Implies(And(is_sorted(x), tail(k) == nil), mem(k, x) == IsMember(head(k), keys(x)))
ind_goal = make_induction_obligation(goal, x)

# check validity with natural proof solver and no lemmas
np_solver = NPSolver()
solution = np_solver.solve(goal)
if not solution.if_sat:
    print('goal is fo provable (no lemmas)')
else:
    print('goal is not fo provable (no lemmas)')

# Try to prove by induction
np_solver = NPSolver()
solution = np_solver.solve(ind_goal)
if not solution.if_sat:
    print('goal is provable by induction (no lemmas)')
else:
    print('goal is not provable by induction (no lemmas)')

# hardcoded lemma
lemma_params = (x, k)
lemma_body = Implies(And(is_sorted(x), tail(k) == nil), Implies(head(k) < head(x), Not(IsMember(head(k), keys(x)))))
lemmas = {(lemma_params, lemma_body)}

# check validity of lemmas
solution = np_solver.solve(make_induction_obligation(lemma_body, x))
print(f'Lemma(s) suggested: {lemma_body}')
if not solution.if_sat:
    print('lemma is valid')
else:
    print('lemma is invalid')

# do the above checks again with lemmas
np_solver = NPSolver()
solution = np_solver.solve(goal, lemmas)
if not solution.if_sat:
    print('goal is fo provable (with lemmas)')
else:
    print('goal is not fo provable (with lemmas)')

# Try to prove by induction
np_solver = NPSolver()
solution = np_solver.solve(ind_goal, lemmas)
if not solution.if_sat:
    print('goal is provable by induction (with lemmas)')
else:
    print('goal is not provable by induction (with lemmas)')
