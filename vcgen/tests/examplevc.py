import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet, SetUnion, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

#from lemsynth.lemsynth_engine import solveProblem

# declarations

nil = Const('nil', fgsort)
x_0 = Var('x_0', fgsort)
y_0 = Var('y_0', fgsort)

next_0 = Function('next_0', fgsort, fgsort)
next_1 = Function('next_1', fgsort, fgsort)
next_2 = Function('next_2', fgsort, fgsort)

list_0 = RecFunction('list_0', fgsort, boolsort)
list_1 = RecFunction('list_1', fgsort, boolsort)
list_2 = RecFunction('list_2', fgsort, boolsort)

x_1 = Var('x_1', fgsort)
y_1 = Var('y_1', fgsort)
var1 = Var('var1', fgsort)
AddAxiom((var1,), next_1(var1)== If(var1==x_0, next_0(y_1), next_0(var1)) )
AddAxiom((var1,), next_2(var1) == If(var1==y_1, x_0, next_1(var1)))
splist_0 = RecFunction('splist_0',fgsort,fgsetsort)
splist_2 = RecFunction('splist_2',fgsort,fgsetsort)

AddRecDefinition(splist_0, var1, If(var1 == nil, fgsetsort.lattice_bottom, SetAdd(splist_0(next_0(var1)),var1)))
AddRecDefinition(splist_2, var1, If(var1 == nil, fgsetsort.lattice_bottom, SetAdd(splist_2(next_2(var1)),var1)))
AddRecDefinition(list_0, var1 , If(var1 == nil, True, And(Not(IsSubset(SetAdd(fgsetsort.lattice_bottom,var1),splist_0(next_0(var1)))),list_0(next_0(var1)))))
AddRecDefinition(list_2, var1 , If(var1 == nil, True, And(Not(IsSubset(SetAdd(fgsetsort.lattice_bottom,var1),splist_2(next_2(var1)))),list_2(next_2(var1)))))


# vc
# pre = And(list_0(x_0),splist_0(x_0))
# post = And(list_2(x_1),splist_2(x_1))
pre = list_0(x_0)
post =list_2(x_1)
#Frame condition:

set1 = SetAdd(fgsetsort.lattice_bottom,x_0)
set2 = SetAdd(fgsetsort.lattice_bottom,y_1)
fp1 = And(list_0(next_0(y_1)), Not(Or(IsSubset(set1,splist_0(next_0(y_1))),IsSubset(set2,splist_0(next_0(y_1))))))
AddAxiom((y_1,), Implies(fp1,list_2(next_0(y_1))))


transform = And(Not(x_0 == nil), y_1 == next_0(x_0), Not(y_1 == nil),x_1==y_1 )
goal = Implies(And(pre,transform),post)

# list(y@2) AND (x@0 \not in Sp(list(y@2)) ) => list’(y@2) 
# check validity with natural proof solver and no hardcoded lemmagis
np_solver = NPSolver()
solution = np_solver.solve(goal)
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')
    #print(solution.model)
