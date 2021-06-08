import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem

# declarations
x, y, y_rec, z = Vars('x y y_rec z', fgsort)
nil = Const('nil', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
hlseg = RecFunction('hlseg', fgsort, fgsort, fgsetsort)
AddRecDefinition(lseg, (x, y), If(x == nil, False,
                                  If(nxt(x) == y, True,
                                     And(lseg(nxt(x), y),
                                         # And(hlseg(x, y) == SetAdd(hlseg(nxt(x), y), x),
                                         SetIntersect(hlseg(nxt(x), y), SetAdd(fgsetsort.lattice_bottom, x)) == fgsetsort.lattice_bottom))))
lhs_rec = RecFunction('lhs_rec', fgsort, fgsort, fgsort, fgsort, boolsort)
AddRecDefinition(lhs_rec, (x, y_rec, y, z), 
                 And(If(x == nil, False,
                        If(nxt(x) == y_rec, True,
                           And(lhs_rec(nxt(x), y_rec, y, z),
                               # And(hlseg(x, y) == SetAdd(hlseg(nxt(x), y), x),
                               SetIntersect(hlseg(nxt(x), y_rec), SetAdd(fgsetsort.lattice_bottom, x)) == fgsetsort.lattice_bottom))),
                     And(y == y_rec,
                         And(nxt(y) == z, 
                             SetIntersect(hlseg(x, y), SetAdd(fgsetsort.lattice_bottom, y)) == fgsetsort.lattice_bottom))))


AddRecDefinition(hlseg, (x, y), If(x == y, fgsetsort.lattice_bottom,
                                   If(nxt(x) == y, SetAdd(fgsetsort.lattice_bottom, x),
                                      SetAdd(hlseg(nxt(x), y), x))))

AddAxiom((), nxt(nil) == nil)
AddAxiom((), z != nil)
AddAxiom((), z != x)

# heap_equality = SetAdd(hlseg(x, y), y) == hlseg(x, z)
# heap_intersection = SetIntersect(hlseg(x, y), SetAdd(fgsetsort.lattice_bottom, y)) == fgsetsort.lattice_bottom
# heap_conds = And(heap_equality, heap_intersection)

# lhs_rec = RecFunction('lhs_rec', fgsort, fgsort, fgsort, boolsort)
# AddRecDefinition(lhs_rec, (x, y, z), And(lseg(x, y), And(nxt(y) == z, heap_conds)))

goal = Implies(lhs_rec(x, y, y, z), lseg(x, z))


# lemma synthesis
v1, v2, v3, v4 = Vars('v1 v2 v3 v4', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v1, nil, nxt(nil), v2, nxt(v2), nxt(v1), nxt(nxt(v1)), nxt(nxt(nxt(v1)))}

name = 'lseg-nil-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string)
