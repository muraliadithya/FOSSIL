import os

import importlib_resources

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions

from lemsynth.lemsynth_engine import solveProblem

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.extensions.finitemodel import loadjsonstr

# Declarations
x, y = Vars('x y', fgsort)
nil, ret = Consts('nil ret', fgsort)
nxt = Function('nxt', fgsort, fgsort)
lst = RecFunction('lst', fgsort, boolsort)
lseg = RecFunction('lseg', fgsort, fgsort, boolsort)
AddRecDefinition(lst, x, If(x == nil, True, lst(nxt(x))))
AddRecDefinition(lseg, (x, y), If(x == y, True, lseg(nxt(x), y)))
AddAxiom((), nxt(nil) == nil)

# Problem parameters
pgm = If(x == nil, ret == nil, ret == nxt(x))
goal = Implies(lseg(x, y), Implies(y == nil, Implies(pgm, lst(ret))))

# parameters representing the grammar for synth-fun and
# terms on which finite model is extracted
# TODO: extract this automatically from grammar_string
v1, v2 = Vars('v1 v2', fgsort)
lemma_grammar_args = [v1, v2, nil]
lemma_grammar_terms = {v1, nil, nxt(nil), v2, nxt(v2), nxt(v1), nxt(nxt(v1)), nxt(nxt(nxt(v1)))}

name = 'lseg-nil-list'
grammar_string = importlib_resources.read_text('experiments', 'grammar_{}.sy'.format(name))

# Code stub that allows the usage of user-provided true counterexample models
# NOTE: make sure config_params is defined, otherwise define an empty dictionary
config_params = dict()
with importlib_resources.path('experiments', 'interactive_cex') as interactive_cex_folder:
    true_model_files = [f for f in os.listdir(interactive_cex_folder) if f.endswith('.json')]
    true_models = []
    for true_model_file in true_model_files:
        true_model_jsonstr = open(os.path.join(interactive_cex_folder, true_model_file), 'r').read()
        true_model = loadjsonstr(true_model_jsonstr, default_annctx)
        true_models.append(true_model)
    config_params['true_models'] = true_models

# NOTE: make sure to include config_params in the arguments to solveProblem as shown below
solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string, config_params=config_params)
