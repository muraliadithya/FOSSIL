import hashlib
import argparse

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet

from benchmark_factory import signature, factory

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula

from lemsynth.lemsynth_engine import solveProblem


# Command-line arguments to run specific benchmark
argparser = argparse.ArgumentParser()
argparser.add_argument('--name')
argparser.add_argument('--dry', action='store_true')
args = argparser.parse_args()

x = signature['x']
nil = signature['nil']
lft = signature['lft']
rght = signature['rght']
tree = signature['tree']

factory_counter = 0
# Loop over each benchmark in factory and run it
for bench_name, metavars in factory.items():
    if args.name and bench_name != args.name:
        continue
    if not args.dry:
        # Check cache to see if already run
        with open('autobench.cache', 'a+') as autobench_cache:
            autobench_cache.seek(0)
            cache = autobench_cache.read().split('\n')
            if any(bench == bench_name for bench in cache):
                # Benchmark already run
                continue
            else:
                autobench_cache.write(bench_name + '\n')

    datafields = metavars['datafields']
    structname, structcond = metavars['treetype']
    basecase = metavars['basecase']
    indcase = metavars['indcase']
    goalprop = metavars['goalprop']
    lemmaprop = metavars['lemmaprop']
    synth_str = metavars['synth_grammar']

    # !!!!!!EXPERTS ONLY!!!!: erasing the old definition of tree from annotated context
    _ = [_ for _ in default_annctx.__recdef_annotation__ if _[0] == tree]
    if len(_) > 1:
        raise Exception('There are already two tree definitions present. Something has gone wrong.')
    default_annctx.__recdef_annotation__.discard(_[0] if _ != [] else None)
    ####### Experts only segment over #########

    # Rec definition in terms of factory-generated metavariables
    AddRecDefinition(tree, x, If(x == nil, True, And(And(And(tree(lft(x)), tree(rght(x))), structcond),
                                                     If(And(lft(x) == nil, rght(x) == nil), basecase,
                                                        And(And(lft(x) != nil, rght(x) != nil), indcase)
                                                        )
                                                     )
                                 ))

    # vc
    goal = Implies(tree(x), Implies(x != nil, goalprop))

    try:
        # check validity with natural proof solver and no hardcoded lemmas
        np_solver = NPSolver()
        solution = np_solver.solve(make_pfp_formula(goal))
        if not solution.if_sat:
            raise ValueError('Goal PFP without lemmas is already valid.')
            # print('goal pfp (no lemmas) is valid')
        else:
            pass
            # print('goal pfp (no lemmas) is unprovable')

        # hardcoded lemma
        lemma_params = (x,)
        lemma_body = Implies(tree(x), Implies(x != nil, lemmaprop))
        lemmas = {(lemma_params, lemma_body)}

        # check validity of lemmas
        solution = np_solver.solve(make_pfp_formula(lemma_body))
        if not solution.if_sat:
            pass
            # print('lemma is valid')
        else:
            raise ValueError('Lemma is not inductive.')
            # print('lemma is invalid')

        # check validity with natural proof solver and hardcoded lemmas
        solution = np_solver.solve(goal, lemmas)
        if not solution.if_sat:
            pass
            # print('goal fo (with lemmas) is valid')
        else:
            raise ValueError('Goal with lemmas is unprovable.')
            # print('goal fo (with lemmas) is invalid')
            # print(solution.model)
            # exit(0)
    except ValueError as err:
        continue
    factory_counter = factory_counter + 1
    if args.dry:
        with open('autobench.cache', 'a') as f:
            f.write(bench_name + '\n')
        print(bench_name)
        continue

    # Not a dry run
    print(f'Running automatically generated benchmark: {bench_name}')

    # lemma synthesis
    v1 = Var('v1', fgsort)
    lemma_grammar_args = [v1, nil]
    lemma_grammar_terms = {v1}

    theorem_name = 'autobench__' + hashlib.md5(bench_name.encode('utf-8')).hexdigest()
    grammar_string = f"""
(synth-fun lemma ((x Int) (nil Int)) Bool

            ((Start Bool) (Val Int))

            ((Start Bool (
                    (=> Start Start)
                    (and Start Start)
                    (= x nil)
                    (not (= x nil))
                    {synth_str} ;benchmark-specific predicates
                        ))
            (Val Int (
                    (key x)
                    {' '.join('(' + dat.name() + ' x)' for dat in datafields)}
                    0
                    ))
            )
)

(synth-fun rswitch () Int

            ((Start Int))
            ((Start Int (0 )))
)
    """

    solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, theorem_name, grammar_string, autobench=True)


# Rerport on total number of sucessful benchmarks if it is a dry run
if args.dry:
    print(factory_counter)
