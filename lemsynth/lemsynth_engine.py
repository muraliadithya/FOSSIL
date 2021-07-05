from z3 import *
import time
import warnings
import itertools

import lemsynth.grammar_utils as grammar
from lemsynth.lemma_synthesis import getSygusOutput
from lemsynth.utils import translateLemma 
import lemsynth.options as options

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.decl_api import is_var_decl, get_boolean_recursive_definitions
from naturalproofs.pfp import make_pfp_formula
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.prover_utils import get_foreground_terms
from naturalproofs.utils import get_all_subterms
from naturalproofs.extensions.finitemodel import FiniteModel
from naturalproofs.extensions.lfpmodels import gen_lfp_model


def solveProblem(lemma_grammar_args, lemma_grammar_terms, goal, name, grammar_string, config_params=None, annctx=default_annctx):
    # Extract relevant parameters for running the verification-synthesis engine from config_params
    if config_params is None:
        config_params = {}
    lemma_grammar_terms = get_all_subterms(lemma_grammar_terms)
    valid_lemmas = set()
    invalid_lemmas = []
    cex_models = []
    true_cex_models = []

    # Determine proof mode for goal
    goal_instantiation_mode = config_params.get('goal_instantiation_mode', None)
    supported_goal_instantiation_modes = {proveroptions.manual_instantiation, 
                                          proveroptions.depth_one_stratified_instantiation, 
                                          proveroptions.fixed_depth}
    if goal_instantiation_mode is None:
        # depth one stratified instantiation by default
        goal_instantiation_mode = proveroptions.depth_one_stratified_instantiation
    elif goal_instantiation_mode not in supported_goal_instantiation_modes:
        # The set of instantiation terms must stay constant
        # TODO: check for unsoundness of algorithm if instantiation mode has automatic adaptive depth.
        # If the check passes there is no need for this branch of the condition.
        raise ValueError('Unsupported or unknown proof (instantiation) mode for goal.')

    # Create properly configured solver object that checks the goal in the presence of 0 or more lemmas
    # IMPORTANT: this is the solver object that will always be used to attempt proving the goal. Doing this 
    # standardises the configuration used to prove the goal and ensures that the changes made to the 
    # solver object are reflected everywhere in the pipeline.
    goal_fo_solver = NPSolver()
    goal_fo_solver.options.instantiation_mode = goal_instantiation_mode
    if goal_instantiation_mode == proveroptions.manual_instantiation:
        goal_manual_instantiation_terms = config_params.get('goal_instantiation_terms', None)
        if goal_manual_instantiation_terms is None:
            raise ValueError('Instantiation terms must be specified for goal in manual mode.')
        goal_fo_solver.options.terms_to_instantiate = goal_manual_instantiation_terms
    elif goal_instantiation_mode == proveroptions.fixed_depth:
        # Default depth is 1
        goal_instantiation_depth = config_params.get('goal_instantiation_depth', 1)
        goal_fo_solver.options.depth = goal_instantiation_depth
    config_params['goal_solver'] = goal_fo_solver

    # check if goal is fo provable
    goal_fo_npsolution = goal_fo_solver.solve(goal)
    if goal_fo_npsolution.if_sat:
        print('goal is not first-order provable.')
    else:
        print('goal is first-order provable.')
        exit(0)

    # check if goal is fo provable using its own pfp
    ## pfp_of_goal = make_pfp_formula(goal)
    ## goal_pfp_solver = NPSolver()
    ## goal_pfp_solver.options.instantiation_mode = goal_instantiation_mode
    ## if goal_instantiation_mode == proveroptions.manual_instantiation:
    ##     warnings.warn('Manual instantiation mode: PFP of goal will be proved using the same terms the goal itself.')
    ## goal_pfp_npsolution = goal_pfp_solver.solve(pfp_of_goal)
    ## if goal_pfp_npsolution.if_sat:
    ##     print('goal cannot be proved using induction.')
    ## else:
    ##     print('goal is provable using induction.')
    ##     exit(0)

    # goal_npsolution_instantiation_terms = goal_fo_npsolution.extraction_terms
    # config_params['goal_npsolution_instantiation_terms'] = goal_npsolution_instantiation_terms
    # Temporarily disabling expanding the set of extraction terms depending on the grammar.
    # goal_extraction_terms = grammar.goal_extraction_terms(goal_npsolution_instantiation_terms, 
    #                                                       lemma_grammar_args, lemma_grammar_terms, annctx)
    # config_params['goal_extraction_terms'] = goal_extraction_terms

    # Extract relevant instantiation/extraction terms for lemmas given the grammar
    # This set is constant
    lemma_instantiation_terms = grammar.lemma_instantiation_terms(lemma_grammar_args, lemma_grammar_terms, annctx)

    # for streaming
    config_params['streaming_timeout'] = 450
    # Dictionary for logging
    final_out = {'total_lemmas': 0, 'time_charged': 0}

    # continuously get valid lemmas until goal has been proven
    while True:
        lemmas = getSygusOutput(valid_lemmas, final_out, lemma_grammar_args, goal, name, grammar_string, config_params, annctx)
        if lemmas is None or lemmas == []:
            exit('No lemmas proposed. Instance failed.')
        # Each result comes in pairs of the lemma body and the lemma lhs (called rswitch)
        lemmas = [(lemmas[i*2], lemmas[i*2+1]) for i in range(len(lemmas)//2)]
        for lemma in lemmas:
            pre_validation = time.time()
            final_out['total_lemmas'] += 1
            # convert CVC4 versions of membership, insertion to z3py versions
            SetIntSort = SetSort(IntSort())
            membership = Function('membership', IntSort(), SetIntSort, BoolSort())
            insertion = Function('insertion', IntSort(), SetIntSort, SetIntSort)
            addl_decls = {'member': membership, 'insert': insertion}
            swap_fcts = {insertion: SetAdd}
            replace_fcts = {membership: IsMember}

            # Casting the lemma into a Z3Py expression
            # Distinguish by output format of synthesis solver
            if options.streaming_synthesis_swtich:
                # Start time is constant because it's the time of the first line printed
                start_time = lemmas[0][0].split(': ')[0]
                curr_time = lemma[0].split(': ')[0]
                lemma_time = float(curr_time) - float(start_time)
                final_out['lemma_time'] = lemma_time
                rhs_pre = lemma[0].split(': ')[1]
                lhs_pre = lemma[1].split(': ')[1]
            else:
                rhs_pre = lemma[0]
                lhs_pre = lemma[1]
            rhs_lemma = translateLemma(rhs_pre, lemma_grammar_args, addl_decls, swap_fcts, replace_fcts, annctx)
            index = int(lhs_pre[-2])
            recs = get_boolean_recursive_definitions()
            lhs = recs[index]
            lhs_arity = lhs.arity()
            lhs_lemma_args = tuple(lemma_grammar_args[:lhs_arity])
            lhs_lemma = lhs(lhs_lemma_args)
            z3py_lemma_body = Implies(lhs_lemma, rhs_lemma)
            z3py_lemma_params = tuple([arg for arg in lemma_grammar_args if is_var_decl(arg)])
            z3py_lemma = (z3py_lemma_params, z3py_lemma_body)

            if options.verbose > 0:
                print('proposed lemma: {}'.format(str(z3py_lemma_body)))
            if options.verbose >= 10:
                print('total lemmas so far: ' + str(final_out['total_lemmas']))

            if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
                if options.use_cex_models:
                    print('lemma has already been proposed')
                    if z3py_lemma in invalid_lemmas:
                        print('Something is wrong. Lemma was re-proposed in the presence of countermodels. '
                              'Exiting.')
                    # TODO: remove after replacing this with a check for terms in the grammar
                    if z3py_lemma in valid_lemmas:
                        print('This is a currently known limitation of the tool. Consider restricting your grammar to '
                              'have terms of lesser height.') 
                    exit('Instance failed.')
                else:
                    # No countermodels. Check if streaming mode for synthesis is enabled.
                    if not options.streaming_synthesis_swtich:
                        raise RuntimeError('Lemmas reproposed with countermodels and streaming disabled. Unsupported.')
                    post_validation = time.time()
                    validation_time = post_validation - pre_validation
                    final_out['time_charged'] += validation_time
                    if options.verbose >= 7:
                        print('Countermodels not enabled. Retrying lemma synthesis.')
                    if options.verbose >= 10:
                        print('Current lemma handled in: ' + str(validation_time) + 's')
                        print('Time charged so far: ' + str(final_out['time_charged']) + 's')
                    continue
            pfp_lemma = make_pfp_formula(z3py_lemma_body)
            lemmaprover = NPSolver()
            lemmaprover.options.instantiation_mode = proveroptions.manual_instantiation
            lemmaprover.options.terms_to_instantiate = lemma_instantiation_terms
            lemma_npsolution = lemmaprover.solve(pfp_lemma, valid_lemmas)
            post_validation = time.time()
            validation_time = post_validation - pre_validation
            final_out['time_charged'] += validation_time
            if options.verbose >= 10 and options.streaming_synthesis_swtich:
                print('Current lemma handled in: ' + str(validation_time) + 's')
                print('Time charged so far: ' + str(final_out['time_charged']) + 's')
            if lemma_npsolution.if_sat:
                if options.verbose >= 4:
                    print('proposed lemma cannot be proved.')
                if options.debug:
                    # Check that the terms needed from the pfp of the proposed
                    # lemma do not exceed lemma_grammar_terms.
                    # Otherwise finite model extraction will not work.
                    needed_instantiation_terms = get_foreground_terms(pfp_lemma, annctx)
                    remaining_terms = needed_instantiation_terms - lemma_instantiation_terms
                    if remaining_terms != set():
                        raise ValueError('lemma_terms is too small.\n'
                                         'Lemma: {}\n'
                                         'Terms needed after pfp computation: {}'
                                         ''.format(str(z3py_lemma_body), remaining_terms))
                invalid_lemmas = invalid_lemmas + [z3py_lemma]

                use_cex_models_fallback = False
                if options.use_cex_true_models:
                    if options.verbose >= 4:
                        print('using true counterexample models')
                    true_cex_model = gen_lfp_model(3, annctx, invalid_formula=z3py_lemma)
                    if true_cex_model is not None:
                        true_model_terms = {z3.IntVal(elem) for elem in true_cex_model.fg_universe}
                        const = [arg for arg in lemma_grammar_args if not is_var_decl(arg, annctx)]
                        lemma_arity = len(lemma_grammar_args) - len(const)
                        args = itertools.product(true_model_terms, repeat=lemma_arity)
                        instantiations = [ arg for arg in args if
                                           z3.is_false(true_cex_model.smtmodel.eval(z3.substitute(z3py_lemma[1],
                                                                                                  list(zip(lemma_grammar_args[:lemma_arity], arg))),
                                                                                    model_completion=True)) ]
                        true_cex_models = true_cex_models + [(true_cex_model, {instantiations[0]})]
                        config_params['true_cex_models'] = true_cex_models
                    else:
                        # No LFP countermodel found. Supplant with PFP countermodel.
                        use_cex_models_fallback = True
                if options.use_cex_models or use_cex_models_fallback:
                    extraction_terms = lemma_npsolution.extraction_terms
                    cex_model = FiniteModel(lemma_npsolution.model, extraction_terms, annctx=annctx)
                    cex_models = cex_models + [cex_model]
            else:
                if options.verbose >= 3:
                    print('proposed lemma was proven.')
                valid_lemmas.add(z3py_lemma)
                if options.streaming_synthesis_swtich:
                    # Check if lemma helps prove goal using originally configured goal solver object
                    # TODO: introduce warning or extend streaming algorithm to multiple lemma case
                    goal_npsolution = goal_fo_solver.solve(goal, z3py_lemma)
                    if not goal_npsolution.if_sat:
                        # Lemma is useful. Exit.
                        print('Goal has been proven. Lemmas used to prove goal:')
                        for lem in valid_lemmas:
                            print(lem[1])
                        print('Total lemmas proposed: ' + str(final_out['total_lemmas']))
                        total_time = final_out['time_charged'] + final_out['lemma_time']
                        if options.verbose > 0:
                            print('Total time charged: ' + str(total_time) + 's')
                        exit(0)

                # Reset countermodels and invalid lemmas to []. We have additional information to retry the proofs.
                cex_models = []
                invalid_lemmas = []
                if options.streaming_synthesis_swtich:
                    continue
                else:
                    # End loop through lemma proposals
                    break
            # Update countermodels and prefetch parameters before next round of synthesis
            config_params['cex_models'] = cex_models

        # reset everything and increase prefetching timeout if streaming is on
        if options.streaming_synthesis_swtich:
            final_out['time_charged'] = 0
            if config_params['prefetch_timeout'] >= 3600:
                exit('Timeout reached. Exiting')
            else:
                config_params['prefetch_timeout'] *= 2
            final_out['total_lemmas'] = 0
            valid_lemmas = set()
            invalid_lemmas = []
