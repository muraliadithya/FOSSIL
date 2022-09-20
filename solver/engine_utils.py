"""
Auxiliary module for engine module.  
This module implements the two stages of the synthesis engine:  
(i) Reading a SyGuS file and writing an SMT file representing the synthesis problem.  
(ii) Calling an SMT solver with appropriate options and returning a pretty printed solution.  
In a synthesis setup with multiple solutions or quantified constraints these stages will alternate 
continuously, with counterexample-guided constraints or symmetry reduction constraints 
being added in each round.  
"""

import subprocess

from solver.SyGuSGrammar import load_from_string
from solver.ConstraintGrammar import ConstraintGrammar
# from solver.lisplike import parse


# Replace SyGuS grammars in file with constraint grammars in SMT-Lib format
def sygus_to_smt(sygus_file, smt_file, options):
    """
    Write a copy of input file, replacing each SyGuS grammar by the corresponding
    constraint grammar in SMT-Lib format.
    If the options parameter contains the key 'additional_constraints', the value should be
    a list (or similar) of strings to append to the SMT file as additional constraints.
    If the options parameter contains the key 'grammar_depth', the value should be an integer
    specifying the desired grammar expansion depth for all grammars found. For each grammar,
    if this value is less than the minimum depth required to obtain an admissible string in the
    grammar, the depth used for that grammar is this minimum value instead. For each finite
    grammar, if this value is more than the maximum depth possible to obtain an admissible string
    in the grammar, the depth used for that grammar is this maximum value instead.
    If the options parameter contains the key 'proposed_solutions', the value should be
    a dictionary (or similar) such that each key is a synth-fun string name and each value is
    the corresponding proposed solution string intended to be the synthesized function body.
    The proposed solutions are currently not checked for admissibility in the grammar, but
    rather used here to check for satisfiability alongside the ambient constraints.
    :param sygus_file: string  
    :param smt_file: string  
    :param options: dict of {string: any}  
    :return grammars: list [solver.ConstraintGrammar]  
    """
    grammars = []
    with open(sygus_file) as sygus_file:
        with open(smt_file, 'w') as smt_file:
            # Manage proposed synth-fun solutions to check satisfiability with constraints
            proposed_solutions = options.get('proposed_solutions', dict())
            # Manage grammar expansion depth
            grammar_depth = options.get('grammar_depth', 50)
            # Prepare reading/writing variables
            reading_sygus = False
            synthfun_str = ''
            lisp_depth = 0
            for num, line in enumerate(sygus_file):
                # Read infile line-by-line
                if reading_sygus:
                    # SyGuS grammar is not written to the outfile
                    # Continue reading SyGuS grammar
                    # Only include uncommented portions into grammar
                    if ';' in line:
                        line = line[:line.find(';')]
                    synthfun_str += '\n' + line
                    lisp_depth += line.count('(') - line.count(')')
                    if lisp_depth <= 0:
                        # Done reading SyGuS grammar
                        reading_sygus = False
                        # Process SyGuS grammar
                        grammar = load_from_string(synthfun_str)
                        # Process constraint grammar
                        constraint_grammar = ConstraintGrammar(grammar)
                        constraint_grammar.compute_constraint_encoding(
                            max_depth=_determine_depth(grammar, grammar_depth)
                        )
                        if grammar.name in proposed_solutions:
                            proposal = proposed_solutions[grammar.name]
                            # Check admissibility of proposed solution
                            # admissible = grammar.is_admissible(parse(proposal))
                            # Write proposed solution
                            smt_file.write(constraint_grammar.proposal_to_definefun_command(proposal))
                        else:
                            # Write constraint grammar
                            smt_file.write(constraint_grammar.pretty_smt_encoding())
                        # Maintain constraint grammar
                        grammars.append(constraint_grammar)
                        synthfun_str = ''
                elif line[:11] == '(synth-fun ':
                    # Start reading SyGuS grammar into synthfun_str
                    reading_sygus = True
                    synthfun_str = line
                    lisp_depth = line.count('(') - line.count(')')
                else:
                    # Aside from grammars, infile and outfile should match
                    smt_file.write(_convert_to_smt(line))
            # Write additional constraints if any
            additional_constraints = options.get('additional_constraints', None)
            if additional_constraints:
                smt_file.write(';Additional constraints\n')
                for additional_constraint in additional_constraints:
                    smt_file.write('(assert {})\n'.format(additional_constraint))
            # Write the check-sat and get-value commands
            smt_file.write('(check-sat)\n')
            boolvars = [boolvar for gr in grammars for boolvar in gr.boolvars]
            smt_file.write('(get-value ({}))'.format(' '.join(boolvars)))
    return grammars


# Helper function for sygus_to_smt
def _convert_to_smt(line):
    """
    Convert a string into SMT format.  
    For uncommented appearances, replace 'constraint' with 'assert'  
    and eliminate '(check-synth)'.  
    :param line: string  
    :return line: string  
    """
    index = len(line)
    if ';' in line:
        index = line.find(';')
    if 'constraint' in line[:index]:
        line = line[:index].replace('constraint', 'assert') + line[index:]
    if '(check-synth)' in line[:index]:
        line = line[:index].replace('(check-synth)', '') + line[index:]
    return line


def call_solver(smtfile_name, grammars, options):
    """
    Call SMT solver on constraint-based encoding of SyGuS problem.  
    Returns a string containing the solution and a string encoding the the solution as an SMT-Lib 
    constraint for further rounds of synthesis.  
    :param smtfile_name: string  
    :param grammars: list [solver.ConstraintGrammar]  
    :param options: dict of {string: any}  
    :return: (string, string)  
    """
    # Call smt solver on smtfile_name
    smtsolver = options['smtsolver']
    smtsolver_call = _make_smtsolver_call(options)
    proc = subprocess.Popen(smtsolver_call.format(smtfile_name), shell=True, 
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    solver_out, err = proc.communicate()
    # Process output
    if solver_out == '' or 'error' in solver_out[:6]:
        raise RuntimeError('SMT solver {} returned with error: {}'.format(smtsolver, solver_out + err))
    else:
        satisfiability_result = _extract_satisfiability_result(solver_out, options)
        if satisfiability_result == 'sat':
            # Extract values from SMT model
            model = _extract_smt_model(solver_out, options)
            # Evaluate and print synthesized lemmas over SMT model
            synth_results = []
            minimised_valuations = []
            for constraint_grammar in grammars:
                synth_results.append(constraint_grammar.valuation_to_definefun_command(model))
                # Minimise the valuation before converting it into a constraint
                # This helps cut down on repeated solutions when multiple solutions are required
                minimised_valuations.append(constraint_grammar.minimise_valuation(model))
            return '\n'.join(synth_results), _valuation_as_constraint({k: v for minval in minimised_valuations 
                                                                       for k, v in minval.items()})
        elif satisfiability_result in {'unsat', 'unknown'}:
            return satisfiability_result
        else:
            raise ValueError('Backend SMT Solver {} returned an unintelligible output.'.format(options['smtsolver']))


# Auxiliary functions 
def _make_smtsolver_call(options):
    smtsolver = options['smtsolver']
    if smtsolver == 'z3':
        return 'z3 {}'
    elif smtsolver == 'cvc4':
        return 'cvc4 --lang=smt2 {} --produce-models'
    else:
        raise ValueError('Unknown SMT solver option.')


def _extract_satisfiability_result(solver_out_string, options):
    return solver_out_string.split('\n')[0]


def _extract_smt_model(solver_out_string, options):
    smtsolver = options['smtsolver']
    model = dict()
    valuation_lines = []
    if smtsolver == 'z3':
        valuation_lines = solver_out_string.split('\n')[1:-1]
    elif smtsolver == 'cvc4':
        valuation_lines = solver_out_string.split('\n')[1].split(')')[:-2]
    for line in valuation_lines:
        try:
            open_paren_index = max(i for i in range(len(line)) if line[i] == '(')
        except ValueError:
            open_paren_index = -1
        try:
            close_paren_index = next(i for i in range(len(line)) if line[i] == ')' and i > open_paren_index)
        except StopIteration:
            close_paren_index = len(line)
        line = line[open_paren_index + 1:close_paren_index]
        line = line.split(' ')
        model[line[0]] = line[1] == 'true'
    return model


def _determine_depth(grammar, proposed_depth, show=False):
    """
    Ensures that grammar depth is neither too small to achieve at least one admissible string
    nor too large beyond a finite grammar.
    """
    depth = proposed_depth
    depth = max(grammar.get_minimum_depth(), depth)
    if grammar.is_finite():
        depth = min(grammar.get_maximum_depth(), depth)
    if show and depth != proposed_depth:
        print('Increased {} grammar depth from {} to {}.'.format(grammar.name, proposed_depth, depth))
    return depth


def _valuation_as_constraint(valuation):
    return '(and {})'.format(' '.join(var if value else '(not {})'.format(var) for var, value in valuation.items()))
