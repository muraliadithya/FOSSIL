import subprocess

from z3 import *
from true_models import *
from false_models import *
from lemsynth_utils import *

# Add constraints from each model into the given solver
# Look through model's function entries and adds each input-output constraint
def modelToSolver(model, fcts_z3, sol):
    for key in fcts_z3.keys():
        signature = getFctSignature(key)
        arity = signature[0]
        if arity == 0:
            # TODO: handle constant symbols
            # constant symbol
            continue
        else:
            for fct in fcts_z3[key]:
                # no need to distinguish by signature as models are organised by
                # dictionaries pointing from input to output
                fct_name = getZ3FctName(fct)
                for input_arg in model[fct_name].keys():
                    output_value = model[fct_name][input_arg]
                    if isinstance(input_arg, tuple):
                        # arg must be unpacked as *arg before constructing the Z3 term
                        sol.add(fct(*input_arg) == output_value)
                    else:
                        sol.add(fct(input_arg) == output_value)

# Generate single model from a given list of models
# Returns the definitions for functions and recdefs.
# TODO: consider not using z3 for this and just generating the definitions using python code
# TODO - VERY IMPORTANT: subtle issue here. The true models' entries are
#  actually integers, whereas the false model's entries are Z3 types like
#  IntNumRef, etc. Must fix this during false model dict generation.
def sygusBigModelEncoding(models, fcts_z3):
    sol = Solver()
    for model in models:
        modelToSolver(model, fcts_z3, sol)
    sol.check()
    m = sol.model()
    return m.sexpr()

# Generate constraints corresponding to false model for SyGuS
def generateFalseConstraints(model_z3, deref, const):
    constraints = ''
    # Must convert result of model.eval using as_string() because returned value is a Z3 type like IntNumRef
    const_values = ' '.join([model_z3.eval(constant_symbol, model_completion=True).as_string() for constant_symbol in const])
    for arg in const + deref:
        # In general, arg will range over the tuples of instantiated terms
        arg_value = model_z3.eval(arg, model_completion=True)
        constraints = constraints + '(not (lemma {0} {1}))\n'.format(arg_value, const_values)
    out = '(constraint (or {0}))'.format(constraints)
    return out

# Generate constraints corresponding to one true model for SyGuS
def generateTrueConstraints(model, const):
    constraints = ''
    const_values = ' '.join([str(model[getZ3FctName(constant_symbol)]) for constant_symbol in const])
    elems = model['elems']
    for elem in elems:
        # TODO: only one universally quantified variable in desired lemma for now
        constraints = constraints + '(lemma {0} {1})\n'.format(elem,const_values)
    out = '(constraint (and {0}))\n'.format(constraints)
    return out

# Generate constraints corresponding to all true models for SyGuS
def generateAllTrueConstraints(models, const):
    out = ''
    for model in models:
        out = out + generateTrueConstraints(model, const)
    return out

# write output to a file that can be parsed by CVC4 SyGuS

# fcts -> fcts_z3
# vc_axioms -> axioms_python
# fct_axioms -> axioms_z3

def getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3, lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const, vc, problem_instance_name):
    grammar_file = 'grammar_{0}.sy'.format(problem_instance_name)
    out_file = 'out_{0}.sy'.format(problem_instance_name)

    true_models = getNTrueModels(elems, fcts_z3, unfold_recdefs_python, axioms_python, num_true_models)
    # TODO: false model currently does not have an 'elems' entry. It is not complete either.

    # However, it works because we only need the false model to provide us with valuations of the dereferenced terms.
    # Also works because the lemma for the current class of examples is not going to use any terms that have not already been explicitly computed.
    # One fix is to evalaute all terms within the false model into itself. Hopefully that can be done easily.
    (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, lemmas, unfold_recdefs_z3, deref, const, vc)
    all_models = true_models + [false_model_dict]
    sygus_model_definitions = sygusBigModelEncoding(all_models, fcts_z3)
    with open(out_file, 'w') as out, open(grammar_file, 'r') as grammar:
        out.write('(set-logic ALL)')
        out.write('\n')
        out.write(';; combination of true models and false model\n')
        out.write(sygus_model_definitions)
        out.write('\n\n')
        grammar_string = grammar.read()
        # Must modify grammar string to include arguments based on problem parameters.
        # Or generate the grammar file based on problem parameters.
        out.write(grammar_string)
        out.write('\n')
        out.write(';; constraints from false model\n')
        false_constraints = generateFalseConstraints(false_model_z3, deref, const)
        out.write(false_constraints)
        out.write('\n')
        out.write('\n')
        out.write(';; constraints from true models\n')
        true_constraints = generateAllTrueConstraints(true_models, const)
        out.write(true_constraints)
        out.write('\n')
        out.write('(check-synth)')
        out.close()
    experimental_prefetching_switch = 'on'
    if experimental_prefetching_switch == 'on':
        # Must include a parameter in the overall call for number of lemmas to be prefetched
        # Currently hardcoded
        prefetch_count = 100
        klemmas_filename = problem_instance_name + '_KLemmas.txt'
        sygus_proc = subprocess.Popen(['cvc4', '--lang=sygus2', '--sygus-stream', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        prefetch_proc = subprocess.Popen(['python3', 'prefetch_lemmas.py', klemmas_filename, str(prefetch_count)], stdin=sygus_proc.stdout, stdout=subprocess.PIPE, universal_newlines=True)
        #Timeout is given in seconds
        try:
            # Timeout given is given in seconds.
            # Currently hardcoded. Must make it a parameter
            standard_out, standard_err = prefetch_proc.communicate(timeout=60)
        except subprocess.TimeoutExpired:
            prefetch_proc.kill()
        sygus_proc.kill()
        with open(klemmas_filename, 'r') as klemmas:
            lemmas = klemmas.readlines()
            # Lemmas are returned as strings. Possibly terminated by '\n'
            # Removing possible '\n' before returning
            lemmas = [lemma[:-1] if lemma[-1] == '\n' else lemma for lemma in lemmas]
            # List of lemmas returned in string format
            return lemmas
    else:
        proc = subprocess.Popen(['cvc4', '--lang=sygus2', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
        cvc4_out, err = proc.communicate()
        if cvc4_out == 'unknown\n':
            return None
        else:
            lemma = str(cvc4_out).split('\n')[1]
            return lemma
