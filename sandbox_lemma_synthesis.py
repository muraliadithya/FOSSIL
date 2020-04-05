import subprocess

from z3 import *
from sandbox_true_models import *

# unfold each recursive definition on x
def unfold_recdefs(sol, recdefs_macros, x):
    for rec in recdefs_macros:
        sol.add(rec(x))

# Get false model - model where VC is false
def getFalseModel(fct_axioms, recdefs_macros, deref, const, vc):
    sol = Solver()

    # add axioms next(nil) = nil, prev(nil) = nil
    for ax in fct_axioms:
        sol.add(ax)

    # unfold constants
    for c in const:
        unfold_recdefs(sol, recdefs_macros, c)

    # unfold dereferenced variables
    for d in deref:
        unfold_recdefs(sol, recdefs_macros, d)

    # negate VC
    sol.add(Not(vc))

    # check satisfiability and print model in format CVC4 can handle 
    if (sol.check() == sat):
        m = sol.model()
        return m

    else:
        print("No model available. Lemma was proved.")

# get false model in dictionary representation
def getFalseModelDict(elems, keys, fct_axioms, recdefs_macros, deref, const, vc, z3_str):
    false_model = getFalseModel(fct_axioms, recdefs_macros, deref, const, vc)
    if false_model == None:
        exit(0)
    false_model_dict = {}
    for key in keys:
        key_dict = {}
        for elem in elems:
            z3_fct = z3_str[key]
            key_dict[elem] = false_model.eval(z3_fct(elem))
        false_model_dict[key] = key_dict
    return false_model_dict


# generate single model from a given list of models
def sygusBigModelEncoding(models, sol, z3_str):
    for model in models:
        modelToSolver(model, sol, z3_str)
    sol.check()
    m = sol.model()
    return m.sexpr()

# generate constraints corresponding to false model for SyGuS
def generateFalseConstraints(model, deref):
    out = '(constraint (or '
    for var in deref:
        out += '(not (lemma ' + str(var) + '))'
    out += '))'
    return out

# generate constraints corresponding to one true model for SyGuS
def generateTrueConstraints(model, elems, f):
    out = ''
    for elem in elems:
        if elem != -1:
            out += '(constraint (lemma ' + str(f(elem)) + '))\n'
    return out

# generate constraints corresponding to all true models for SyGuS
def generateAllTrueConstraints(models, elems):
    out = '(constraint (lemma (- 1)))\n'
    for i in range(len(models)):
        out += generateTrueConstraints(models[i], elems, lambda x: x + 50*(i+1))
    return out

# write output to a file that can be parsed by CVC4 SyGuS

#fcts -> fcts_z3
#vc_axioms -> axioms_python
#fct_axioms -> axioms_z3

def getSygusOutput(elems, fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, vc(x, y, z),\
                   preamble_file, grammar_file, out_file):
    true_models = getTrueModelsOffsets(elems, fcts_z3, axioms_python, unfold_recdefs_python)
    return None
    # keys = true_models[0].keys()
    # false_model = getFalseModelDict(elems, keys, fct_axioms, recdefs_macros,
    #                                 deref, const, vc, z3_str)
    # all_models = true_models + [ false_model ]
    # encoding_sol = Solver()
    # sygus_model = sygusBigModelEncoding(all_models, encoding_sol, z3_str)
    # with open(out_file, 'w') as out, open(preamble_file, 'r') as preamble, open(grammar_file, 'r') as grammar:
    #     for line in preamble:
    #         out.write(line)
    #     out.write('\n')
    #     out.write(';; combination of true models and false model\n')
    #     out.write(sygus_model)
    #     out.write('\n\n')
    #     for line in grammar:
    #         out.write(line)
    #     out.write('\n')
    #     out.write(';; constraints from false model\n')
    #     out.write(generateFalseConstraints(false_model, deref))
    #     out.write('\n')
    #     out.write('\n')
    #     out.write(';; constraints from true models\n')
    #     out.write(generateAllTrueConstraints(true_models, elems))
    #     out.write('\n')
    #     out.write('(check-synth)')
    # proc = subprocess.Popen(['cvc4', '--lang=sygus2', out_file], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    # cvc4_out, err = proc.communicate()
    # lemma = str(cvc4_out).split('\\n')[1]
    # return lemma
