from z3 import *

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
    sol.check()
    m = sol.model()
    return m

# get false model in dictionary representation
def getFalseModelDict(elems, keys, fct_axioms, recdefs_macros, deref, const, vc, z3_str):
    false_model = getFalseModel(fct_axioms, recdefs_macros, deref, const, vc)
    false_model_dict = {}
    for key in keys:
        key_dict = {}
        for elem in elems:
            z3_fct = z3_str[key]
            key_dict[elem] = false_model.eval(z3_fct(elem))
        false_model_dict[key] = key_dict
    return false_model_dict

# return product of two lists of dictionaries
def product(ll1, ll2):
    out = []
    for x in ll1:
        for y in ll2:
            new_dict = x.copy()
            for key in y.keys():
                if key in new_dict:
                    new_dict_key = new_dict[key].copy()
                    new_dict_key.update(y[key])
                    new_dict[key] = new_dict_key
                else:
                    new_dict[key] = y[key]
            out += [new_dict]
    return out

# return product of two lists of lists
def productlist(ll1, ll2):
    return [ x + y for x in ll1 for y in ll2 ]

# generate all possible valuations of all functions at src
def getTrueModelsElem(elems, fcts, src):
    models_elt = [{}]
    for fct in fcts:
        fct_eval = [ { fct : { src : tgt } } for tgt in elems ]
        models_elt = product(fct_eval, models_elt)
    return models_elt

# generate true models in the form of all posible evaluations of all functions
def getTrueModels(elems, fcts):
    models = [{}]
    for elem in elems:
        models_elt = getTrueModelsElem(elems, fcts, elem)
        models = product(models, models_elt)
    return models

# initialize dictionary where all recdefs are False for all elements
def initializeRecDefs(elems, recdefs, recdef_str):
    init = {}
    for recdef in recdefs:
        curr = {}
        for elem in elems:
            curr[elem] = False
        init[recdef_str[recdef]] = curr
    return init

# evaluate model via recdef functions until fixpoint is reached
def evaluateUntilFixpoint(model, prev_model, elems, recdefs, recdef_str):
    if model == prev_model:
        return model
    new_prev = model.copy()
    for elem in elems:
        for recdef in recdefs:
            new_val = recdef(elem, model)
            model[recdef_str[recdef]][elem] = new_val
    return evaluateUntilFixpoint(model, new_prev, elems, recdefs, recdef_str)

# add constraints from each model into a given solver
def modelToSolver(model, sol, z3_str):
    for key in model.keys():
        z3key = z3_str[key]
        for arg in model[key].keys():
            sol.add(z3key(arg) == model[key][arg])

# return True if given model satisfies all axioms, uses Z3 solving. slow
def filterByAxioms(model, fct_axioms):
    axiom_sol = Solver()
    modelToSolver(model, axiom_sol)
    axiom_sol.add(Not(And(fct_axioms)))
    if axiom_sol.check() == unsat:
        return True
    else:
        return False

# same as above, uses builtin functions on the model instead of Z3 solving. fast
def filterByAxiomsFct(model, vc_axioms):
    for axiom in vc_axioms:
        if not(axiom(model)):
            return False
    return True

# evaluate recursive definitions on true model
def getRecDefsEval(elems, fcts, vc_axioms, recdefs, recdef_str):
    models = getTrueModels(elems, fcts)
    evaluated_models = []
    for model in models:
        init_recs = initializeRecDefs(elems, recdefs, recdef_str)
        model.update(init_recs)
        eval_model = evaluateUntilFixpoint(model, [], elems, recdefs, recdef_str)
        if filterByAxiomsFct(eval_model, vc_axioms):
            evaluated_models += [ eval_model ]
    return evaluated_models

# add offset to true models to avoid non-unique keys
def addOffset(model, f):
    newModel = model.copy()
    for key in model.keys():
        newDict = {}
        for fctkey in model[key].keys():
            if fctkey == -1:
                new_in = fctkey
            else:
                new_in = f(fctkey)
            if isinstance(model[key][fctkey], bool) or model[key][fctkey] == -1:
                new_out = model[key][fctkey]
            else:
                new_out = f(model[key][fctkey])
            newDict[new_in] = new_out
        newModel[key] = newDict
    return newModel

# get true models with offsets added
def getTrueModelsOffsets(elems, fcts, vc_axioms, recdefs, recdef_str):
    models = getRecDefsEval(elems, fcts, vc_axioms, recdefs, recdef_str)
    for i in range(len(models)):
        models[i] = addOffset(models[i], lambda x: x + 50*(i+1))
    return models

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
def getSygusOutput(elems, fcts, vc_axioms, fct_axioms, recdefs_macros, recdefs,
                   recdef_str, deref, const, vc, z3_str, preamble_file, grammar_file, out_file):
    true_models = getTrueModelsOffsets(elems, fcts, vc_axioms, recdefs, recdef_str)
    keys = true_models[0].keys()
    false_model = getFalseModelDict(elems, keys, fct_axioms, recdefs_macros,
                                    deref, const, vc, z3_str)
    all_models = true_models + [ false_model ]
    encoding_sol = Solver()
    sygus_model = sygusBigModelEncoding(all_models, encoding_sol, z3_str)
    with open(out_file, 'w') as out, open(preamble_file, 'r') as preamble, open(grammar_file, 'r') as grammar:
        for line in preamble:
            out.write(line)
        out.write('\n')
        out.write(';; combination of true models and false model\n')
        out.write(sygus_model)
        out.write('\n\n')
        for line in grammar:
            out.write(line)
        out.write('\n')
        out.write(';; constraints from false model\n')
        out.write(generateFalseConstraints(false_model, deref))
        out.write('\n')
        out.write('\n')
        out.write(';; constraints from true models\n')
        out.write(generateAllTrueConstraints(true_models, elems))
        out.write('\n')
        out.write('(check-synth)')
