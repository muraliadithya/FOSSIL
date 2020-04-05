from z3 import *
import itertools

# Each true model is a dictionary with keys being names of constants/functions, and values being
##the valuation of the item. For a constant, the entry is just the value of the constant. For a function,
##the value is a dictionary from tuples of arguments to the corresponding outputs.

#TODO: consider adding the signature of the constant/function to the key of the model

# Implementing a copy function because dictionary with dictionary entries is not copied as expected.
# The inner dictionaries are stll passed by reference
# Consider doing a more general and systematic deepcopy implementation
def deepcopyModel(model):
    new_model = {}
    for key in model.keys():
        entry = model[key]
        if isinstance(entry,list) or isinstance(entry,dict):
            new_model[key] = entry.copy()
        else:
            new_model[key] = model[key]
    return new_model


# Cartesian product of two lists of elements, with a given function applied to the pair
def listProduct(ll1, ll2, combine_func = lambda x,y: x + y):
    return [ combine_func(x,y) for x in ll1 for y in ll2 ]

# # generate all possible valuations of all functions at src
# def getTrueModelsElem(elems, fcts, src):
#     models_elt = [{}]
#     for fct in fcts:
#         fct_eval = [ { fct : { src : tgt } } for tgt in elems ]
#         models_elt = product(fct_eval, models_elt)
#     return models_elt

# Function/Predicate signatures are of the form input-arity_input-tuple-type_output-type
def getFctSignature(fct_class):
    s = fct_class.split('_')
    if s[0] == '0':
        return (0,None,None)
    else:
        return (int(s[0]),tuple(s[1:-2]),s[-1])

# Currently the symbols are returning the variable name as a string under the str() operator
# Might need to distinguish them by their Z3 types for a more reliable way
def getZ3FctName(z3_fct_variable):
    return str(z3_fct_variable)

# Generates a list of dictionaries with key corresponding to the function name and valuation being one of
##many possible valuations
def getTrueModelFctValuations(elems, fct_signature, fct_name):
    arity = fct_signature[0]
    if arity == 0:
        #Return list of dictionaries evaluating the constant symbol to any of the elements
        return [{fct_name : elem} for elem in elems]
    else:
        # Only supporting integer type, with many arguments and one output
        # Return list of dictionaries evaluating each input element/tuples of elements to aribtrary elements
        if arity == 1:
            input_values = elems
        else:
            input_values = [tuple(x) for x in itertools.product(elems,repeat=arity)]
        domain_size = len(input_values)
        output_valuations = [list(x) for x in itertools.product(elems,repeat=domain_size)]
        # Writing in a loop and not in a list comprehension to make it easier to understand
        # [{input_values[i] : x[i] for i in range(domain_size)} for x in output_valuations]
        result = []
        for i in range(len(output_valuations)):
            one_possible_valuation = {input_values[k] : output_valuations[i][k] for k in range(domain_size)}
            result = result + [{fct_name : one_possible_valuation}]
        return result

# Generate true models in the form of all posible evaluations of all functions
# This generates all possible combinations. Maybe better to get a few random ones instead if this is slow
def getTrueModels(elems, fcts_z3):
    models = [{'elems': elems}]
    for key in fcts_z3.keys():
        if key == 'recpreds_loc':
            continue
        else:
            fct_signature = getFctSignature(key)
            for fct in fcts_z3[key]:
                fct_name = getZ3FctName(fct)
                submodel_fct = getTrueModelFctValuations(elems, fct_signature, fct_name)
                models = listProduct(models, submodel_fct, lambda x,y: {**x, **y})
    return models

# nil = Int('nil')
# next = Function('next', IntSort(), IntSort())
# next_p = Function('next_p', IntSort(), IntSort())
# for x in getTrueModels([1,2,3],{'0_int': [nil],'1_int_int':[next,next_p]}):
#     print(x)


# Extract name of recdef from the python function name.
def getRecdefName(recdef_python_function):
    # It is usually u + <name> + _python
    # Make this more systematic
    recdef_name = recdef_python_function.__name__
    return '_'.join(recdef_name[1:].split('_')[:-1])

# initialize dictionary where given recdef's name is evaluated to a dictionary
## where all elements have the initial value (lattice bottom)
def initializeRecdef(model, recdef):
    #Currently supporting only boolean recursive predicates. Initial value is false
    elems = model['elems']
    recdef_name = getRecdefName(recdef)
    init = {recdef_name : {elem : False for elem in elems}}
    return init

# evaluate model via recdef functions until fixpoint is reached
def evaluateUntilFixpoint(recdef_lookup, model, prev_model = {}):
    # Currently no mutually recursive definitions, but implementation computes all definitions together
    # Currently only supporting unary recursive predicates (no functions)
    if model == prev_model:
        return model
    else:
        recdef_names = recdef_lookup.keys()
        new_prev = deepcopyModel(model)
        elems = model['elems']
        for elem in elems:
            for recdef_name in recdef_names:
                recdef_function = recdef_lookup[recdef_name]
                new_val = recdef_function(elem, model)
                model[recdef_name][elem] = new_val
        return evaluateUntilFixpoint(recdef_lookup, model, new_prev)

# # add constraints from each model into a given solver
# def modelToSolver(model, sol, z3_str):
#     for key in model.keys():
#         z3key = z3_str[key]
#         for arg in model[key].keys():
#             sol.add(z3key(arg) == model[key][arg])
#
# # return True if given model satisfies all axioms, uses Z3 solving. slow
# def filterByAxioms(model, fct_axioms):
#     axiom_sol = Solver()
#     modelToSolver(model, axiom_sol)
#     axiom_sol.add(Not(And(fct_axioms)))
#     if axiom_sol.check() == unsat:
#         return True
#     else:
#         return False
#

# same as above, uses builtin functions on the model instead of Z3 solving. fast
def filterByAxiomsFct(model, axioms_python):
    for axiom in axioms_python:
        if not axiom(model):
            return False
    return True

#Alternate definition of filter by pythona xioms where axioms are distinguished by signature
# def filterByAxiomsFct(model, axioms_python):
#     for axiom_class in axioms_python.keys():
#         signature = getFctSignature(axiom_class)
#         print(signature)
#         arity = signature[0]
#         if arity == 0:
#             for axiom in axioms_python[axiom_class]:
#                 if not axiom(model):
#                     return False
#         else:
#             elems = model['elems']
#             if arity == 1:
#                 input_values = elems
#             else:
#                 input_values = [tuple(x) for x in itertools.product(elems,repeat=arity)]
#             for axiom in axioms_python[axiom_class]:
#                 for input_value in input_values:
#                     if not axiom(input_value, model):
#                         return False
#     #Default case. All axioms are satisfied
#     return True


# evaluate recursive definitions on true model
def getRecdefsEval(models, unfold_recdefs_python):
    recdef_lookup = {getRecdefName(recdef) : recdef for recdef in unfold_recdefs_python}
    evaluated_models = []
    for model in models:
        for recdef in unfold_recdefs_python:
            init_rec = initializeRecdef(model, recdef)
            model.update(init_rec)
        #Evaluate recursive definitions. Since they may be mutually recursive they must be evaluated together
        eval_model = evaluateUntilFixpoint(recdef_lookup, model)
        evaluated_models = evaluated_models +  [ eval_model ]
    return evaluated_models

# add offset to true models to avoid non-unique keys
def addOffset(model, f):
    newModel = deepcopyModel(model)
    for key in model.keys():
        if not isinstance(model[key],dict):
            value = model[key]
            if isinstance(value, list):
               new_out = [f(i) for i in value]
            elif isinstance(value, bool):
                new_out = value
            else:
                new_out = f(value)
            newModel[key] = new_out
        else:
            newDict = {}
            for fctkey in model[key].keys():
                new_in = f(fctkey)
                if isinstance(model[key][fctkey], bool):
                    new_out = model[key][fctkey]
                else:
                    new_out = f(model[key][fctkey])
                newDict[new_in] = new_out
            newModel[key] = newDict
    return newModel

# get true models with offsets added
def getTrueModelsOffsets(elems, fcts_z3, unfold_recdefs_python, axioms_python):
    true_models_base = getTrueModels(elems, fcts_z3)
    #true_models_base = [{'elems' : [0,1,-1], 'x' : 1, 'y' : 1, 'z' : 1, 'next' : {1 : 0, 0 : -1, -1 : -1}, 'next_p' : {1 : 1, 0 : -1, -1 : -1} }]
    models = getRecdefsEval(true_models_base, unfold_recdefs_python)
    #print(models)
    filtered_models = []
    #print(len(models))
    for model in models:
        pass_or_fail = filterByAxiomsFct(model, axioms_python)
        if pass_or_fail:
            filtered_models = filtered_models + [model]
    #print(len(filtered_models))
    for i in range(len(filtered_models)):
        filtered_models[i] = addOffset(filtered_models[i], lambda x: x + 50*(i+1))
    return filtered_models