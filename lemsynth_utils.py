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
# Default is a + function which will work if defined for the sort of list elements
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
# Optionally, the class name might begin with 'rec<something>_' for recursive functions/predicates
# Returns (arity,input-tuple-type,output-type,recursive_or_not)
def getFctSignature(fct_class):
    s = fct_class.split('_')
    if s[0].startswith('rec'):
        return (int(s[1]),tuple(s[2:-2]),s[-1],True)
    else:
        #Not a recursive definition
        if s[0] == '0':
            return (0,None,None,False)
        else:
            return (int(s[0]),tuple(s[1:-2]),s[-1],False)

# Currently the symbols are returning the variable name as a string under the str() operator
# Might need to distinguish them by their Z3 types for a more reliable way
def getZ3FctName(z3_fct_variable):
    return str(z3_fct_variable)

# Extract name of recdef from the python function name.
def getRecdefName(recdef_python_function):
    #print('hello')
    #print(recdef_python_function)
    # It is usually u + <name> + _python
    # Make this more systematic
    recdef_name = recdef_python_function.__name__
    return '_'.join(recdef_name[1:].split('_')[:-1])
