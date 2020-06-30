from z3 import *
from lemma_synthesis import *
from set_sort import *

####### Section 0
# some general FOL macros
# TODO: move to utils
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

# Datastructure initialisations Below are some dictionaries being
# initialised. Will be updated later with constants/functions/definitions of
# different input/output signatures

# fcts_z3 holds z3 function/predicate/recursive definition symbols.
# The signatures are written as
# <arity>_<input-tuple-type_underscore-separated>_<output-type>
# for non-recursive functions. Signatures are
# <rec*>_<arity>_<input-tuple-type_underscore-separated>_<output-type>
# forrecursive functions/predicates where <rec*> is a string starting with rec
fcts_z3 = {}

# Axioms always provide boolean output and may have different signatures for inputs
# Z3 axioms return z3's boolean type and the python version returns a boolean value
axioms_z3 = {}
axioms_python = {}

# Unfolding recursive definitions.

# The Z3 version says that the recursive call and its unfolding are equivalent
# The python version computes the value based on one level of unfolding given a
# concrete model
unfold_recdefs_z3 = {}
unfold_recdefs_python = {}

# NOTE: All axioms as well as unfoldings will only take one argument 'w'
# corresponding to the input parameters (apart from the model argument for the
# python versions). For those that require multiple arguments, this will be
# packed into a tuple before calling the functions/axioms.

######## Section 1
# Variables and Function Symbols

# The z3py variable for a z3 variable will be the same as its string value.
# So we will use the string 'x' for python functions and just x for creating z3 types
x, k, nil = Ints('x k nil')
skolem = Int('skolem')
fcts_z3['0_int'] = [x, k, nil, skolem]

######## Section 2
# Functions
next = Function('next', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
# TODO: what to do about -1 for key axioms?
fcts_z3['1_int_int'] = [next, key]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
SetIntSort = createSetSort('int')
slist = Function('slist', IntSort(), BoolSort())
slist_find_k = Function('slist_find_k', IntSort(), BoolSort())
keys = Function('keys', IntSort(), SetIntSort)

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))))

def uslist_z3(x):
    return Iff( slist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(key(x) <= key(next(x)), slist(next(x)))) ))

def uslist_find_k_z3(x):
    return Iff( slist_find_k(x), IteBool( x == nil,
                                          False,
                                          IteBool( key(x) == k,
                                                   True,
                                                   IteBool( key(x) > k,
                                                            False,
                                                            slist_find_k(next(x)) ))))

def ukeys_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    then_case = Implies(is_nil, keys(x) == emptyset)
    else_case = Implies(Not(is_nil), keys(x) == SetAdd(keys(next(x)), key(x)))
    return And(then_case, else_case)

# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def uslist_python(x, model):
    if x == model['nil']:
        return True
    elif model['next'][x] == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        sorted_cond = model['key'][x] <= model['key'][next_val]
        return sorted_cond and model['slist'][next_val]

def uslist_find_k_python(x, model):
    if x == model['nil']:
        return False
    elif model['key'][x] == model['k']:
        return True
    elif model['key'][x] > model['k']:
        return False
    else:
        next_val = model['next'][x]
        return model['slist_find_k'][next_val]

def ukeys_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_keys = model['keys'][x]
        next_keys = model['keys'][next_val]
        return {curr_key} | next_keys

unfold_recdefs_z3['1_int_bool'] = [uslist_z3, uslist_find_k_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_z3]
unfold_recdefs_python['1_int_bool'] = [uslist_python, uslist_find_k_python]
unfold_recdefs_python['1_int_set-int'] = [ukeys_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [slist, slist_find_k]
fcts_z3['recfunctions-loc_1_int_set-int'] = [keys]

############# Section 5
# Program, VC, and Instantiation

def vc(x, k):
    precondition = And(key(x) == 0, k != 0)
    return Implies( slist(x),
                    Implies(precondition, Iff( slist_find_k(x), IsMember(k, keys(x)) ) ) )

deref = [x, next(x), skolem, next(skolem)]
const = [nil, k]
elems = [*range(2)]
num_true_models = 10

# End of input
###########################################################################################################################
# Lemma synthesis stub to follow: must be replaced with a uniform function call between all examples.
##########################################################################################################################
# valid and invalid lemmas
valid_lemmas = []
invalid_lemmas = []

cex_models = []
config_params = {'mode': 'random', 'num_true_models': 0}
config_params['use_cex_models'] = True
config_params['cex_models'] = cex_models

# check if VC is provable
orig_model = getFalseModel(axioms_z3, fcts_z3, valid_lemmas, unfold_recdefs_z3, deref, const, vc(x,k), True)
if orig_model == None:
    print('original VC is provable using induction.')
    exit(0)

# continuously get valid lemmas until VC has been proven
while True:
    lemmas = getSygusOutput(elems, config_params, fcts_z3, axioms_python, axioms_z3,
                             valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                             vc(x,k), 'slist-find')
    print("lemmas: {}".format(lemmas))
    for lemma in lemmas:
        z3py_lemma = translateLemma(lemma, fcts_z3)
        if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
            print('lemma has already been proposed')
            continue
        fresh = Int('fresh')
        lemma_deref = [fresh, next(fresh)]
        (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, valid_lemmas, unfold_recdefs_z3, lemma_deref, const, z3py_lemma, True)
        if false_model_z3 != None:
            print('proposed lemma cannot be proved.')
            invalid_lemmas = invalid_lemmas + [ z3py_lemma ]
            use_cex_models = config_params.get('use_cex_models', False)
            if use_cex_models:
                cex_models = cex_models + [false_model_dict]
                config_params['cex_models'] = cex_models
                # correct_lemma = Implies(dlist(fresh), list(fresh))
                # cexmodeleval = false_model_z3.eval(correct_lemma)
                # print('cexmodeleval: {}'.format(cexmodeleval))
                # if not cexmodeleval:
                #     print(false_model_z3.sexpr())
                #     exit(0)
            # TODO: add to bag of unwanted lemmas (or add induction principle of lemma to axioms)
            # and continue
        else:
            valid_lemmas = valid_lemmas + [ z3py_lemma ]
            break
