from z3 import *
from lemsynth.set_sort import *
from lemsynth.lemma_synthesis import *
from lemsynth.true_models import *

raise NotImplementedError

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
x, y, yp, nil = Ints('x y yp nil')
fcts_z3['0_int'] = [x, y, yp, nil]

####### Section 2
# Functions
next = Function('next', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and next' of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# Updating fcts and fct_Axioms for next and next_p
# TODO: change signature to have 'loc' rather than 'int'
fcts_z3['1_int_int'] = [next, key]
axioms_z3['0'] = [next_nil_z3]
axioms_python['0'] = [next_nil_python]

######## Section 3
# Recursive definitions

# Recdefs can only be unary (on the foreground sort?)
# TODO: add support for recursive functions
SetIntSort = createSetSort('int')
list = Function('list', IntSort(), BoolSort())
lseg_y = Function('lseg_y', IntSort(), BoolSort())
lseg_yp = Function('lseg_yp', IntSort(), BoolSort())
keys = Function('keys', IntSort(), SetIntSort)
lsegkeys_y = Function('lsegkeys_y', IntSort(), SetIntSort)
lsegkeys_yp = Function('lsegkeys_yp', IntSort(), SetIntSort)

############ Section 4
# Unfolding recursive definitions
# TODO: add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))) )

def ulseg_y_z3(x):
    return Iff( lseg_y(x), IteBool(x == y, True, lseg_y(next(x))) )

def ulseg_yp_z3(x):
    return Iff( lseg_yp(x), IteBool(x == yp, True, lseg_yp(next(x))) )

def ukeys_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_nil = x == nil
    in_domain = list(x)
    then_case = Implies(is_nil, keys(x) == emptyset)
    else_case = Implies(Not(is_nil), keys(x) == SetAdd(keys(next(x)), key(x)))
    return And(then_case, else_case)

def ulsegkeys_y_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_y = x == y
    in_domain = lseg_y(x)
    then_case = Implies(is_y, lsegkeys_y(x) == emptyset)
    else_case = Implies(Not(is_y), lsegkeys_y(x) == SetAdd(lsegkeys_y(next(x)), key(x)))
    return And(then_case, else_case)

def ulsegkeys_yp_z3(x):
    emptyset = getSortEmptySet(SetIntSort)
    is_yp = x == yp
    # in_domain = lseg_yp(x)
    then_case = Implies(is_yp, lsegkeys_yp(x) == emptyset)
    else_case = Implies(Not(is_yp), lsegkeys_yp(x) == SetAdd(lsegkeys_yp(next(x)), key(x)))
    return And(then_case, else_case)

# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def ulseg_y_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next'][x]
        return model['lseg_y'][next_val]

def ulseg_yp_python(x, model):
    if x == model['yp']:
        return True
    else:
        next_val = model['next'][x]
        return model['lseg_yp'][next_val]

def ukeys_python(x, model):
    if x == model['nil']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_keys = model['keys'][x]
        next_keys = model['keys'][next_val]
        curr_list = model['list'][x]
        if curr_list:
            return {curr_key} | next_keys
        else:
            return curr_keys

def ulsegkeys_y_python(x, model):
    if x == model['y']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_lsegkeys = model['lsegkeys_y'][x]
        next_lsegkeys = model['lsegkeys_y'][next_val]
        curr_lseg = model['lseg_y'][x]
        if curr_lseg:
            return {curr_key} | next_lsegkeys
        else:
            return curr_lsegkeys

def ulsegkeys_yp_python(x, model):
    if x == model['yp']:
        return set()
    else:
        next_val = model['next'][x]
        curr_key = model['key'][x]
        curr_lsegkeys = model['lsegkeys_yp'][x]
        next_lsegkeys = model['lsegkeys_yp'][next_val]
        curr_lseg = model['lseg_yp'][x]
        if curr_lseg:
            return {curr_key} | next_lsegkeys
        else:
            return curr_lsegkeys

unfold_recdefs_z3['1_int_bool'] = [ulist_z3, ulseg_y_z3, ulseg_yp_z3]
unfold_recdefs_z3['1_int_set-int'] = [ukeys_z3, ulsegkeys_y_z3, ulsegkeys_yp_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, ulseg_y_python, ulseg_yp_python]
unfold_recdefs_python['1_int_set-int'] = [ukeys_python, ulsegkeys_y_python, ulsegkeys_yp_python]

pfp_dict = {}
pfp_dict['list'] = """
(=> (ite (= {primary_arg} {nil})
         true
         (and (list (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))
"""
pfp_dict['lseg_y'] = """
(=> (ite (= {primary_arg} {y})
         true
         (and (lseg_y (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))
"""

pfp_dict['lseg_yp'] = """
(=> (ite (= {primary_arg} {yp})
         true
         (and (lseg_yp (next {primary_arg})) (lemma (next {primary_arg}) {rest_args})))
    (lemma {primary_arg} {rest_args}))
"""

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [list, lseg_y, lseg_yp]
fcts_z3['recfunctions-loc_1_int_set-int'] = [keys, lsegkeys_y, lsegkeys_yp]

############# Section 5
# Program, VC, and Instantiation

# lemma: lsegy(x) /\ next(y) = yp => lsegkeys_yp(x) = lsegkeys_y(x) U {key(y)}
# Implies(lseg_y(x), Implies(next(y) == yp, lsegkeys_yp(x) == SetAdd(lsegkeys_y(x), key(y))))

def pgm(x, y, yp):
    precondition = And(list(x), lseg_y(x), keys(x) == SetUnion(lsegkeys_y(x), keys(y)))
    program_body = next(y) == yp
    return And(precondition, program_body)

def vc(x, y, yp):
    return Implies( pgm(x, y, yp), keys(x) == SetUnion(lsegkeys_yp(x), keys(yp)) )

deref = [x, next(y)]
const = [nil, y, yp]

elems = [*range(2)]

# End of input
################################################################################
# Lemma synthesis stub to follow: must be replaced with a uniform function call
# between all examples.
################################################################################

fresh = Int('fresh')

# valid and invalid lemmas
valid_lemmas = [Implies(list(fresh), Implies(lseg_y(fresh), Implies(lseg_yp(y), Not(lseg_y(yp)))))]
invalid_lemmas = []

cex_models = []
config_params = {'mode': 'random', 'num_true_models': 0}
config_params['pfp_dict'] = pfp_dict
config_params['use_cex_models'] = True
config_params['cex_models'] = cex_models

fresh = Int('fresh')
skolem = Int('skolem')

lemma = Implies(lseg_y(fresh), Implies(list(fresh), Implies(next(y) == yp, lsegkeys_yp(fresh) == SetAdd(lsegkeys_y(fresh), key(y)))))
lemma_deref = [ skolem, next(skolem), fresh, next(fresh), y, next(y), yp ]
(false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, valid_lemmas, unfold_recdefs_z3, lemma_deref, const, lemma, True)

# continuously get valid lemmas until VC has been proven
while True:
    lemma = getSygusOutput(elems, config_params, fcts_z3, axioms_python, axioms_z3,
                           valid_lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                           vc(x,y,yp), 'lseg-keys')
    insert_tmp = Function('insert_tmp', IntSort(), SetIntSort, SetIntSort)
    addl_decls = { 'insert': insert_tmp }
    swaps = { insert_tmp: SetAdd }
    rhs_lemma = translateLemma(lemma[0], fcts_z3, addl_decls, swaps)
    index = int(lemma[1][-2])
    lhs_lemma = fcts_z3['recpreds-loc_1_int_bool'][index](fresh)
    z3py_lemma = Implies(lhs_lemma, rhs_lemma)
    print('proposed lemma: ' + str(z3py_lemma))
    if z3py_lemma in invalid_lemmas or z3py_lemma in valid_lemmas:
            print('lemma has already been proposed')
            continue
    lemma_deref = []
    (false_model_z3, false_model_dict) = getFalseModelDict(fcts_z3, axioms_z3, valid_lemmas, unfold_recdefs_z3, lemma_deref, const, z3py_lemma, True)
    if false_model_z3 != None:
        print('proposed lemma cannot be proved.')
        invalid_lemmas = invalid_lemmas + [ z3py_lemma ]
        use_cex_models = config_params.get('use_cex_models', False)
        if use_cex_models:
            cex_models = cex_models + [false_model_dict]
    else:
        valid_lemmas = valid_lemmas + [ z3py_lemma ]
        # Reset countermodels and invalid lemmas to empty because we have
        # additional information to retry those proofs.
        cex_models = []
        invalid_lemmas = []
    # Update countermodels before next round of synthesis
    config_params['cex_models'] = cex_models
