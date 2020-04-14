from z3 import *
from lemma_synthesis import *
from natural_proofs import *

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
x, ret, nil = Ints('x ret nil')
fcts_z3['0_int'] = [x, ret, nil]

######## Section 2
# Functions
next = Function('next', IntSort(), IntSort())
key = Function('key', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as z3py formulas
next_nil_z3 = next(nil) == nil
# key_nil_z3 = key(nil) == nil

# Python version for the axioms above
def next_nil_python(model):
    return model['next'][model['nil']] == model['nil']

# def key_nil_python(model):
#     return model['key'][model['nil']] == model['nil']

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
list = Function('list', IntSort(), BoolSort())
slist = Function('slist', IntSort(), BoolSort())

############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))) )

def uslist_z3(x):
    return Iff( slist(x), IteBool( x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(key(x) <= key(next(x)), slist(next(x)))) ))

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

unfold_recdefs_z3['1_int_bool'] = [ulist_z3, uslist_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, uslist_python]

# Recall recursive predicates are always unary
fcts_z3['recpreds-loc_1_int_bool'] = [list, slist]

############# Section 5
# Program, VC, and Instantiation

def pgm(x, ret):
    return IteBool(x == nil, ret == nil, ret == next(x))

def vc(x, ret):
    return Implies( slist(x),
                    Implies(pgm(x, ret), list(ret)))

deref = [x]
const = [nil]
elems = [*range(3)]
num_true_models = 10

# translate output of cvc4 into z3py form
# TODO: abstract this out as general function, not specific to each input
def translateLemma(lemma):
    const_decls = '(declare-const fresh Int)'
    assertion = '(assert (lemma fresh nil))'
    smt_string = const_decls + '\n' + lemma + '\n' + assertion
    z3_str = extractDecls(fcts_z3)
    z3py_lemma = parse_smt2_string(smt_string, decls=z3_str)[0]
    print(z3py_lemma)
    # model = getFalseModel(axioms_z3, lemmas, unfold_recdefs_z3, deref, const, z3py_lemma, True)
    model = None
    if model == None:
        # TODO: check if lemma is valid/provable
        return z3py_lemma
    else:
        print('proposed lemma cannot be proved.')
        # TODO: add to bag of unwanted lemmas (or add induction principle of lemma to axioms)
        # and continue
        exit(0)

# bag of unwanted lemmas. initialized to empty
lemmas = []

# continuously get valid lemmas until VC has been proven
while True:
    lemma = getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3,
                           lemmas, unfold_recdefs_z3, unfold_recdefs_python, deref, const,
                           vc(x,ret), 'slist-list')
    z3py_lemma = translateLemma(lemma)
    lemmas = lemmas + [ z3py_lemma ]
