from z3 import *
from sandbox_lemma_synthesis import *

####### Section 0
# some general FOL macros
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

# Datastructure initialisations
# Below are some dictionaries being initialised. Will be updated later with constants/functions/definitions of different input/output signatures

# fcts_z3 holds z3 function/predicate/recursive definition symbols.
# The signatures are written as <arity>_<input-tuple-type_underscore-separated>_<output-type> for non recursive functions
# Signatures are <rec*>_<arity>_<input-tuple-type_underscore-separated>_<output-type> for recursive functions/predicates where <rec*> is a string starting with rec
fcts_z3 = {}
# Axioms always provide boolean output and may have different signatures for inputs
axioms_z3 = {}
axioms_python = {} #Z3 axioms return z3's boolean type and the python version returns a boolean value
# Unfolding recursive definitions.
# The Z3 version says that the recursive call and its unfolding are equal (or bi-implication if predicate)
# The python version computes the value based on one level of unfolding
unfold_recdefs_z3 = {}
unfold_recdefs_python = {}

# NOTE: All axioms (both z3 and python versions) as well as the unfoldings (both z3 and python versions)
## will only take one argument 'w' corresponding to the input parameters (apart from the model argument for the python versions).
## For those that require multiple arguments, this will be packed into a tuple before calling the functions/axioms.

######## Section 1
# Variables and Function Symbols

# The z3py variable for a z3 variable will be the same as its string value.
# So we will use the string 'x' for python functions and just x for creating z3 types
x, ret, nil = Ints('x ret nil')
fcts_z3['0_int'] = [x,ret,nil]

######## Section 2
## Functions
next = Function('next', IntSort(), IntSort())
prev = Function('prev', IntSort(), IntSort())

# Axioms for next and prev of nil equals nil as python functions -
axiomNextNil_z3 = next(nil) == nil
axiomPrevNil_z3 = prev(nil) == nil
# Python version for the axioms above
def axiomNextNil_python(model):
    return model['next'][model['nil']] == model['nil']

def axiomPrevNil_python(model):
    return model['prev'][model['nil']] == model['nil']

# Updating fcts and fct_axioms for next and prev
# Use dict.setdefault to be able to update the dictionary in multiple stages
# Must change signature to have 'loc' rather than 'int' once types are changed for the location variables
fcts_z3['1_int_int'] = [next, prev]
axioms_z3['0'] = [axiomNextNil_z3, axiomPrevNil_z3]
axioms_python['0'] = [axiomNextNil_python, axiomPrevNil_python]

########Section 3
## Recursive definitions
# Recdefs can only be unary (on the foreground sort?)
# TODO: Must add support for recursive functions

list = Function('list', IntSort(), BoolSort())
dlist = Function('dlist', IntSort(), BoolSort())


############ Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# Macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == nil, True, list(next(x))))

def udlist_z3(x):
    return Iff( dlist(x), IteBool(x == nil,
                                   True,
                                   IteBool( next(x) == nil,
                                            True,
                                            And(prev(next(x)) == x, dlist(next(x))) )))

# Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == model['nil']:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def udlist_python(x, model):
    if x == nil:
        return True
    elif model['next'][x] == nil:
        return True
    else:
        next_val = model['next'][x]
        doubly_linked_cond = model['prev'][next_val] == x
        return doubly_linked_cond and model['dlist'][next_val]


unfold_recdefs_z3['1_int_bool'] = [ulist_z3, udlist_z3]
unfold_recdefs_python['1_int_bool'] = [ulist_python, udlist_python]

# Recursive predicates are only unary, so there's no signature apart from the fact that
## they are predicates on the loc sort
fcts_z3['recpreds-loc_1_int_bool'] = [list,dlist]


############# Section 5
# Program, VC and Instantiation

def pgm(x, ret):
    return IteBool(x == nil, ret == nil, ret == next(x))

def vc(x, ret):
    return Implies(dlist(x),
                    Implies(pgm(x, ret), list(ret)))


deref = [x]
const = [nil]
elems = [*range(3)]
num_true_models = 10


lemma = getSygusOutput(elems, num_true_models, fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, vc(x,ret), 'dlist-list')