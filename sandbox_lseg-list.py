from z3 import *
from lemma_synthesis import *
from sandbox_true_models import *

# some general FOL macros
def Iff(b1, b2):
    return And(Implies(b1, b2), Implies(b2, b1))

def IteBool(b, l, r):
    return And(Implies(b, l), Implies(Not(b), r))

########Section 1
#Initial definition. Will be updated later with constants/functions of different signatures
fcts_z3 = {}
#Axioms always provide boolean output and may have different signatures for inputs
axioms_z3 = {}
axioms_python = {} #Z3 axioms return z3's boolean type and the python version returns a boolean value

#Variable declaration. The z3py variable for a z3 variable will be the same as its string value.
#So we will use the string 'x' for python functions and just x for creating z3 types
x, y, z, nil = Ints('x y z nil')
fcts_z3['0_int'] = [x,y,z,nil]
#######Section 2
## functions
next = Function('next', IntSort(), IntSort())
next_p = Function('next_p', IntSort(), IntSort())

# axiom for nexty with ite
def next_p_fct_axiom_z3(w):
    return IteBool(w == y, next_p(w) == z, next_p(w) == next(w))
#Python version for the above axiom for true model generation
def next_p_fct_axiom_python(model):
    elems = model['elems']
    for w in elems:
        if w == model['y']:
            if model['next_p'][w] != model['z']:
                return False
        else:
            if model['next_p'][w] != model['next'][w]:
                return False
    #Defaul case. All elements satisfy axiom
    return True

# axioms for next and prev of nil equals nil as python functions -
axiomNextNil_z3 = next(-1) == -1
axiomNextpNil_z3 = next_p(-1) == -1
# Python version for the axioms above
def axiomNextNil_python(model):
    return model['next'][-1] == -1

def axiomNextpNil_python(model):
    return model['next_p'][-1] == -1

#Updating fcts and fct_Axioms for next and next_p
#Use dict.setdefault to be able to update the dictionary in multiple stages
#Must change signature to have 'loc' rather than 'int' once types are changed for the location variables
fcts_z3['1_int_int'] = [next, next_p]
axioms_z3['0'] = [axiomNextNil_z3, axiomNextpNil_z3]
axioms_z3['1_int'] = [next_p_fct_axiom_z3]
axioms_python = [axiomNextNil_python, axiomNextpNil_python]
axioms_python = axioms_python + [next_p_fct_axiom_python]
# axioms_python['0'] = [axiomNextNil_python, axiomNextpNil_python]
# axioms_python['1_int'] = [next_p_fct_axiom_python]

########Section 3
## Recursive definitions
# Recdefs can only be unary (on the foreground sort?)
# TODO: Must add support for recursive functions

list = Function('list', IntSort(), BoolSort())
lsegy = Function('lsegy', IntSort(), BoolSort())
list_p = Function('list_p', IntSort(), BoolSort())
lsegy_p = Function('lsegy_p', IntSort(), BoolSort())

#Axioms about recdefs
axiomLsegyNil_z3 = lsegy(-1) == False
axiomLsegypNil_z3 = lsegy_p(-1) == False
#Python versions of axioms
def axiomLsegyNil_python(model):
    return model['lsegy'][-1] == False
def axiomLsegypNil_python(model):
    return model['lsegy_p'][-1] == False

axioms_z3['0'] = axioms_z3['0'] + [axiomLsegyNil_z3,axiomLsegypNil_z3]
axioms_python = axioms_python + [axiomLsegyNil_python,axiomLsegypNil_python]
#axioms_python['0'] = axioms_python['0'] + [axiomLsegyNil_python,axiomLsegypNil_python]

#vc_axioms  = [axiomNextNil, axiomPrevNil, axiomLsegNil]

############Section 4
# Unfolding recursive definitions
# TODO: Must add support for recursive functions

# macros for unfolding recursive definitions
def ulist_z3(x):
    return Iff( list(x), IteBool(x == -1, True, list(next(x))) )

def ulsegy_z3(x):
    return Iff( lsegy(x), IteBool(x == y, True, lsegy(next(x))) )

def ulist_p_z3(x):
    return Iff( list_p(x), IteBool(x == -1, True, list_p(next_p(x))) )

def ulsegy_p_z3(x):
    return Iff( lsegy_p(x), IteBool(x == y, True, lsegy_p(next_p(x))) )

#Python versions for finding valuation on true models
def ulist_python(x, model):
    if x == -1:
        return True
    else:
        next_val = model['next'][x]
        return model['list'][next_val]

def ulsegy_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next'][x]
        return model['lsegy'][next_val]

def ulist_p_python(x, model):
    if x == -1:
        return True
    else:
        next_val = model['next_p'][x]
        return model['list_p'][next_val]

def ulsegy_p_python(x, model):
    if x == model['y']:
        return True
    else:
        next_val = model['next_p'][x]
        return model['lsegy_p'][next_val]

unfold_recdefs_z3 = [ulist_z3, ulsegy_z3, ulist_p_z3, ulsegy_p_z3]
unfold_recdefs_python = [ulist_python, ulsegy_python, ulist_p_python, ulsegy_p_python]


# Defining the VC and calling the lemma synthesis solver
#recdef_str = { list_fct : 'list', lsegy_fct : 'lsegy',
#               list_p_fct : 'list_p', lsegy_p_fct : 'lsegy_p' }
# Z3Py representation of strings (for converting internal model to Z3Py model)
#z3_str = { 'list' : list, 'lsegy' : lsegy, 'list_p' : list_p, 'lsegy_p' : lsegy_p,
#           'next' : next, 'next_p' : next_p }

# Recursive predicates are only unary, so there's no signature apart from the fact that
## they are predicates on the loc sort
fcts_z3['recpreds_loc'] = [list,lsegy,list_p,lsegy_p]


# VC
def pgm(x, y, z):
    return And( lsegy(x), next(y) == -1, list(z) )

def vc(x, y, z):
    return Implies( pgm(x, y, z), list_p(x) )


deref = [x]
const = [-1, z, y]
elems = [-1, *range(2)]

#for i in deref + const:
#    fct_axioms = fct_axioms [ next_p_fct_axiom(i) ]

#fcts -> fcts_z3
#vc_axioms -> axioms_python
#fct_axioms -> axioms_z3

#lemma = getSygusOutput(elems, fcts_z3, axioms_python, axioms_z3, unfold_recdefs_z3, unfold_recdefs_python, deref, const, vc(x, y, z),\
#                       'preamble_lseg-list.sy', 'grammar_lseg-list.sy', 'out_lseg-list.sy')

#print(lemma)

# TODO: enforce small false model?

# models = getTrueModelsOffsets(elems, fcts_z3, unfold_recdefs_python, axioms_python)
# print(len(models))
# ls = [10,40,100]
# for i in ls:
#     print(models[i])