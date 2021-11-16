import itertools
import random

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsMember, IsSubset, SetUnion, SetIntersect, SetComplement, EmptySet, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom


# dimensions of variation
# list vs trees, etc
# number of data fields/ number of relevant data fields
# changing the property p and the update (this one may or may not have much effect)
# grammar needs to be fixed automatically!


# General ideas
## Properties
# x > 0
# x > y
# even-ness
# odd-ness
# 
# a > b & c > d => a + b > c + d

# List of props
# a,b -> 2, 4 || bnx + 1, anx + 1; a > 1; a > 1 & b > 1
# a,b -> -2, -4 || bnx - 1, anx - 1; a < 0; a < 0 & b < 0
# a,b -> 2, 4 || bnx + 2, anx + 2; a % 2 == 0; a % 2 == 0 & b % 2 == 0
# a,b -> -1, -1 || bnx * 2, anx * 2; a < 0; a < 0 & b < 0
# a,b -> 2, 4 || bnx * 2, anx * 2; a > 0; a > 0 & b > 0
# a,b -> 4, 2 || 2*anx - bnx, anx; a >= 0; a >= 0 & a >= b
# a,b -> 4, 2 || (anx - bnx), bnx/2; a >= 0; a >= 0 & a >= 2*b --- need to add addition to all grammars?


# Work in progress
# a,b -> 2, 3 || bnx + 2, anx + 2; ????; (a % 2 == 0 & b % 2 == 1) || (a % 2 == 1 & b %2 == 0)
#   - maybe it will work with three fields?
# if (n.d1 is 0 then n.d2=left(n).d2+right(n).d2 else n,d2=left(n).d2+1 where n.d1 is either 1 or 0
# If X is a leaf, v(X) is 7, 23, or 31. • If X has one child Y , then v(X) = v(Y ) + 7. • If X has two children Y and Z, then v(X) = v(Y )v(Z). 
# google search cs173 strong induction
# only implement the abstract framework for trees!!!!

# Grammar cues
# set of vals: all datafields and 0
# Relations between vals: >, =, >=, %2 == 0 --- added depending on example
# negation of relations is allowed


############################# Preamble ##########################################################

# Helper function for normalising conjunctive expressions
def binary_anded(exprs):
    if len(exprs) == 0:
        return z3.BoolVal(True)
    elif len(exprs) == 1:
        return exprs[0]
    else:
        return And(exprs[0], binary_anded(exprs[1:]))


# Signature
x = Var('x', fgsort)
nil = Const('nil', fgsort)
lft = Function('lft', fgsort, fgsort)
rght = Function('rght', fgsort, fgsort)
parent = Function('parent', fgsort, fgsort)
key = Function('key', fgsort, intsort)
tree = RecFunction('tree', fgsort, boolsort)

signature = dict()
signature['x'] = x
signature['nil'] = nil
signature['lft'] = lft
signature['rght'] = rght
signature['parent'] = parent
signature['key'] = key
signature['tree'] = tree

# Additional recursive definitions
htree = RecFunction('htree', fgsort, fgsetsort)
AddRecDefinition(htree, x, If(x == nil, fgsetsort.lattice_bottom,
                              SetAdd(SetUnion(htree(lft(x)), htree(rght(x))), x)))
minr = RecFunction('minr', fgsort, intsort)
AddRecDefinition(minr, x, If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x)))))
maxr = RecFunction('maxr', fgsort, intsort)
AddRecDefinition(maxr, x, If(x == nil, -100, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))


########## Variant dimensions ##########

## Variant dimension number of datafields
define_datafields = lambda datname, datnum: [Function(f'{datname}{str(i)}', fgsort, intsort) for i in range(1, datnum + 1)]
two_fields = define_datafields('d', 2)
three_fields = define_datafields('e', 3)
# Storing all datafields and the number of active ones
datafields = {
    '2/2': {
        'fields': two_fields,
        'active': 2
    },
    '2/3': {
        'fields': three_fields,
        'active': 2
    },
    '3/3': {
        'fields': three_fields,
        'active': 3
    }
}


## Variant dimension conditional update and the update mixing method
# Helper function for constructing conditional expressions
# NOTE: uses the variable 'x' initialised above! Not good practice.
def conditional_update(cyc, update_func, update_cond, mixmethod):
    return binary_anded([If(update_cond(cyc, idx),
                            dat(x) == update_func(idx, lft(x)) if mixmethod(idx) else dat(x) == update_func(idx, rght(x)),
                            dat(x) == update_func(idx, rght(x)) if mixmethod(idx) else dat(x) == update_func(idx, lft(x))
                            )
                         for idx, dat in enumerate(cyc)])


update_conds = {
    'nocondition': lambda cyc, index: z3.BoolVal(True),
    'keyrange': lambda cyc, index: And(key(x) > z3.IntVal(-50), key(x) < z3.IntVal(50)),
    'datacompare': lambda cyc, index: cyc[index](x) == z3.IntVal(3)
}
mixmethods = {
    'normal': lambda index: True,
    'skipone': lambda index: index % 2 == 0
}


## Variant dimension tree type
treetypes = {
    # 'dag': True,
    # 'tree': SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom,
    'maxheap': And(And(key(lft(x)) <= key(x), key(rght(x)) <= key(x)),
                   SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom),
    'bst': And(And(And(-100 < key(x), key(x) < 100), And(maxr(lft(x)) <= key(x), key(x) <= minr(rght(x)))),
               SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom),
    # 'tree_p': And(And(parent(lft(x)) == x, parent(rght(x)) == x),
    #               SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom)
}
# For each type of tree also add the condition that x is not a member of the left or right subtrees
for treetype in treetypes:
    treetypes[treetype] = And(treetypes[treetype], And(SetIntersect(SetAdd(fgsetsort.lattice_bottom, x), htree(rght(x))) == fgsetsort.lattice_bottom, 
                                                       SetIntersect(htree(lft(x)), SetAdd(fgsetsort.lattice_bottom, x)) == fgsetsort.lattice_bottom))


## Variant dimension update operators and properties preserved under them
def cycidx(cyc, idx):
    return cyc[idx % len(cyc)]


properties = {
    # # a,b -> 2, 4 || bnx + 1, anx + 1; a > 1; a > 1 & b > 1
    # 'idx+1!!exp+1!!>0': {
    #     'baseschema': lambda cyc: binary_anded([dat(x) == idx+1 for idx, dat in enumerate(cyc)]),
    #     'indschema': lambda cyc: (lambda idx, arg: cycidx(cyc, idx+1)(arg) + 1),
    #     'goalschema': lambda cyc:  cyc[0](x) > 0,
    #     'lemmaschema': lambda cyc: binary_anded([dat(x) > 0 for dat in cyc]),
    #     'grammar': '(> Val 0)'
    # },
    # # a,b -> -2, -4 || bnx - 1, anx - 1; a < 0; a < 0 & b < 0
    # '(idx+1)*-2!!exp-1!!<0': {
    #     'baseschema': lambda cyc: binary_anded([dat(x) == (idx+1)*-2 for idx, dat in enumerate(cyc)]), 
    #     'indschema': lambda cyc: (lambda idx, arg: cycidx(cyc, idx+1)(arg) - 1),
    #     'goalschema': lambda cyc:  cyc[0](x) < 0,
    #     'lemmaschema': lambda cyc: binary_anded([dat(x) < 0 for dat in cyc]),
    #     'grammar': '(< Val 0)'
    # },
    # # a,b -> 2, 4 || bnx + 2, anx + 2; a % 2 == 0; a % 2 == 0 & b % 2 == 0
    # '2!!exp+2*(idx+1)!!%2==0': {
    #     'baseschema': lambda cyc: binary_anded([dat(x) == 2 for idx, dat in enumerate(cyc)]),
    #     'indschema': lambda cyc: (lambda idx, arg: cycidx(cyc, idx+1)(arg) + (idx+1)*2),
    #     'goalschema': lambda cyc:  cyc[0](x) % 2 == 0,
    #     'lemmaschema': lambda cyc: binary_anded([dat(x) % 2 == 0 for dat in cyc]),
    #     'grammar': '(= 0 (mod Val 2))'
    # },
    # # a,b -> 1, 3 || bnx + 2, anx + 2; a % 2 == 1; a % 2 == 1 & b % 2 == 1
    # '2*idx+1!!exp+2*(idx+1)!!%2==1': {
    #     'baseschema': lambda cyc: binary_anded([dat(x) == 2*idx + 1 for idx, dat in enumerate(cyc)]),
    #     'indschema': lambda cyc: (lambda idx, arg: cycidx(cyc, idx+1)(arg) + (idx+1)*2),
    #     'goalschema': lambda cyc:  cyc[0](x) % 2 == 1,
    #     'lemmaschema': lambda cyc: binary_anded([dat(x) % 2 == 1 for dat in cyc]),
    #     'grammar': '(= 1 (mod Val 2))'
    # },
    # a,b -> -1, -1 || bnx * 2, anx * 2; a < 0; a < 0 & b < 0
    '-(idx+1)!!exp*2!!<0': {
        'baseschema': lambda cyc: binary_anded([dat(x) == -(idx+1) for idx, dat in enumerate(cyc)]), 
        'indschema': lambda cyc: (lambda idx, arg: cycidx(cyc, idx+1)(arg) * 2),
        'goalschema': lambda cyc:  cyc[0](x) < 0,
        'lemmaschema': lambda cyc: binary_anded([dat(x) < 0 for dat in cyc]),
        'grammar': '(< Val 0)'
    },
    # a,b -> 2, 4 || bnx * 2, anx * 2; a > 0; a > 0 & b > 0
    '(idx+1)*2!!exp*2!!>0': {
        'baseschema': lambda cyc: binary_anded([dat(x) == (idx+1)*2 for idx, dat in enumerate(cyc)]), 
        'indschema': lambda cyc: (lambda idx, arg: cycidx(cyc, idx+1)(arg) * 2),
        'goalschema': lambda cyc:  cyc[0](x) > 0,
        'lemmaschema': lambda cyc: binary_anded([dat(x) > 0 for dat in cyc]),
        'grammar': '(> Val 0)'
    },
    # End of simple examples
    # a,b,c -> 6, 4, 2 || 2anx - cnx, 2bnx - cnx, anx; a > 0; a > 0 & a > b
    '2*(n-idx)!!2d1-dk,2d2-dk,..d1!!>0': {
        'baseschema': lambda cyc: binary_anded([dat(x) == 2*(len(cyc)-idx) for idx, dat in enumerate(cyc)]),
        'indschema': lambda cyc: (lambda idx, arg: 2*cyc[idx](arg) - cyc[-1](arg) if idx < len(cyc)-1 else cyc[0](arg)),
        'goalschema': lambda cyc: cyc[0](x) > 0,
        'lemmaschema': lambda cyc: And(cyc[0](x) > 0, cyc[0](x) > cyc[-1](x)),
        'grammar': '(> Val 0) (> Val Val)'
    },
    # # Key update examples that require an additional conjunct in the inductive case schema
    # # a,b -> 1, 2 key=1 || alx + arx, blx + brx, key = a + b; key > 0; key > 0 & a > 0 & b > 0
    # 'di>0keyupdate': {
    #     'baseschema': lambda cyc: binary_anded([key(x) == -1] + [dat(x) == idx+1 for idx, dat in enumerate(cyc)]), 
    #     'indschema': lambda cyc: (lambda idx, arg: 3*cycidx(cyc, idx)(arg)),#[key(x) == -1*sum([dat(x) for dat in cyc])] + [dat(x) == dat(lft(x)) + dat(rght(x)) for dat in cyc],
    #     'goalschema': lambda cyc: key(x) < 0,
    #     'lemmaschema': lambda cyc: binary_anded([key(x) < 0] + [dat(x) > 0 for dat in cyc]),
    #     'grammar': '(> Val 0) (< Val 0)',
    #     'indschema_extra': lambda cyc: binary_anded([key(x) == -1*sum([dat(x) for dat in cyc])])
    # },
    # # a,b -> 2, 4, key=2 || alx + arx, blx + brx, key = 3a + 5b; key%2 == 0; key%2 == 0 & a%2 == 0 & b%2 == 0
    # 'di%2==0keyupdate': {
    #     'baseschema': lambda cyc: binary_anded([key(x) == 2] + [dat(x) == 2*idx for idx, dat in enumerate(cyc)]), 
    #     'indschema': lambda cyc: (lambda idx, arg: 3*cycidx(cyc, idx)(arg)),#[key(x) == sum([(2*idx+1)*dat(x) for idx, dat in enumerate(cyc)])] + [dat(x) == dat(lft(x)) + dat(rght(x)) for dat in cyc],
    #     'goalschema': lambda cyc: key(x) % 2 == 0,
    #     'lemmaschema': lambda cyc: binary_anded([key(x) % 2 == 0] + [dat(x) % 2 == 0 for dat in cyc]),
    #     'grammar': '(= 0 (mod Val 2))',
    #     'indschema_extra': lambda cyc: binary_anded([key(x) == sum([(2*idx+1)*dat(x) for idx, dat in enumerate(cyc)])])
    # },
    # # a,b,c -> 6, 4, 2, key=1 || alx + arx, blx + brx, clx + crx, key = 2(a - b) + 3(b-c); key > 0; key > 0 & a > b
    # 'di>di+1keyupdate': {
    #     'baseschema': lambda cyc: binary_anded([key(x) == -1] + [dat(x) == 2*(len(cyc)-idx) for idx, dat in enumerate(cyc)]), 
    #     'indschema': lambda cyc: (lambda idx, arg: 3*cycidx(cyc, idx)(arg)),#[key(x) == sum([(i+1)*(cyc[i+1](x) - cyc[i](x)) for i in range(len(cyc)-1)])] + [dat(x) == dat(lft(x)) + dat(rght(x)) for dat in cyc],
    #     'goalschema': lambda cyc: key(x) < 0,
    #     'lemmaschema': lambda cyc: binary_anded([key(x) < 0] + [cycidx(cyc, i)(x) > cycidx(cyc, i+1)(x) for i in range(len(cyc)-1)]),
    #     'grammar': '(< Val 0) (> Val Val)',
    #     'indschema_extra': lambda cyc: binary_anded([key(x) == sum([(i+1)*(cyc[i+1](x) - cyc[i](x)) for i in range(len(cyc)-1)])])
    # }
}
############################# End of preamble ##########################################################

# Metavariable factory dictionary
factory = dict()
# Populating the factory
# Loop over datafields (combinations of total versus active)
for datafield_combo_idx, (datafield_combo_name, datafield_combo) in enumerate(datafields.items()):
    fields = datafield_combo['fields']
    num_active = datafield_combo['active']
    # Loop over properties
    for propidx, (propname, propvals) in list(enumerate(properties.items())):
        # Loop over datastructures
        for structidx, (structname, structcond) in list(enumerate(treetypes.items())):
            # Loop over update conditions and mixing methods
            for (updateidx, (updatename, updatecond)), (mixid, (mixname, mixmethod)) in \
                    itertools.product(enumerate(update_conds.items()), enumerate(mixmethods.items())):
                # Deterministically choose a random seed according to the example
                random.seed(16112021 + datafield_combo_idx + propidx + structidx + updateidx + mixid)
                cycle = random.sample(fields, num_active)

                # Check for additional induction schema clause for key update examples
                indschema_extra = propvals.get('indschema_extra', lambda cyc: True)
                # Construct the relevant predicates and properties
                curr = {
                    'datafields': fields,
                    'treetype': (structname, structcond),
                    'basecase': propvals['baseschema'](cycle),
                    'indcase': And(conditional_update(cycle, propvals['indschema'](cycle), updatecond, mixmethod), indschema_extra(cycle)),
                    'goalprop': propvals['goalschema'](cycle),
                    'lemmaprop': propvals['lemmaschema'](cycle),
                    'synth_grammar': propvals['grammar']
                }
                name = '__'.join([propname, structname, updatename, mixname, f'cycle={",".join(c.name() for c in cycle)}', datafield_combo_name])
                factory[name] = curr


###################################### End of factory building loop #################################


# # # Batch 3: individual examples that do not have a schema across cycle lengths. Varied across datastructures.
# # properties_3 = {
# #     # a,b -> 4, 2 || (anx - bnx), bnx/2; a >= 0; a >= 0 & a >= 2*b
# #     '4,2!!d0nx-d1nx,d1nx/2!!>=0': {
# #         'basecase': And(d[0](x) == 64, d[1](x) == 32), 
# #         'indcase_lft_nil': And(d[0](x) == d[0](rght(x)) - d[1](rght(x)), d[1](x) == d[1](rght(x))/2),
# #         'indcase_rght_nil': And(d[0](x) == d[0](lft(x)) - d[1](lft(x)), d[1](x) == d[1](lft(x))/2),
# #         'indcase_gen': And(d[0](x) == d[0](lft(x)) - d[1](lft(x)), d[1](x) == d[1](lft(x))/2),
# #         'goalprop': d[0](x) >= 0,
# #         'lemmaprop': And(d[0](x) >= 0, d[0](x) >= 2*d[1](x)),
# #         'synth_grammar': '(>= Val 0) (>= Val Val) (>= Val (+ Val Val))'
# #     },
# #     # a,b -> 2, 3 || (anx + bnx + 1), bnx + 2; a%2 == 0; a + a%2 == 0 & b%2 == 1
# #     '2,3!!d0nx+d1nx+1,d1nx+2!!a%2=0': {
# #         'basecase': And(d[0](x) == 2, d[1](x) == 3), 
# #         'indcase_lft_nil': And(d[0](x) == d[0](rght(x)) + d[1](rght(x)) + 1, d[1](x) == d[1](rght(x)) + 2),
# #         'indcase_rght_nil': And(d[0](x) == d[0](lft(x)) + d[1](lft(x)) + 1, d[1](x) == d[1](lft(x)) + 2),
# #         'indcase_gen': And(d[0](x) == d[0](lft(x)) + d[1](lft(x)) + 1, d[1](x) == d[1](lft(x)) + 2),
# #         'goalprop': d[0](x) % 2 == 0,
# #         'lemmaprop': And(d[0](x) % 2 == 0, d[1](x) % 2 == 1),
# #         'synth_grammar': '(= 0 (mod Val 2)) (= 1 (mod Val 2))'
# #     }
# # }
# # # Loop over properties
# # for propidx, (propname, propvals) in enumerate(properties_3.items()):
# #     # Loop over datastructures
# #     for structidx, (structname, structcond) in enumerate(treetypes.items()):
# #         # Construct the relevant predicates and properties
# #         curr = {
# #                 'datafields': d,
# #                 'treetype': (structname, structcond),
# #                 **propvals
# #                 }
# #         name = propname + '__' + structname + '__silobenchmark'
# #         factory[name] = curr
# # 
# # ###################################### End of Batch 3 #################################
# 
# # Template
# # curr = {
# #         'datafields': d,
# #         'treetype': True, #or other tree property
# #         'basecase': And(d[0](x) == 1, d[1](x) == 1),
# #         'indcase_lft_nil': And(d[0](x) == d[1](rght(x)) + 1, d[1](x) == d[0](rght(x)) + 1),
# #         'indcase_rght_nil': And(d[0](x) == d[1](lft(x)) + 1, d[1](x) == d[0](lft(x)) + 1),
# #         'indcase_gen': And(d[0](x) == d[1](lft(x)) + 1, d[1](x) == d[0](lft(x)) + 1),
# #         'goalprop': d[0](x) > 0,
# #         'lemmaprop': And(d[0](x) > 0, d[1](x) > 0)
# #         }
# # name = 'namestr'
# # factory[name] = curr
