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
datafields = lambda n: [Function(f'd{str(i)}', fgsort, intsort) for i in range(1, n + 1)]

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
AddRecDefinition(maxr, x, If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))


# Metavariable factory dictionary
factory = dict()
num_datafields = 3
num_min_datafields = 3
d = datafields(num_datafields)
signature['datafields'] = d

# Property variant dimension 'tree type'
treetypes = {
    'dag': True,
    'tree': SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom,
    'maxheap': And(And(key(lft(x)) <= key(x), key(rght(x)) <= key(x)),
                   SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom),
    'bst': And(And(And(-100 < key(x), key(x) < 100), And(maxr(lft(x)) <= key(x), key(x) <= minr(rght(x)))),
               SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom),
    'tree_p': And(And(parent(lft(x)) == x, parent(rght(x)) == x),
                  SetIntersect(htree(lft(x)), htree(rght(x))) == fgsetsort.lattice_bottom)
}
# For each type of tree also add the condition that x is not a member of the left or right subtrees
for treetype in treetypes:
    treetypes[treetype] = And(treetypes[treetype], And(SetIntersect(SetAdd(fgsetsort.lattice_bottom, x), htree(rght(x))) == fgsetsort.lattice_bottom, 
                                                       SetIntersect(htree(lft(x)), SetAdd(fgsetsort.lattice_bottom, x)) == fgsetsort.lattice_bottom))

############################# End of preamble ##########################################################

#### Populating the factory

# Batch 1: One single property both in goal and lemma. No real variation across cycles or datastructures.
# For each one give schema for basecase, indcase modifier, and synth_predicate as well as the smt expression
properties_1 = {
    # a,b -> 2, 4 || bnx + 1, anx + 1; a > 1; a > 1 & b > 1
    'idx+1!!exp+1!!>0': {
        'baseschema': lambda idx, val: idx+1, 
        'indschema': lambda idx, val: val + 1,
        'synthpred': lambda idx, val: val > 0,
        'grammar': '(> Val 0)'
    },
    # a,b -> -2, -4 || bnx - 1, anx - 1; a < 0; a < 0 & b < 0
    '(idx+1)*-2!!exp-1!!<0': {
        'baseschema': lambda idx, val: (idx+1)*-2, 
        'indschema': lambda idx, val: val - 1,
        'synthpred': lambda idx, val: val < 0,
        'grammar': '(< Val 0)'
    },
    # a,b -> 2, 4 || bnx + 2, anx + 2; a % 2 == 0; a % 2 == 0 & b % 2 == 0
    '2!!exp+2*(idx+1)!!%2==0': {
        'baseschema': lambda idx, val: 2, 
        'indschema': lambda idx, val: val + (idx+1)*2,
        'synthpred': lambda idx, val: val % 2 == 0,
        'grammar': '(= 0 (mod Val 2))'
    },
    # a,b -> 1, 3 || bnx + 2, anx + 2; a % 2 == 1; a % 2 == 1 & b % 2 == 1
    '2*idx+1!!exp+2*(idx+1)!!%2==1': {
        'baseschema': lambda idx, val: 2*idx + 1, 
        'indschema': lambda idx, val: val + (idx+1)*2,
        'synthpred': lambda idx, val: val % 2 == 1,
        'grammar': '(= 1 (mod Val 2))'
    },
    # a,b -> -1, -1 || bnx * 2, anx * 2; a < 0; a < 0 & b < 0
    '-(idx+1)!!exp*2!!<0': {
        'baseschema': lambda idx, val: -(idx+1), 
        'indschema': lambda idx, val: val * 2,
        'synthpred': lambda idx, val: val < 0,
        'grammar': '(< Val 0)'
    },
    # a,b -> 2, 4 || bnx * 2, anx * 2; a > 0; a > 0 & b > 0
    '(idx+1)*2!!exp*2!!>0': {
        'baseschema': lambda idx, val: (idx+1)*2, 
        'indschema': lambda idx, val: val * 2,
        'synthpred': lambda idx, val: val > 0,
        'grammar': '(> Val 0)'
    }
}
# Loop over properties
for propidx, (propname, propvals) in list(enumerate(properties_1.items())):
    # Loop over datastructures
    for structidx, (structname, structcond) in list(enumerate(treetypes.items())):
        # Loop over cycle lengths
        for cycle_length in range(num_min_datafields, num_datafields + 1):
            # Initialize a deterministic random seed according to the example
            random.seed(12112021 + propidx + structidx + cycle_length)
            cycle = random.sample(d, cycle_length)

            # Construct the relevant predicates and properties
            curr = {
'datafields': d,
'treetype': (structname, structcond),
'basecase': binary_anded([cycle[idx](x) == propvals['baseschema'](idx, None) for idx in range(len(cycle))]), #And(d[0](x) == 1, d[1](x) == 1)
'indcase_lft_nil': binary_anded([cycle[idx](x) == propvals['indschema'](idx, cycle[(idx+1) % len(cycle)](rght(x))) for idx in range(len(cycle))]), #And(d[0](x) == d[1](rght(x)) + 1, d[1](x) == d[0](rght(x)) + 1)
'indcase_rght_nil': binary_anded([cycle[idx](x) == propvals['indschema'](idx, cycle[(idx+1) % len(cycle)](lft(x))) for idx in range(len(cycle))]), #And(d[0](x) == d[1](lft(x)) + 1, d[1](x) == d[0](lft(x)) + 1)
'indcase_gen': binary_anded([cycle[idx](x) == propvals['indschema'](idx, cycle[(idx+1) % len(cycle)](lft(x))) for idx in range(len(cycle))]), #And(d[0](x) == d[1](lft(x)) + 1, d[1](x) == d[0](lft(x)) + 1)
'goalprop': propvals['synthpred'](None, cycle[0](x)),
'lemmaprop': binary_anded([propvals['synthpred'](None, dat(x)) for dat in cycle]), #And(d[0](x) > 0, d[1](x) > 0)
'synth_grammar': propvals['grammar']
                    }
            name = propname + '__' + structname + '__' + f'cycle={",".join(c.name() for c in cycle)}/{str(num_datafields)}'
            factory[name] = curr

###################################### End of Batch 1 #################################

# Batch 2: explicit descriptions but schema available across cycles. No variation across datastructures.
properties_2 = {
    # a,b,c -> 6, 4, 2 || 2anx - cnx, 2bnx - cnx, anx; a > 0; a > 0 & a > b
    '2*(n-idx)!!2d1-dk,2d2-dk,..d1!!>0': {
        'baseschema': lambda cyc: [dat(x) == 2*(len(cyc)-idx) for idx, dat in enumerate(cyc)], 
        'indschema_lft_nil': lambda cyc: [dat(x) == 2*dat(rght(x)) - cyc[-1](rght(x)) for dat in cyc[:-1]] + [cyc[-1](x) == cyc[0](rght(x))],
        'indschema_rght_nil': lambda cyc: [dat(x) == 2*dat(lft(x)) - cyc[-1](lft(x)) for dat in cyc[:-1]] + [cyc[-1](x) == cyc[0](lft(x))],
        'indschema_gen': lambda cyc: [dat(x) == 2*dat(lft(x)) - cyc[-1](lft(x)) for dat in cyc[:-1]] + [cyc[-1](x) == cyc[0](lft(x))],
        'goalschema': lambda cyc: [cyc[0](x) > 0],
        'lemmaschema': lambda cyc: [cyc[0](x) > 0, cyc[0](x) > cyc[-1](x)],
        'grammar': '(> Val 0) (> Val Val)'
    },
}
# Loop over properties
for propidx, (propname, propvals) in enumerate(properties_2.items()):
    # Loop over datastructures
    for structidx, (structname, structcond) in enumerate(treetypes.items()):
        # Loop over cycle lengths
        for cycle_length in range(num_min_datafields, num_datafields + 1):
            # Initialize a deterministic random seed according to the example
            random.seed(13112021 + propidx + structidx + cycle_length)
            cycle = random.sample(d, cycle_length)

            # Construct the relevant predicates and properties
            curr = {
'datafields': d,
'treetype': (structname, structcond),
'basecase': binary_anded(propvals['baseschema'](cycle)),
'indcase_lft_nil': binary_anded(propvals['indschema_lft_nil'](cycle)),
'indcase_rght_nil': binary_anded(propvals['indschema_rght_nil'](cycle)),
'indcase_gen': binary_anded(propvals['indschema_gen'](cycle)),
'goalprop': binary_anded(propvals['goalschema'](cycle)),
'lemmaprop': binary_anded(propvals['lemmaschema'](cycle)),
'synth_grammar': propvals['grammar']
                    }
            name = propname + '__' + structname + '__' + f'cycle={",".join(c.name() for c in cycle)}/{str(num_datafields)}'
            factory[name] = curr

###################################### End of Batch 2 #################################
# Batch 3: individual examples that do not have a schema across cycle lengths. Varied across datastructures.
properties_3 = {
    # a,b -> 4, 2 || (anx - bnx), bnx/2; a >= 0; a >= 0 & a >= 2*b
    '4,2!!d0nx-d1nx,d1nx/2!!>=0': {
        'basecase': And(d[0](x) == 64, d[1](x) == 32), 
        'indcase_lft_nil': And(d[0](x) == d[0](rght(x)) - d[1](rght(x)), d[1](x) == d[1](rght(x))/2),
        'indcase_rght_nil': And(d[0](x) == d[0](lft(x)) - d[1](lft(x)), d[1](x) == d[1](lft(x))/2),
        'indcase_gen': And(d[0](x) == d[0](lft(x)) - d[1](lft(x)), d[1](x) == d[1](lft(x))/2),
        'goalprop': d[0](x) >= 0,
        'lemmaprop': And(d[0](x) >= 0, d[0](x) >= 2*d[1](x)),
        'synth_grammar': '(>= Val 0) (>= Val Val) (>= Val (+ Val Val))'
    },
    # a,b -> 2, 3 || (anx + bnx + 1), bnx + 2; a%2 == 0; a + a%2 == 0 & b%2 == 1
    '2,3!!d0nx+d1nx+1,d1nx+2!!a%2=0': {
        'basecase': And(d[0](x) == 2, d[1](x) == 3), 
        'indcase_lft_nil': And(d[0](x) == d[0](rght(x)) + d[1](rght(x)) + 1, d[1](x) == d[1](rght(x)) + 2),
        'indcase_rght_nil': And(d[0](x) == d[0](lft(x)) + d[1](lft(x)) + 1, d[1](x) == d[1](lft(x)) + 2),
        'indcase_gen': And(d[0](x) == d[0](lft(x)) + d[1](lft(x)) + 1, d[1](x) == d[1](lft(x)) + 2),
        'goalprop': d[0](x) % 2 == 0,
        'lemmaprop': And(d[0](x) % 2 == 0, d[1](x) % 2 == 1),
        'synth_grammar': '(= 0 (mod Val 2)) (= 1 (mod Val 2))'
    }
}
# Loop over properties
for propidx, (propname, propvals) in enumerate(properties_3.items()):
    # Loop over datastructures
    for structidx, (structname, structcond) in enumerate(treetypes.items()):
        # Construct the relevant predicates and properties
        curr = {
                'datafields': d,
                'treetype': (structname, structcond),
                **propvals
                }
        name = propname + '__' + structname + '__silobenchmark'
        factory[name] = curr

###################################### End of Batch 3 #################################
# Batch 4: explicit descriptions and schema across cycles, but lemma is linear in the size of the cycle
properties_4 = {
    # a,b -> 1, 2 key=1 || alx + arx, blx + brx, key = a + b; key > 0; key > 0 & a > 0 & b > 0
    'di>0': {
        'baseschema': lambda cyc: [key(x) == -1] + [dat(x) == idx+1 for idx, dat in enumerate(cyc)], 
        'indschema_lft_nil': lambda cyc: [key(x) == key(rght(x))] + [dat(x) == dat(rght(x)) + 1 for dat in cyc],
        'indschema_rght_nil': lambda cyc: [key(x) == key(lft(x))] + [dat(x) == dat(lft(x)) + 2 for dat in cyc],
        'indschema_gen': lambda cyc: [key(x) == -1*sum([dat(x) for dat in cyc])] + [dat(x) == dat(lft(x)) + dat(rght(x)) for dat in cyc],
        'goalschema': lambda cyc: [key(x) < 0],
        'lemmaschema': lambda cyc: [key(x) < 0] + [dat(x) > 0 for dat in cyc],
        'grammar': '(> Val 0) (< Val 0)'
    },
    # a,b -> 2, 4, key=2 || alx + arx, blx + brx, key = 3a + 5b; key%2 == 0; key%2 == 0 & a%2 == 0 & b%2 == 0
    'di%2==0': {
        'baseschema': lambda cyc: [key(x) == 2] + [dat(x) == 2*idx for idx, dat in enumerate(cyc)], 
        'indschema_lft_nil': lambda cyc: [key(x) == key(rght(x))] + [dat(x) == dat(rght(x)) + 2 for dat in cyc],
        'indschema_rght_nil': lambda cyc: [key(x) == key(lft(x))] + [dat(x) == dat(lft(x)) + 2 for dat in cyc],
        'indschema_gen': lambda cyc: [key(x) == sum([(2*idx+1)*dat(x) for idx, dat in enumerate(cyc)])] + [dat(x) == dat(lft(x)) + dat(rght(x)) for dat in cyc],
        'goalschema': lambda cyc: [key(x) % 2 == 0],
        'lemmaschema': lambda cyc: [key(x) % 2 == 0] + [dat(x) % 2 == 0 for dat in cyc],
        'grammar': '(= 0 (mod Val 2))'
    },
    # a,b,c -> 6, 4, 2, key=1 || alx + arx, blx + brx, clx + crx, key = 2(a - b) + 3(b-c); key > 0; key > 0 & a > b
    'di>di+1': {
        'baseschema': lambda cyc: [key(x) == -1] + [dat(x) == 2*(len(cyc)-idx) for idx, dat in enumerate(cyc)], 
        'indschema_lft_nil': lambda cyc: [key(x) == key(rght(x))] + [dat(x) == dat(rght(x)) + 1 for dat in cyc],
        'indschema_rght_nil': lambda cyc: [key(x) == key(lft(x))] + [dat(x) == dat(lft(x)) + 1 for dat in cyc],
        'indschema_gen': lambda cyc: [key(x) == sum([(i+1)*(cyc[i+1](x) - cyc[i](x)) for i in range(len(cyc)-1)])] + [dat(x) == dat(lft(x)) + dat(rght(x)) for dat in cyc],
        'goalschema': lambda cyc: [key(x) < 0],
        'lemmaschema': lambda cyc: [key(x) < 0] + [cyc[i](x) > cyc[i+1](x) for i in range(len(cyc)-1)],
        'grammar': '(< Val 0) (> Val Val)'
    },

}
# Loop over properties
for propidx, (propname, propvals) in enumerate(properties_4.items()):
    # Loop over datastructures
    for structidx, (structname, structcond) in enumerate(treetypes.items()):
        # Loop over cycle lengths
        for cycle_length in range(num_min_datafields, num_datafields + 1):
            # Initialize a deterministic random seed according to the example
            random.seed(14112021 + propidx + structidx + cycle_length)
            cycle = random.sample(d, cycle_length)

            # Construct the relevant predicates and properties
            curr = {
'datafields': d,
'treetype': (structname, structcond),
'basecase': binary_anded(propvals['baseschema'](cycle)),
'indcase_lft_nil': binary_anded(propvals['indschema_lft_nil'](cycle)),
'indcase_rght_nil': binary_anded(propvals['indschema_rght_nil'](cycle)),
'indcase_gen': binary_anded(propvals['indschema_gen'](cycle)),
'goalprop': binary_anded(propvals['goalschema'](cycle)),
'lemmaprop': binary_anded(propvals['lemmaschema'](cycle)),
'synth_grammar': propvals['grammar']
                    }
            name = propname + '__' + structname + '__' + f'cycle={",".join(c.name() for c in cycle)}/{str(num_datafields)}' + '__linearsizelemma'
            factory[name] = curr

###################################### End of Batch 4 #################################

# Template
# curr = {
#         'datafields': d,
#         'treetype': True, #or other tree property
#         'basecase': And(d[0](x) == 1, d[1](x) == 1),
#         'indcase_lft_nil': And(d[0](x) == d[1](rght(x)) + 1, d[1](x) == d[0](rght(x)) + 1),
#         'indcase_rght_nil': And(d[0](x) == d[1](lft(x)) + 1, d[1](x) == d[0](lft(x)) + 1),
#         'indcase_gen': And(d[0](x) == d[1](lft(x)) + 1, d[1](x) == d[0](lft(x)) + 1),
#         'goalprop': d[0](x) > 0,
#         'lemmaprop': And(d[0](x) > 0, d[1](x) > 0)
#         }
# name = 'namestr'
# factory[name] = curr
