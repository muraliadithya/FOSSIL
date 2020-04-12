from z3 import *

# This is the version that has one dictionary but has old values floating around
def getAxiom1(smt_str, z3_dict):
    z3_dict_copy = z3_dict.copy()
    lam = lambda w : parse_smt2_string(smt_str,decls = (z3_dict_copy.update({'fresh': w}) or z3_dict_copy))[0]
    return lam

# This is the version that has no old values floating around but possibly creates several anonymous dictionaries that will never have any variable pointing to them
def getAxiom2(smt_str, z3_dict):
    z3_dict_copy = z3_dict.copy()
    lam = lambda w : parse_smt2_string(smt_str,decls = {**z3_dict_copy, 'fresh' : w})[0]
    return lam


list = Function('list', IntSort(), BoolSort())
x, y = Ints('x y')

lemma_str = '(define-fun lemma ((x Int)) Bool (list x))\n (assert (lemma fresh))'
z3_dict = {'list': list}

ax1 = getAxiom1(lemma_str,z3_dict)
print(ax1(x))
print(ax1(y))

ax2 = getAxiom2(lemma_str, z3_dict)
print(ax2(x))
print(ax2(y))

