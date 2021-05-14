# run `python3 translate.py goal1.smt2` to test

from z3 import *

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from collections import deque
import sys

filename = sys.argv[1]
in_file = open(filename, 'r')
Lines = in_file.readlines()
parsed_file = parse_smt2_file(filename)

def isNegatedFormula(formula):
    try:
        topmost_name = formula.decl().name()
        if topmost_name == 'not':
            return True
        else:
            return False
    except Exception:
        return False

negated_formulas = list(filter(isNegatedFormula, parsed_file))
if len(negated_formulas) != 1:
    raise Exception('Input file must have exactly 1 negated formula')
goal = negated_formulas[0].children()[0]
axioms = [f for f in parsed_file if not f in negated_formulas]

# remove comments
text = ''
for line in Lines:
    if ';' in line:
        comment_index = line.index(';')
        line = line[:comment_index] + '\n'
    text += line

declare_index = text.index('(declare-fun')
datatypes = text[:declare_index]
assert_index = text.index('(assert')
functions = text[declare_index:assert_index]
asserts = text[assert_index:]

datatypes = datatypes.split('(declare-datatypes () ((')[1:]
datatypes = [' '.join(dt.split())[:-3] for dt in datatypes]

axioms = asserts.split('(assert')[1:]
goal = ' '.join(axioms[-1].split()[:-1])
goal = '(assert ' + goal

axioms = [' '.join(ax.split())[:-1] for ax in axioms][:-1]

# Get index of matching parenthesis in a string
def getIndex(s, i):
    if s[i] != '(':
        raise Exception('Not matching parentheses.')
    d = deque()
    for k in range(i, len(s)):
        if s[k] == ')':
            d.popleft()  
        elif s[k] == '(':
            d.append(s[i])
        if not d:
            return k  
    raise Exception('Not matching parentheses.')

# return all variables in an axiom
def getVariables(formula):
    if not 'forall' in formula.split('(')[1]:
        return {}
    start = formula.index('(', formula.index('(') + 1)
    end = getIndex(formula, start)
    params = formula[start+1 : end]
    curr = 0
    var_sort_dict = {}
    while curr < len(params):
        if params[curr] == '(':
            end_param = getIndex(params, curr)
            curr_param = params[curr+1 : end_param].strip()
            var_sort = curr_param.split(' ')
            variable = var_sort[0].strip()
            sort = var_sort[1].strip()
            var_sort_dict[variable] = sort
            curr = end_param
        else:
            curr += 1
    return var_sort_dict

# return body of a formula
def getBody(formula):
    if 'forall' in formula.split('(')[1]:
        start = formula.index('(', formula.index('(') + 1)
        end = getIndex(formula, start)
        body = formula[end+1:].strip()[:-1]
    else:
        body = formula
    return '(assert ' + body + ')'

# gather all variables from all axioms
# NOTE: we assume all variables are of the foreground sort
all_variables = {}
for ax in axioms:
    curr_variables = getVariables(ax)
    all_variables.update(curr_variables)

# add z3py variables for each var
z3py_variables = {}
for var in all_variables:
    z3py_variables[var] = Var(var, fgsort)

# convert body into z3Py formulas
# TODO: does not work yet as datatypes not yet translated
z3py_axioms = []
for ax in axioms:
    body = getBody(ax)
    z3py_ax = parse_smt2_string(body, decls=z3py_variables)
    z3py_axioms += [ z3py_ax ]

print(z3py_axioms)
