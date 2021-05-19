# run `python3 translate.py goal1.smt2` to test

from z3 import *

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom

from collections import deque
import sys

filename = sys.argv[1]
in_file = open(filename, 'r')
Lines = in_file.readlines()
# parsed_file = parse_smt2_file(filename)

def isNegatedFormula(formula):
    try:
        topmost_name = formula.decl().name()
        if topmost_name == 'not':
            return True
        else:
            return False
    except Exception:
        return False

# negated_formulas = list(filter(isNegatedFormula, parsed_file))
# if len(negated_formulas) != 1:
#     raise Exception('Input file must have exactly 1 negated formula')
# goal = negated_formulas[0].children()[0]
# axioms = [f for f in parsed_file if not f in negated_formulas]

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
if len(datatypes) != 1:
    raise Exception('Must be exactly 1 datatype corresponding to fgsort')
fg_datatype = datatypes[0]

functions = functions.split('(declare-fun ')[1:]
functions = [' '.join(fct.split()).strip()[:-1] for fct in functions]

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
z3py_decls = {}
for var in all_variables:
    z3py_decls[var] = Var(var, fgsort)

# get list of constructors for datatype
def getConstructors(datatype):
    ctor_start_index = datatype.index('(')
    fgsort = datatype[:ctor_start_index].strip()
    ctors = []
    index = ctor_start_index
    while index < len(datatype):
        ctor_end_index = getIndex(datatype, index)
        ctor = datatype[index+1:ctor_end_index].strip()
        ctors += [ ctor ]
        if '(' in datatype[ctor_end_index+1:]:
            index = datatype.index('(', ctor_end_index + 1)
        else:
            index = len(datatype)
    return ctors

sort_map = { 'Int': intsort, 'Bool': boolsort }

# get Z3Py functions from a constructor (both ctors/dtors)
def getZ3PyFunctionsConstructor(constructor):
    z3py_functions = {}
    if not '(' in constructor:
        z3py_functions[constructor] = Const(constructor, fgsort)
    else:
        arg_index = constructor.index('(')
        ctor_name = constructor[:arg_index].strip()
        args_string = constructor[arg_index:].strip()
        args = args_string.split('(')[1:]
        args = [ arg.strip()[:-1].strip() for arg in args ]
        z3py_ctor_args = [ sort_map[i] if i in sort_map else fgsort for i in args ]
        z3py_functions[ctor_name] = Function(ctor_name, *z3py_ctor_args, fgsort)
        for arg in args:
            arg_name = arg.split()[0].strip()
            arg_sort = arg.split()[1].strip()
            # TODO: also assumed unary
            z3py_functions[arg_name] = Function(arg_name, fgsort, fgsort)
    return z3py_functions

constructors = getConstructors(fg_datatype)
for ctor in constructors:
    z3py_decls.update(getZ3PyFunctionsConstructor(ctor))

# get Z3Py functions from a function
def getZ3PyFunctionsFunction(function):
    z3py_functions = {}
    if not '(' in function:
        z3py_functions[function] = Const(function, fgsort)
    else:
        arg_index_start = function.index('(')
        arg_index_end = getIndex(function, arg_index_start)
        fct_name = function[:arg_index_start].strip()
        args_sorts = function[arg_index_start+1:arg_index_end].strip().split()
        ret_sort = function[arg_index_end+1:].strip()
        sorts = args_sorts + [ ret_sort ]
        z3py_fct_args = [ sort_map[sort] if sort in sort_map else fgsort for sort in sorts ]
        z3py_functions[fct_name] = Function(fct_name, *z3py_fct_args)
    return z3py_functions

for fct in functions:
    z3py_decls.update(getZ3PyFunctionsFunction(fct))

# convert body into z3Py formulas
z3py_axioms = []
for ax in axioms:
    body = getBody(ax)
    z3py_ax = parse_smt2_string(body, decls=z3py_decls)
    z3py_axioms += z3py_ax

print(z3py_axioms)
