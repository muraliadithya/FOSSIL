# run `python3 translate.py goal1.smt2` to test

from z3 import *

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
print('axioms: ' + str(axioms))
print('goal: ' + str(goal))

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

print('datatypes: ' + str(datatypes))
print('axioms: ' + str(axioms))
