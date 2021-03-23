from z3 import *
from list_signature import *

"""
Print a counterexample model for the "ls(x,y) => lst(x)" lemma, generated using the Z3Py interface.
Specifying -N val in terminal call will specify val as an upper bound for the countexample model without nil (default is 3).
Specifying -exact in terminal call will force val parameter as an exact size for the model (default is upper bound).
"""

# Lemma creation
x,y = Ints('x y')
lemma = Implies(ls(x,y), lst(x))
lemma_vars = [x, y]

# Manage terminal options to specify model
N = int(sys.argv[sys.argv.index('-N')+1]) if '-N' in sys.argv[:-1] else 3
exact = '-exact' in sys.argv

# Generate counterexample
model, elements = counterexemplify(lemma, lemma_vars, N, exact)
if model is not None:
    print(model)
    print(elements)