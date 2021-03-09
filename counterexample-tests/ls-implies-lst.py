from z3 import *
from counterexample_utils import *
import sys

"""
Return the set of counterexamples for "ls(x) => list(x,y)" lemma.
These are generated using the z3Py interface and are unique up to isomorphism given any particular choice of
instantiation for the negated lemma.
Specifiying --N val in terminal call will enact an underlying set with val-many elements distinct from nil.
Specifying --p will print the particular counterexamples.
"""

# Functions to replace Z3 macros
def lsrankdec(x, y):
    ls_def = ls(x,y) == Or(x == y, ls(nxt(x), y))
    rankdec_def = Implies(x != y, ls(nxt(x), y) == (rank(nxt(x), y) < rank(x, y)))
    return And(ls_def, rankdec_def)

def lst(x):
    return ls(x, nil)


# Manage terminal options
N = int(sys.argv[sys.argv.index('--N')+1]) if '--N' in sys.argv[:-1] else 3
prnt = '--p' in sys.argv

# Initiate z3py variables
nxt = Function('nxt', IntSort(), IntSort())
ls = Function('ls', IntSort(), IntSort(), BoolSort())
rank = Function('rank', IntSort(), IntSort(), IntSort())
S = Ints(' '.join(['x'+str(i) for i in range(1,N+1)]))
nil = Int('nil')
Snil = [nil] + S

# Construct assertion lists
# Ensure distinct variables are interpreted distinctly
distinctions = [a != b for i,a in enumerate(Snil) for j,b in enumerate(Snil) if i != j]
# Ensure rank interpretations are nonnegative, and moreover zero on the diagonal
nonneg_ranks = [rank(a, b) >= 0 if i != j else rank(a, b) == 0
                for i,a in enumerate(Snil) for j,b in enumerate(Snil)]
# Ensure nxt function has range in the underlying set
nxt_def = [Or([nxt(a) == b for b in Snil]) for a in S] + [nxt(nil) == nil]
# Ensure ls is well-defined and rank monotonically decreases along nxt (under assumption of ls)
ls_rank_def = [lsrankdec(a, b) for a in Snil for b in Snil]
# Force the intuitive interpretations, without loss of generality: nil as 0, x1 as 1, x2 as 2, etc.
intuitive = [a == i for i,a in enumerate(Snil)]

# Assert the negation of proposed lemma to generate counterexample models
y = Snil[2] if N > 1 else Snil[1]
neg_lemma = [
    ls(Snil[1], y),
    Not(lst(Snil[1]))
]

# Initiate solver and add assertions
s = Solver()
s.add(distinctions)
s.add(intuitive)
s.add(nonneg_ranks)
s.add(nxt_def)
s.add(ls_rank_def)
s.add(neg_lemma)

# Generate counterexamples
cexs = counterexample_engine(s, nxt, S, prnt)

print('Found {} counterexample{}.'.format(len(cexs),'s' if len(cexs) != 1 else ''))