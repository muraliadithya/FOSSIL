from z3 import *
from counterexample_utils import *
import sys

"""
Return the set of counterexamples for "ts(x,y) => tree(x)" lemma.
These are generated using the z3Py interface and are unique up to isomorphism given any particular choice of
instantiation for the negated lemma.
Specifiying -N val in terminal call will enact an underlying set with val-many elements distinct from nil.
Specifying -p will print the particular counterexamples.
"""

# Functions to replace Z3 macros
def tsrankdec(x, y):
    ts_def = ts(x,y) == Or(x == y, ts(lft(x), y), ts(rht(x), y))
    rank_def = Implies(x != y, And(ts(lft(x), y) == (rank(lft(x), y) < rank(x, y)),
                                   ts(rht(x), y) == (rank(rht(x), y) < rank(x, y))))
    return And(ts_def, rank_def)

def tree(x):
    return And(ts(x, nil), ts(lft(x), nil), ts(rht(x), nil))


# Manage terminal options
N = int(sys.argv[sys.argv.index('-N')+1]) if '-N' in sys.argv[:-1] else 3
prnt = '-p' in sys.argv

# Initiate z3py variables
lft = Function('lft', IntSort(), IntSort())
rht = Function('rht', IntSort(), IntSort())
ts = Function('ts', IntSort(), IntSort(), BoolSort())
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
# Ensure lft, rht functions have range in the underlying set
lft_def = [Or([lft(a) == b for b in Snil]) for a in S] + [lft(nil) == nil]
rht_def = [Or([rht(a) == b for b in Snil]) for a in S] + [rht(nil) == nil]
# Ensure ts is well-defined and rank monotonically decreases along nxt (under assumption of ts)
ts_rank_def = [tsrankdec(a, b) for a in Snil for b in Snil]
# Force the intuitive interpretations, without loss of generality: nil as 0, x1 as 1, x2 as 2, etc.
intuitive = [a == i for i,a in enumerate(Snil)]

# Assert the negation of proposed lemma to generate counterexample models
y = Snil[2] if N > 1 else Snil[1]
neg_lemma = [
    ts(Snil[1], y),
    Not(tree(Snil[1]))
]

# Initiate solver and add assertions
s = Solver()
s.add(distinctions)
s.add(intuitive)
s.add(nonneg_ranks)
s.add(lft_def)
s.add(rht_def)
s.add(ts_rank_def)
s.add(neg_lemma)

# Generate counterexamples
cexs = counterexample_engine(s, [lft, rht], S, prnt)

print('Found {} counterexample{}.'.format(len(cexs),'s' if len(cexs) != 1 else ''))