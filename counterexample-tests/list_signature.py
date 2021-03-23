from counterexample_utils import *
from z3 import *


# Initialize signature
ls = Function('ls', IntSort(), IntSort(), BoolSort())
nil = Int('nil')
# Initialize macros representing conservative extension
def lst(x):
    return ls(x, nil)


def counterexemplify(lemma, lemma_vars, N, exact=False, additional_constraints=[]):
    """
    Generate a counterexample model for a proposed lemma in the language of lists.
    :param lemma: Z3Py object encoding proposal lemma
    :param lemma_vars: list of Z3Py variables appearing in lemma_smt; these should not include any 'xi' for i=1,...,N
    :param N: natural number upper bound for model
    :param exact: Bool denoting parameter N as an exact model size (if True) or an upper bound (if False)
    :param additional_constraints: List of Z3Py objects representing additional constraints
    :return: Z3Py model of counterexample
    :return: list of integers comprising underlying set
    """
    # Initialize Z3Py objects
    nxt = Function('nxt', IntSort(), IntSort())
    rank = Function('rank', IntSort(), IntSort(), IntSort())
    S = Ints(' '.join(['x'+str(i) for i in range(1,N+1)]))
    Snil = [nil] + S
    
    # Functions to replace Z3 macros
    def lsrankdec(x, y):
        ls_def = ls(x,y) == Or(x == y, ls(nxt(x), y))
        rank_def = Implies(x != y, ls(nxt(x), y) == (rank(nxt(x), y) < rank(x, y)))
        return And(ls_def, rank_def)

    # Construct assertion lists
    # Ensure rank interpretations are nonnegative, and moreover zero on the diagonal
    nonneg_ranks = [rank(a, b) >= 0 if i != j else rank(a, b) == 0
                    for i,a in enumerate(Snil) for j,b in enumerate(Snil)]
    # Ensure nxt function has range in the underlying set
    nxt_def = [Or([nxt(a) == b for b in Snil]) for a in S] + [nxt(nil) == nil]
    # Ensure ls is well-defined and rank monotonically decreases along nxt (under assumption of ls)
    ls_rank_def = [lsrankdec(a, b) for a in Snil for b in Snil]
    # Bound or force the interpretations
    if exact:
        intuitive = [a == i for i,a in enumerate(Snil)]
    else:
        intuitive = [And(a <= i, 0 <= a) for i,a in enumerate(Snil)]
    # Ensure lemma instantiation variables are in underlying set but not Nil
    instantiate = [Or([v == xi for xi in S]) for v in lemma_vars]
    
    s = Solver()
    s.add(intuitive)
    s.add(instantiate)
    s.add(nonneg_ranks)
    s.add(nxt_def)
    s.add(ls_rank_def)
    s.add(additional_constraints)
    # Constrain with negation of proposed lemma to force counterexample
    s.add(Not(lemma))
    
    if s.check() == CheckSatResult(Z3_L_TRUE):
        cex_model = s.model()
        # Return set of assignments for Snil variables
        elements = {cex_model.eval(v) for v in Snil}
    else:
        cex_model = None
        elements = set()
    
    return cex_model, elements
