from counterexample_utils import *
from z3 import *
import re

def counterexemplify(lemma_smt, lemma_vars, N, exact=False):
    """
    Generate a counterexample model for a proposed lemma.
    :param lemma_smt: string proposal lemma in SMT-Lib format, variables demarked inside curly braces (e.g. {x})
    :param lemma_vars: list of string variable names appearing in lemma_smt
    :param N: natural number upper bound for model
    :param exact: Bool denoting parameter N as an exact model size (if True) or an upper bound (if False)
    :return: Z3Py model of counterexample
    :return: list of Z3Py variables used to instantiate proposed lemma negation
    """
    neg_lemma, inst_vars = convert_smt_z3(lemma_smt, lemma_vars)
    
    # Initiate z3py variables
    nxt = Function('nxt', IntSort(), IntSort())
    ls = Function('ls', IntSort(), IntSort(), BoolSort())
    rank = Function('rank', IntSort(), IntSort(), IntSort())
    S = Ints(' '.join(['x'+str(i) for i in range(1,N+1)]))
    nil = Int('nil')
    Snil = [nil] + S
    
    # Functions to replace Z3 macros
    def lsrankdec(x, y):
        ls_def = ls(x,y) == Or(x == y, ls(nxt(x), y))
        rank_def = Implies(x != y, ls(nxt(x), y) == (rank(nxt(x), y) < rank(x, y)))
        return And(ls_def, rank_def)

    def lst(x):
        return ls(x, nil)

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
    # Ensure lemma instantiation variables are in underlying set
    instantiate = [Or([v == xi for xi in S]) for v in inst_vars]
    
    s = Solver()
    s.add(intuitive)
    s.add(instantiate)
    s.add(nonneg_ranks)
    s.add(nxt_def)
    s.add(ls_rank_def)
    s.add(neg_lemma)
    
    print(s.check() == CheckSatResult(Z3_L_TRUE))
    return s.model(), inst_vars
    
def convert_smt_z3(lemma, lemma_vars):
    """
    Convert SMT-Lib formatted text to Z3Py object with new variable assignment.
    :param lemma_smt: string proposal lemma in SMT-Lib format, variables demarked inside curly braces (e.g. {x})
    :param lemma_vars: list of string variable names appearing in lemma_smt
    :return: Z3Py object encoding instantiated lemma negation
    :return: list of Z3Py variables used to instantiate proposed lemma negation
    """
    inst_vars = Ints(' '.join(['y_'+str(i+1) for i in range(len(lemma_vars))]))
    rep = {'{'+var+'}': str(inst_vars[i]) for i,var in enumerate(lemma_vars)}
    rep = dict((re.escape(k), v) for k, v in rep.items())
    pattern = re.compile("|".join(rep.keys()))
    lemma_z3 = pattern.sub(lambda m: rep[re.escape(m.group(0))], lemma)
    return parse_smt2_string('(not {})'.format(lemma_z3)), inst_vars