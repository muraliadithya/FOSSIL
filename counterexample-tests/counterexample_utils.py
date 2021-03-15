from z3 import *

def counterexample_engine(s, m_funcs, S, prnt=False):
    """
    Check satisfiability of s, obtain model, then append negation of model to derive all counterexamples.
    :param s: z3py Solver
    :param m_funcs: list of z3py Functions to encode the counterexamples
    :param S: list of z3py variables representing the underlying set (distinct from nil)
    :param prnt: Bool to print each particular counterexample
    :return cexs: list of tuple encodings of counterexamples found
    """
    cexs = []
    N = len(S)
    while s.check().__repr__() == 'sat':
        # Obtain satisfying model and encode as the image of nxt on S
        m = s.model()
        funcs = [z3_func(m[m_func].as_list()) for m_func in m_funcs]
        cex = [tuple(f(i) for i in range(1,N+1)) for f in funcs]
        cexs.append(cex)
        if prnt:
            print(cex)
        # Append negation of nxt model (counterexample to proposed lemma)
        s.add(Not(And([m_func(a) == cex[j][i] for j,m_func in enumerate(m_funcs) for i,a in enumerate(S)])))
    return cexs

def z3_func(f):
    """
    Convert z3py FuncInterp object to a Python function.
    :param f: z3py model function interpretation as a list
    :return: Python function representation of f
    """
    func = {}
    for x,fx in f[:-1]:
        func[x.as_string()] = fx.as_long()
    func['-1'] = f[-1].as_long()
    return lambda x : func[str(x)] if str(x) in func else func['-1']