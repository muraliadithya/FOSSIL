from z3 import *
import itertools


def counterexemplify(lemma, lemma_vars, N, func_def, rank_def, rank, rank_zero, iter_funcs, nil):
    """
    Generate a counterexample model for a proposed lemma in the custom language.
    """
    # Establish underlying set
    S = Ints(' '.join(['x'+str(i) for i in range(1,N+1)]))
    Snil = [nil] + S
    
    # Non-negative ranks
    nonneg_ranks = [rank(args) == 0 if rank_zero(*args) else rank(args) >= 0
                    for args in itertools.product(Snil, repeat=rank.arity())]
    # Ensure underlying set is closed under iteration functions
    nxt_def = [Or([nxt(a) == b for b in Snil]) for a in S
               for nxt in iter_funcs] + [nxt(nil) == nil for nxt in iter_funcs]
    # Enforce definition of list segments and rank
    func_rank_def = [And(func_def(*args), rank_def(*args))
                     for args in itertools.product(Snil, repeat=rank.arity())]
    # Set intuitive interpretations, treating N as upper bound to model size
    intuitive = [And(a <= i, 0 <= a) for i,a in enumerate(Snil)]
    
    s = Solver()
    s.add(nonneg_ranks)
    s.add(nxt_def)
    s.add(func_rank_def)
    s.add(intuitive)
    #s.add(additional_constraints)
    
    # Exclude nil interpretation from variables
    instantiate = [Or([v == xi for xi in S]) for v in lemma_vars]
    s.add(instantiate)
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
