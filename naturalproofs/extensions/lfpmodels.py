# import z3
from z3 import *
import itertools

from naturalproofs.uct import fgsort
from naturalproofs.decl_api import get_vocabulary, get_uct_signature, get_recursive_definition, get_all_axioms
from naturalproofs.utils import apply_bound_formula
from naturalproofs.prover_utils import instantiate, make_recdef_unfoldings

from naturalproofs.extensions.finitemodel import FiniteModel


def rank_fcts():
    x, y, nil = Ints('x y nil')
    nxt = Function('nxt', IntSort(), IntSort())
    lft = Function('lft', IntSort(), IntSort())
    rht = Function('rht', IntSort(), IntSort())
    submin = Function('submin', IntSort(), IntSort())
    submax = Function('submax', IntSort(), IntSort())

    # List
    lst = Function('lst', IntSort(), BoolSort())
    lst_rank = Function('lst_rank', IntSort(), IntSort())
    lst_def_body = And(Or(x == nil, lst(nxt(x))) == lst(x),
                       Or(x == nil, lst(nxt(x)) == (lst_rank(nxt(x)) < lst_rank(x))))

    # List segment
    lseg = Function('lseg', IntSort(), IntSort(), BoolSort())
    lseg_rank = Function('lseg_rank', IntSort(), IntSort(), IntSort())
    lseg_def_body = And(Or(x == y, lseg(nxt(x), y)) == lseg(x, y),
                        Or(x == y, lseg(nxt(x), y) == (lseg_rank(nxt(x), y) < lseg_rank(x, y))))

    # Binary tree
    btree = Function('btree', IntSort(), BoolSort())
    btree_rank = Function('btree_rank', IntSort(), IntSort())
    btree_def_body = And(Or(x == nil, And(btree(lft(x)), btree(rht(x))) == btree(x)),
                         Or(x == nil, And(btree(lft(x)) == (btree_rank(lft(x)) < btree_rank(x)),
                                          btree(rht(x)) == (btree_rank(rht(x)) < btree_rank(x)))))
    
    # Binary search tree
    bstree = Function('bstree', IntSort(), BoolSort())
    bstree_rank = Function('bstree_rank', IntSort(), IntSort())
    lft_sort = Or(lft(x) == nil, And(bstree(lft(x)),
                                     submax(lft(x)) < x,
                                     submin(lft(x)) == submin(x)))
    cen_sort = And((lft(x) == nil) == (submin(x) == x),
                   submin(x) <= x, x <= submax(x), btree(x), 
                   (rht(x) == nil) == (submax(x) == x))
    rht_sort = Or(rht(x) == nil, And(bstree(rht(x)),
                                     x < submin(rht(x)), 
                                     submax(rht(x)) == submax(x)))
    bstree_def_body = And(Or(x == nil, And(lft_sort, cen_sort, rht_sort)) == bstree(x),
                          Or(x == nil, And(lft_sort == (bstree_rank(lft(x)) < bstree_rank(x)),
                                           rht_sort == (bstree_rank(rht(x)) < bstree_rank(x)))))
    
    return {
        'lst': ((x,), lst_def_body),
        'lseg': ((x, y,), lseg_def_body),
        'btree': ((x,), btree_def_body),
        'bstree': ((x,), bstree_def_body)
    }


rank_defs_dict = rank_fcts()


def gen_lfp_model(size, annctx, invalid_formula=None):
    """
    Generate a finite model of the theory given by annctx of specified size where the valuation 
    of recursive definitions respects LFP semantics. Returns None if model with specified conditions does not exist.  
    Optional argument invalid_formula is a bound formula that must be falsified by the returned model.  
    :param size: int  
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext  
    :param invalid_formula: pair (tuple of z3.ExprRef, z3.BoolRef)  
    :return: pair (z3.ModelRef, set)  
    """
    # Establish underlying universe
    universe = {z3.IntVal(i) for i in range(size)}
    constraints = []

    vocabulary = get_vocabulary(annctx=annctx)
    # Closure for vocabluary that is over the foreground sort
    # If signature guidelines follow naturalproofs.uct then range can only be fgsort if the domain args are all fgsort
    foreground_vocabluary = {funcdecl for funcdecl in vocabulary
                             if all(srt == fgsort for srt in get_uct_signature(funcdecl, annctx=annctx))}
    for funcdecl in foreground_vocabluary:
        argslist = itertools.product(universe, repeat=funcdecl.arity())
        constraints.append(And([Or([funcdecl(*args) == elem for elem in universe]) for args in argslist]))

    # Recursive definitions and ranks
    recdefs = get_recursive_definition(None, alldefs=True, annctx=annctx)
    recdef_unfoldings = make_recdef_unfoldings(recdefs)
    rank_formulas = {recdef.name(): rank_defs_dict.get(recdef.name(), None) for recdef, _, _ in recdefs}
    if any(value is None for value in rank_formulas.values()):
        raise Exception('Rank definitions not given for: {}'
                        .format(', '.join(key for key, value in rank_formulas.items() if value is None)))
    # Axioms
    axioms = get_all_axioms(annctx=annctx)
    structural_constraints = recdef_unfoldings | set(rank_formulas.values()) | axioms
    constraints.extend(instantiate(structural_constraints, universe))

    # Bound formula to negate
    if invalid_formula is not None:
        formal_vars, body = invalid_formula
        constraints.append(Or([Not(apply_bound_formula(invalid_formula, args))
                               for args in itertools.product(universe, repeat=len(formal_vars))]))
    sol = z3.Solver()
    sol.add(constraints)
    if sol.check() == z3.sat:
        lfp_model = sol.model()
        # Project model onto the numbers corresponding to the foreground universe 
        finite_lfp_model = FiniteModel(lfp_model, universe, annctx=annctx)
        return finite_lfp_model
    else:
        return None
