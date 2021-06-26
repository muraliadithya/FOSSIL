# import z3
from z3 import *
import itertools

from naturalproofs.uct import fgsort, intsort, boolsort, min_intsort, max_intsort
from naturalproofs.decl_api import get_vocabulary, get_uct_signature, get_recursive_definition, get_all_axioms
from naturalproofs.utils import apply_bound_formula
from naturalproofs.prover_utils import instantiate, make_recdef_unfoldings

from naturalproofs.extensions.finitemodel import FiniteModel


def rank_fcts():
    x, y, nil = Ints('x y nil')

    # List
    nxt = Function('nxt', fgsort, intsort)
    lst = Function('lst', fgsort, boolsort)
    lst_rank = Function('lst_rank', fgsort, intsort)
    lst_recdef = lst(x) == If(x == nil, True, lst(nxt(x)))
    lst_rankdef = If(x == nil, lst_rank(x) == 0,
                               lst(x) == (lst_rank(nxt(x)) < lst_rank(x)))
    lst_def_body = And(lst_recdef, lst_rankdef)

    # List segment
    lseg = Function('lseg', fgsort, fgsort, boolsort)
    lseg_rank = Function('lseg_rank', fgsort, fgsort, intsort)
    lseg_recdef = lseg(x, y) == If(x == y, True,
                                           If(x == nil, False,
                                                        lseg(nxt(x), y)))
    lseg_rankdef = If(x == y, lseg_rank(x, y) == 0,
                              If(x == nil, True,
                                           lseg(x, y) == (lseg_rank(nxt(x), y) < lseg_rank(x, y))))
    lseg_def_body = And(lseg_recdef, lseg_rankdef)

    # Binary tree
    lft = Function('lft', fgsort, intsort)
    rght = Function('rght', fgsort, intsort)
    tree = Function('tree', fgsort, boolsort)
    tree_rank = Function('tree_rank', fgsort, intsort)
    tree_recdef = tree(x) == If(x == nil, True,
                                          And(tree(lft(x)), tree(rght(x))))
    tree_rankdef = If(x == nil, tree_rank(x) == 0,
                                tree(x) == And(tree_rank(lft(x)) < tree_rank(x),
                                               tree_rank(rght(x)) < tree_rank(x)))
    tree_def_body = And(tree_recdef, tree_rankdef)

    # Binary search tree
    minr = Function('minr', fgsort, intsort)
    maxr = Function('maxr', fgsort, intsort)
    minr_recdef = If(x == nil, 100, min_intsort(key(x), minr(lft(x)), minr(rght(x))))
    maxr_recdef = If(x == nil, -1, max_intsort(key(x), maxr(lft(x)), maxr(rght(x)))))
    key = Function('key', fgsort, intsort)
    bst = Function('bst', fgsort, boolsort)
    bst_rank = Function('bst_rank', fgsort, intsort)
    bst_recdef = bst(x) == If(x == nil, True,
                                        And(0 < key(x), key(x) < 100,
                                            bst(lft(x)), bst(rht(x)),
                                            maxr(lft(x)) <= key(x),
                                            key(x) <= minr(rght(x))))
    bst_rankdef = If(x == nil, bst_rank(x) == 0,
                               bst(x) == And(bst_rank(lft(x)) < bst_rank(x),
                                             bst_rank(rght(x)) < bst_rank(x)))
    bst_def_body = And(minr_recdef, maxr_recdef, bst_recdef, bst_rankdef)

    # Cyclic
    cyclic = Function('cyclic', fgsort, boolsort)
    cyclic_rank = Function('cyclic_rank', fgsort, intsort)
    cyclic_recdef = cyclic(x) == If(x == nil, False,
                                              lseg(nxt(x), x))
    cyclic_rankdef = If(x == nil, True,
                                  cyclic(x) == And(lseg_rank(nxt(x), x) < cyclic_rank(x),
                                                   cyclic_rank(nxt(x)) == cyclic_rank(x)))
    cyclic_def_body = And(cyclic_recdef, cyclic_rankdef)

    return {
        'lst': ((x,), lst_def_body),
        'lseg': ((x, y,), lseg_def_body),
        'tree': ((x,), tree_def_body),
        'bst': ((x,), bst_def_body),
        'cyclic': ((x,), cyclic_def_body)
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
