# import z3
from z3 import *
import itertools

from naturalproofs.decl_api import get_vocabulary, get_uct_signature, get_recursive_definition, get_all_axioms
from naturalproofs.utils import apply_bound_formula
from naturalproofs.prover_utils import instantiate, make_recdef_unfoldings

from naturalproofs.extensions.finitemodel import FiniteModel


def rank_fcts():
    x, y, nil = Ints('x y nil')

    # List
    nxt = Function('nxt', IntSort(), IntSort())
    lst = Function('lst', IntSort(), BoolSort())
    lst_rank = Function('lst_rank', IntSort(), IntSort())
    lst_recdef = lst(x) == If(x == nil, True, lst(nxt(x)))
    lst_rankdef = If(x == nil, True, lst(x) == (lst_rank(nxt(x)) < lst_rank(x)))
    lst_def_body = And(lst_recdef, lst_rankdef)

    # List segment
    lseg = Function('lseg', IntSort(), IntSort(), BoolSort())
    lseg_rank = Function('lseg_rank', IntSort(), IntSort(), IntSort())
    lseg_recdef = lseg(x, y) == If(x == y, True,
                                           If(x == nil, False,
                                                        lseg(nxt(x), y)))
    lseg_rankdef = If(Or(x == y, x == nil), True, lseg(x, y) == (lseg_rank(nxt(x), y) < lseg_rank(x, y)))
    lseg_def_body = And(lseg_recdef, lseg_rankdef)

    # Binary tree
    lft = Function('lft', IntSort(), IntSort())
    rght = Function('rght', IntSort(), IntSort())
    tree = Function('tree', IntSort(), BoolSort())
    tree_rank = Function('tree_rank', IntSort(), IntSort())
    tree_recdef = tree(x) == If(x == nil, True,
                                          And(tree(lft(x)), tree(rght(x))))
    tree_rankdef = If(x == nil, True, tree(x) == And(tree_rank(lft(x)) < tree_rank(x),
                                                     tree_rank(rght(x)) < tree_rank(x)))
    tree_def_body = And(tree_recdef, tree_rankdef)

    # Binary search tree
    minr = Function('minr', IntSort(), IntSort())
    maxr = Function('maxr', IntSort(), IntSort())
    key = Function('key', IntSort(), IntSort())
    minr_recdef = If(x == nil, minr(x) == 100,
                     If(And(key(x) <= minr(lft(x)), key(x) <= minr(rght(x))), minr(x) == key(x),
                        If(minr(lft(x)) <= minr(rght(x)), minr(x) == minr(lft(x)),
                                                          minr(x) == minr(rght(x)))))
    maxr_recdef = If(x == nil, maxr(x) == -1,
                     If(And(key(x) >= maxr(lft(x)), key(x) >= maxr(rght(x))), maxr(x) == key(x),
                        If(maxr(lft(x)) >= maxr(rght(x)), maxr(x) == maxr(lft(x)),
                                                          maxr(x) == maxr(rght(x)))))
    bst = Function('bst', IntSort(), BoolSort())
    bst_rank = Function('bst_rank', IntSort(), IntSort())
    bst_recdef = bst(x) == If(x == nil, True,
                                        And(0 < key(x), key(x) < 100,
                                            bst(lft(x)), bst(rght(x)),
                                            maxr(lft(x)) <= key(x),
                                            key(x) <= minr(rght(x))))
    bst_rankdef = If(x == nil, True, bst(x) == And(bst_rank(lft(x)) < bst_rank(x),
                                                   bst_rank(rght(x)) < bst_rank(x)))
    bst_def_body = And(minr_recdef, maxr_recdef, bst_recdef, bst_rankdef)

    # Cyclic
    cyclic = Function('cyclic', IntSort(), BoolSort())
    cyclic_rank = Function('cyclic_rank', IntSort(), IntSort())
    cyclic_recdef = cyclic(x) == If(x == nil, False,
                                              lseg(nxt(x), x))
    cyclic_rankdef = If(x == nil, True, cyclic(x) == And(lseg_rank(nxt(x), x) < cyclic_rank(x),
                                                         cyclic_rank(nxt(x)) == cyclic_rank(x)))
    cyclic_def_body = And(cyclic_recdef, cyclic_rankdef)

    # Directed acyclic graph
    dag = Function('dag', IntSort(), BoolSort())
    dag_rank = Function('dag_rank', IntSort(), IntSort())
    dag_recdef = dag(x) == If(x == nil, True,
                                        And(dag(lft(x)), dag(rght(x))))
    dag_rankdef = If(x == nil, True, dag(x) == And(dag_rank(lft(x)) < dag_rank(x),
                                                   dag_rank(rght(x)) < dag_rank(x)))
    dag_def_body = And(dag_recdef, dag_rankdef)
    
    # Reachability
    reach = Function('reach', IntSort(), IntSort(), BoolSort())
    reach_rank = Function('reach_rank', IntSort(), IntSort(), IntSort())
    reach_recdef = reach(x, y) == If(x == y, True,
                                             Or(reach(lft(x), y), reach(rght(x), y)))
    reach_rankdef = If(x == y, True,
                               And(reach(lft(x), y) == (reach_rank(lft(x), y) < reach_rank(x, y)),
                                   reach(rght(x), y) == (reach_rank(rght(x), y) < reach_rank(x, y))))
    reach_def_body = And(reach_recdef, reach_rankdef)

    # Directed list
    prv = Function('prv', IntSort(), IntSort())
    dlst = Function('dlst', IntSort(), BoolSort())
    dlst_rank = Function('dlst_rank', IntSort(), IntSort())
    dlst_recdef = dlst(x) == If(Or(x == nil, nxt(x) == nil), True, And(prv(nxt(x)) == x, dlst(nxt(x))))
    dlst_rankdef = If(x == nil, True, dlst(x) == (dlst_rank(nxt(x)) < dlst_rank(x)))
    dlst_def_body = And(dlst_recdef, dlst_rankdef)

    # Even list
    even_lst = Function('even_lst', IntSort(), BoolSort())
    even_lst_rank = Function('even_lst_rank', IntSort(), IntSort())
    even_lst_recdef = even_lst(x) == If(x == nil, True,
                                                  even_lst(nxt(nxt(x))))
    even_lst_rankdef = If(x == nil, True, even_lst(x) == (even_lst_rank(nxt(nxt(x)) < even_lst_rank(x))))
    even_lst_def_body = And(even_lst_recdef, even_lst_rankdef)

    # Odd list
    odd_lst = Function('odd_lst', IntSort(), BoolSort())
    odd_lst_rank = Function('odd_lst_rank', IntSort(), IntSort())
    odd_lst_recdef = odd_lst(x) == If(x == nil, False,
                                                If(nxt(x) == nil, True,
                                                                  odd_lst(nxt(nxt(x)))))
    odd_lst_rankdef = If(nxt(x) == nil, True, odd_lst(x) == (odd_lst_rank(nxt(nxt(x)) < odd_lst_rank(x))))
    odd_lst_def_body = And(odd_lst_recdef, odd_lst_rankdef)

    # Sorted list
    slst = Function('slst', IntSort(), BoolSort())
    slst_rank = Function('slst_rank', IntSort(), IntSort())
    slst_recdef = slst(x) == If(Or(x == nil, nxt(x) == nil), True,
                                                             And(key(x) <= key(nxt(x)),
                                                                 slst(nxt(x))))
    slst_rankdef = If(Or(x == nil, nxt(x) == nil), True,
                                                   slst(x) == (slst_rank(nxt(x)) < slst_rank(x)))
    slst_def_body = And(slst_recdef, slst_rankdef)

    # Sorted list segment
    slseg = Function('slseg', IntSort(), IntSort(), BoolSort())
    slseg_rank = Function('slseg_rank', IntSort(), IntSort(), IntSort())
    slseg_recdef = slseg(x, y) == If(x == y, True,
                                          And(key(x) <= key(nxt(x)),
                                              slseg(nxt(x), y)))
    slseg_rankdef = If(x == y, True, slseg(x, y) == (slseg_rank(nxt(x), y) < slseg_rank(x, y)))
    slseg_def_body = And(slseg_recdef, slseg_rankdef)


    return {
        'lst': ((x,), lst_def_body),
        'lseg': ((x, y,), lseg_def_body),
        'tree': ((x,), tree_def_body),
        'bst': ((x,), bst_def_body),
        'cyclic': ((x,), cyclic_def_body),
        'dag': ((x,), dag_def_body),
        'reach': ((x, y,), reach_def_body),
        'dlst': ((x,), dlst_def_body),
        'even_lst': ((x,), even_lst_def_body),
        'odd_lst': ((x,), odd_lst_def_body),
        'slst': ((x,), slst_def_body),
        'slseg': ((x,), slseg_def_body)
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
