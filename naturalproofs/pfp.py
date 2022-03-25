# This module contains functions for creating and manipulating inductive claims.
# In the current implementation, the choice of induction template is that of pre-fixpoints.

import z3

from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.uct import is_expr_fg_sort
from naturalproofs.decl_api import get_recursive_definition
from naturalproofs.utils import transform_expression


def make_pfp_formula(formula, is_strong_induction=True, annctx=default_annctx):
    """
    Construct the 'pre-fixpoint' formula of the given expression. If this pfp formula holds, then the given formula
    holds with least-fixpoint semantics. The formula is almost always of the form recdef => pformula, where recdef is a
    recursively defined function and pformula is any formula.  
    :param formula: z3.BoolRef  
    :param is_strong_induction: bool  
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext  
    :return:z3.BoolRef  
    """
    if not isinstance(formula, z3.BoolRef):
        raise TypeError('BoolRef expected. Given expression is not a formula.')
    try:
        # Supported formulae are of the form Op(recdef(arg-variables), formula)
        # Typically the Op is an implication
        topmost_operator = formula.decl()
        left_side, right_side = formula.children()
        recdef = left_side.decl()
        arity = recdef.arity()
        recdef_arglist = left_side.children()
    except Exception:
        raise TypeError('Cannot make PFP formula. Given formula does not fit expected format.')
    # Supported formulae can only have simple variables as arguments to the recursively defined function.
    if not all([arg.decl().arity() == 0 for arg in recdef_arglist]):
        raise TypeError('Cannot make PFP formula. Given formula does not fit expected format.')
    lhs_sort = get_uct_sort(left_side, annctx)
    if lhs_sort is None:
        raise ValueError('Untracked declaration {}. Cannot make PFP formula.'.format(left_side.decl()))
    # The topmost operator of the given formula should be the less_than operator corresponding to the lattice over the
    # uct sort of the left hand side.
    lessequals_operator = lhs_sort.get_lattice_lessequals_operator()
    if lessequals_operator != topmost_operator:
        raise TypeError('Cannot make PFP formula. Given formula does not fit expected format.')
    recursive_definition = get_recursive_definition(recdef, annctx=annctx)
    if recursive_definition is None:
        raise TypeError('Untracked recursive definition. Add definition using naturalproofs.decl_api.AddRecDefinition')
    _, formal_params, body = recursive_definition
    # Express body of recursive definition in terms of variables in given formula, i.e., recdef_arglist
    induction_structure = z3.substitute(body, [(formal_params[i], recdef_arglist[i]) for i in range(arity)])
    # Substitute recdef with right_side in induction_structure
    if_recdef = lambda x: x.decl() == recdef
    inductive_hypothesis = z3.And(right_side, left_side) if is_strong_induction else right_side
    subst_op = lambda x: z3.substitute(inductive_hypothesis, [(recdef_arglist[i], x.arg(i)) for i in range(arity)])
    induction_step = transform_expression(induction_structure, [(if_recdef, subst_op)])
    # pfp property is induction_step of claim is smaller than claim
    induction_claim = lessequals_operator(induction_step, right_side)
    return induction_claim


def make_induction_obligation(formula, ind_var, annctx=default_annctx):
    """
    Construct the obligation expressing the induction proof of the given formula. The induction template is the one
    corresponding to the sort of the induction variable 'ind_var' when it is an ADT sort.
    The only induction obligation currently supported is the standard one with one level of destructor.
    :param formula: z3.BoolRef
    :param ind_var: z3.ExprRef
    :param annctx: naturalproofs.AnnotatedContext.AnnotatedContext
    :return: z3.BoolRef
    """
    if not isinstance(formula, z3.BoolRef):
        raise TypeError('BoolRef expected. Given expression is not a formula.')
    z3sort = ind_var.sort()
    if not isinstance(z3sort, z3.DatatypeSortRef):
        raise TypeError(f'Expected an Algebraic Datatype to induct on, but was given {z3sort}.')
    induction_steps = []
    for i in range(z3sort.num_constructors()):
        ctor = z3sort.constructor(i)
        arity = ctor.arity()
        check = z3sort.recognizer(i)
        if arity == 0:
            ind_step = z3.Implies(check(ind_var), formula)
        else:
            inductive_hypotheses = [z3.substitute(formula, [(ind_var, z3sort.accessor(i, j)(ind_var))])
                                    for j in range(arity) if ctor.domain(j) == z3sort]
            num_hyp = len(inductive_hypotheses)
            if num_hyp == 0:
                raise ValueError(f'Cannot handle constructors with no arguments from sort {z3sort.name()}.')
            inductive_hypothesis = z3.And(inductive_hypotheses) if num_hyp != 1 else inductive_hypotheses[0]
            ind_step = z3.Implies(check(ind_var), z3.Implies(inductive_hypothesis, formula))
        induction_steps.append(ind_step)
    return z3.And(induction_steps)
