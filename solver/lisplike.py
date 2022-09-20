"""
Module containing general utilities for handling lisp-like data. This is the primary form of representation in the 
SMT-Lib 2.6 format that specifies the input format of files given to a SMT solvers.  

In particular this implementations handles strings where utterances are separated by 
whitespaces and applications are grouped by parentheses. At the level of abstraction provided by this module, 
utterances are themselves simply strings with no additional semantic annotations. The grammar describing such 
'lisp-like' expressions (LL_EXP) is:  

LL_EXP -> (LL_EXP LL_EXP LL_EXP .... LL_EXP)  
LL_EXP -> UTTERANCE  
LL_EXP -> WHITESPACE LL_EXP WHITESPACE  
UTTERANCE -> string  
WHITESPACE -> any of {'\n', ' ', '\t'}  

This module provides a cohesive representation for reading in such lisp-like strings as nested lists of utterances 
(strings), referred to in the code as 'lisplike_repr'. It also provides functions to perform the parsing of 
strings into the repr, as well as other miscellaneous utilities like pretty printers.  
"""

# TODO (low): give helpful error messages from parser about parentheses
# TODO (low): integrate/replace parser with official sygus parser


class NotLispLikeStringException(Exception):
    """
    This exception is raised when a string is expected to be lisp-like (able to be parsed into a lisp-like repr), 
    but is not.  
    """
    pass


class NotLispLikeReprException(Exception):
    """
    This exception is raised when a value is not a lisp-like repr. A lisp-like repr is either a string (utterance)
    or a list of lisp-like repr (application expressions).  
    """
    pass


def is_lisplike(value):
    """
    Checking whether a value is a lisp-like representation.  
    :param value: any  
    :return: bool  
    """
    if isinstance(value, str):
        return True
    if isinstance(value, list):
        return all(is_lisplike(v) for v in value)
    else:
        return False


def parse(input_str, noerr=False):
    """
    Basic lisp-like parser.  
    Setting the noerr argument does not raise an exception, instead behaves like a best-effort parser.  
    :param input_str: string  
    :param noerr: bool  
    :return: is_lisplike (nested list of strings)  
    """
    # Preprocess: remove arbitrary whitespaces and replace with single space
    processed_str = ' '.join(input_str.split())
    # Call a nested list parser that returns nested list of strings
    [lisplike_repr], pos = _parse_aux(processed_str, noerr, len(processed_str))
    # The last parsed position must be the last position
    if pos != len(processed_str) - 1 and not noerr:
        raise NotLispLikeStringException('Input is not lisp-like. Could not parse {}'.format(processed_str[pos + 1:]))
    return lisplike_repr


def _parse_aux(in_str, noerr, end, begin=0):
    """
    Simple function to parse lisp-like strings where the delimiters are single spaces.  
    The function returns a 'partially' parsed nested list and an integer, where the integer denotes the position 
    in the input string until which the partial parsing was done. The nested list of strings is such that 
    the leaves are utterances and applications are written as lists of utterances or other lists.  

    Setting the noerr argument does not raise an exception, instead behaves like a best-effort parser.  

    :param in_str: string  
    :param noerr: bool  
    :param end: int (ending position until which the parsing must be done)  
    :param begin: int (the starting position from which the parsing must begin)  
    :return: (nested list of strings, int)  
    """
    # TODO (high): replace this function with an iterative implementation or a library call.
    utterance_accumulator = ''
    partial_result = []
    # Loop character-by-character and recurse when parentheses are opened.
    curr = begin
    while curr < end:
        c = in_str[curr]
        if c == ')':
            # End parsing and pop up the recursion level
            if utterance_accumulator != '':
                partial_result.append(utterance_accumulator)
            return partial_result, curr
        elif c == '(':
            # Recursive call
            # Recursive call can only be made if there are no utterances to be parsed at this point
            if utterance_accumulator != '' and not noerr:
                raise NotLispLikeStringException('Input is not lisp-like. Utterance {} '
                                                 'is not part of any expression.'.format(utterance_accumulator))
            partial_repr, partial_pos = _parse_aux(in_str, noerr, end=end, begin=curr+1)
            partial_result.append(partial_repr)
            # Update curr to last parsed position, which is partial_pos
            curr = partial_pos
            # If recursion has ended at topmost level, simply return the result.
            # This prevents from parsing multiple concatenated lisp-like strings, instead parsing only the first one.
            # At topmost level, begin = 0
            if begin == 0:
                return partial_result, curr
        elif c == ' ':
            # Start new utterance if one already exists in the accumulator
            if utterance_accumulator != '':
                partial_result.append(utterance_accumulator)
            utterance_accumulator = ''
        else:
            utterance_accumulator = utterance_accumulator + c

        # Advance curr by one 
        curr = curr + 1
    # Function should not reach this point at the topmost level.
    # If so, there are likely unmatched parentheses or no parentheses.
    return partial_result, curr


def pretty_string(expr, noindent=False):
    """
    Pretty printer to output lisp-like strings from a nested list of utterances.  
    Specifying 'noindent' will yield a string that is only delimited by spaces, rather than tabs or newlines.  
    :param expr: is_lisplike  
    :param noindent: bool  
    :return: string  
    """
    if not is_lisplike(expr):
        raise NotLispLikeReprException('Given value is not a lisp-like representation.')
    # TODO (medium): Ensure each line does not exceed a certain length.
    # Hack around pretty printer for controlling indentation explicitly
    # Can only be done when noindent is True
    if noindent:
        # Replace all existing '\n' with a special symbol
        expr = substitute(expr, [('\n', '<newline>')])
    result = _pretty_string_aux(expr, noindent)
    # Hack around pretty printer for controlling indentation explicitly
    # Can only be done when noindent is True
    if noindent:
        # Replace all '<newline>' with '\n'
        result = result.replace('<newline>', '\n')
    return result


def _pretty_string_aux(lisplike_repr, noindent, align=0):
    if not lisplike_repr:
        # Degenerate case. Not an application, not an utterance. Empty expression.
        return '()'
    if isinstance(lisplike_repr, str):
        # Base case: single utterance. Just return the string, respecting alignment.
        result = ' ' * align + lisplike_repr
        return result
    # Open parentheses, respecting column alignment
    result = ' ' * align + '('
    operator, *operands = lisplike_repr
    operator_str = operator
    if isinstance(operator, list):
        # Directive or declaration. Switch off indentation for the entire expression.
        noindent = True
        operator_str = _pretty_string_aux(operator, noindent, align)
    # Print operator on the same line and the move to a new line for the operands
    result = result + operator_str + '\n'
    # Print operand strings aligned after the operator
    new_align = align + len(operator_str) + 1
    pretty_operand_strings = [_pretty_string_aux(operand, noindent, new_align) for operand in operands]
    for pretty_operand_string in pretty_operand_strings:
        result = result + pretty_operand_string + '\n'
    # Close parentheses, respecting original alignment
    result = result + ' ' * align + ')'
    # If noindent is true, strip all whitespaces and replace with a single space, respecting alignment.
    if noindent:
        # result = ' ' * align + ' '.join(result.split())
        result = ' ' * align + ' '.join(result[:-1].split()) + ')'
    return result


# Additional utilities for denoting a 'lisp-like' string or nested list
def is_lisplike_string(input_str):
    """
    Checking whether a given string is lisp-like.  
    :param input_str: string  
    :return: bool  
    """
    # Parser must be able to parse without raising any exception
    try:
        lisplike_repr = parse(input_str, noerr=False)
    except NotLispLikeStringException:
        lisplike_repr = None
    return lisplike_repr is not None


# Almost surely obsolete. Delete in future versions
# def is_subexpr_string(subexpr_string, expr_string):
#     """
#     Check if the first argument is a sub-expression of the second. The expressions are given 
#     as strings.  
#     :param subexpr_string: string  
#     :param expr_string: string  
#     :return: bool  
#     """
#     if not is_lisplike_string(subexpr_string):
#         raise ValueError('The arguments need to be a lisp-like string: check first argument.')
#     elif not is_lisplike_string(expr_string):
#         raise ValueError('The arguments need to be a lisp-like string: check second argument.')
#     return subexpr_string in expr_string


def count_subexpr(subexpr_repr, expr_repr):
    """
    Count the number of times the first argument occurs as a sub-expression of the second.  
    :param subexpr_repr: is_lisplike  
    :param expr_repr: is_lisplike  
    :return: bool  
    """
    if not is_lisplike(subexpr_repr):
        raise NotLispLikeReprException('The arguments need to be a lisp-like representation: check first argument.')
    elif not is_lisplike(expr_repr):
        raise NotLispLikeReprException('The arguments need to be a lisp-like representation: check second argument.')
    return _count_subexpr_aux(subexpr_repr, expr_repr)


def _count_subexpr_aux(subexpr_repr, expr_repr):
    # Check if it is already equal to the expression
    count = 1 if subexpr_repr == expr_repr else 0
    if isinstance(expr_repr, list):
        # If the expression is an application (rather than a string which is an utterance), then 
        # check for the number of occurrences among all its sub-expressions as well.
        count = count + sum(_count_subexpr_aux(subexpr_repr, e) for e in expr_repr)
    return count


def is_subexpr(subexpr_repr, expr_repr):
    """
    Check if the first argument is a sub-expression of the second.  
    :param subexpr_repr: is_lisplike  
    :param expr_repr: is_lisplike  
    :return: bool  
    """
    return count_subexpr(subexpr_repr, expr_repr) != 0


def less_than(repr1, repr2):
    """
    Custom less-than for lisp-like representation. Utterances are smaller than application expressions, and all other 
    orderings are fixed but arbitrary.  
    :param repr1: is_lisplike  
    :param repr2: is_lisplike  
    :return: bool  
    """
    if not is_lisplike(repr1):
        raise NotLispLikeReprException('The arguments need to be a lisp-like representation: check first argument.')
    elif not is_lisplike(repr2):
        raise NotLispLikeReprException('The arguments need to be a lisp-like representation: check second argument.')

    if isinstance(repr1, str):
        if isinstance(repr2, list):
            # Strings are less than lists
            return True
        else:
            # Both strings; use built-in comparison
            return repr1 < repr2
    else:
        if isinstance(repr2, list):
            # Both lists; imitate built-in comparison for lists by comparing elementwise
            i = 0
            max_ind = min(len(repr1), len(repr2))
            while i < max_ind:
                if less_than(repr1[i], repr2[i]):
                    return True
                elif less_than(repr2[i], repr1[i]):
                    return False
                else:
                    i += 1
            # One list is an 'initial segment' of the other
            # So repr1 is less than repr2 iff repr1 is strictly shorter
            return len(repr1) < len(repr2)
        else:
            # Lists are not less than strings
            return False


# TODO (medium): write substitute by calling transform instead
def substitute(expr, subst_pairs):
    """
    Perform a substitution in the given expression with given substitution pairs. Each pair (present, replacement) 
    is such that if the 'present' occurs as a subexpression, it will be replaced with 'replacement'.  
    The substitutions are performed top-down on the expression, and the first matching substitution is applied.  
    :param expr: is_lisplike  
    :param subst_pairs: list of (is_lisplike, is_lisplike)  
    :return: is_lisplike  
    """
    if not is_lisplike(expr):
        raise NotLispLikeReprException('Given expression is not lisp-like.')
    else:
        for (present, replacement) in subst_pairs:
            if not is_lisplike(present) or not is_lisplike(replacement):
                raise NotLispLikeReprException('Substitution pairs must contain lisp-like representations.')
    return _substitute_aux(expr, subst_pairs)


def _substitute_aux(expr, subst_pairs):
    # Perform substitution if any pairs match
    for (if_present, replacement) in subst_pairs:
        if if_present == expr:
            return replacement
    # None of the substitution pairs match. Apply substitutions recursively if possible.
    if isinstance(expr, list):
        # Substitute recursively
        subst_expr_rec = [_substitute_aux(subexpr, subst_pairs) for subexpr in expr]
        return subst_expr_rec
    else:
        # expr is a string: no recursion. The result is the expression itself.
        return expr


# TODO (low): generalise to be able to choose other expression traversal orders
def transform(expr, transform_pairs, traversal_order='preorder'):
    """
    Perform a transformation of the given expression.  
    Preorder traversal: attempt transforming the expression as a whole before attempting transformation of 
    subexpressions from left to right.  
    Postorder traversal: transform subexpressions from left to right and transform the expression as a whole after.  
    Inorder traversal of an expression does not have a use case at this point and is not supported.  

    Each transform pair (cond, op) will contain functions that, respectively, indicate when a transformation should 
    be applied and what the transformation will be. The first pair that 'matches' is the one that is applied.  
    :param expr: is_lisplike  
    :param transform_pairs: list of (function: is_lisplike -> bool, function: is_lisplike -> is_lisplike)  
    :param traversal_order: string  
    :return: is_lisplike  
    """
    if not is_lisplike(expr):
        raise NotLispLikeReprException('Given expression is not lisp-like.')
    if traversal_order not in {'preorder', 'postorder'}:
        raise ValueError('Traversal order has to be either \'preorder\' (default) or \'postorder\'.')
    transformed_expr = _transform_aux(expr, transform_pairs, traversal_order)
    if not is_lisplike(transformed_expr):
        raise NotLispLikeReprException('Could not transform given expression into a lisp-like expression. '
                                       'Check that the transformation pairs have the expected input/output types.')
    return transformed_expr


def _transform_aux(expr, transform_pairs, traversal_order):
    # TODO (low): must find a way to inexpensively check that the results of transformations are also lisplike
    # For preorder traversal, attempt to transform the entire expression first
    if traversal_order == 'preorder':
        # Apply transformations if any match on the entire expression
        for (cond, op) in transform_pairs:
            if cond(expr):
                return op(expr)
    # Transform recursively, regardless of traversal order
    if isinstance(expr, list):
        # Apply transformations recursively from the first subexpression to the last
        transform_expr_rec = []
        for subexpr in expr:
            transform_expr_rec.append(_transform_aux(subexpr, transform_pairs, traversal_order))
    else:
        # expr is a string: no recursive transformation
        transform_expr_rec = expr
    # For postorder traversal, attempt to transform the entire expression once before returning
    if traversal_order == 'postorder':
        for (cond, op) in transform_pairs:
            if cond(transform_expr_rec):
                return op(transform_expr_rec)
    else:
        # Not postorder traversal. Return recursively transformed expression
        return transform_expr_rec
