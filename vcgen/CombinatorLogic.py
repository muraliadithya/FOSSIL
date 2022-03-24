"""
This module defines a class whose objects instantiate a formula parser given a grammar of atoms
"""

import pyparsing as pp

import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, SetUnion, SetIntersect, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort, get_uct_sort

from vcgen.utils import sort_to_setsort, BadType, LParen, RParen

"""
TODO:
1) Add true and false to formula grammar
"""


class CombinatorLogic:
    """
    This class defines a combinatory logic on top of a term grammar given as input. The incoming term grammar is
    usually one defining a language of applications (variables and functions applied to variables).
    """

    def __init__(self, application_grammar):
        self.Application = application_grammar

        # Nonterminal representing the formula and term parser elements to be instantiated
        Formula = pp.Forward()
        Term = pp.Forward()
        self.Formula = Formula
        self.Term = Term

        # Keywords
        IfKeyword = pp.Literal("If").suppress()
        ThenKeyword = pp.Literal("Then").suppress()
        ElseKeyword = pp.Literal("Else").suppress()

        # Grammar for terms
        IntConstTerm = pp.common.signed_integer
        SetIntConstTerm = pp.Literal("empSetInt")
        SetLocConstTerm = pp.Literal("empSetLoc")
        ConstTerm = SetIntConstTerm ^ SetLocConstTerm ^ IntConstTerm
        # UnTermOp = "singleton"  # constructing a singleton set
        BinTermOp = pp.one_of("+ - * & |")
        # Parse action for TermAtom will be defined automatically defined once the action for each OR piece is defined
        TermAtom = ConstTerm ^ self.Application
        ITETerm = LParen + IfKeyword + Formula + ThenKeyword + Term + ElseKeyword + Term + RParen
        Term <<= TermAtom ^ (LParen + Term + BinTermOp + Term + RParen) ^ ITETerm

        # Interpretation for terms
        # A term is interpreted as a z3.ExprRef. The interpretation functions below return both the interpretation and the
        # uct sort to be used when parsing formulas.
        @IntConstTerm.set_parse_action
        def interpret_int_const(string, loc, tokens):
            return tokens[0], intsort

        @SetLocConstTerm.set_parse_action
        def interpret_empty_locset(string, loc, tokens):
            return fgsetsort.lattice_bottom, fgsetsort

        @SetIntConstTerm.set_parse_action
        def interpret_empty_intset(string, loc, tokens):
            return intsetsort.lattice_bottom, intsetsort

        @ITETerm.set_parse_action
        def interpret_ite_term(string, loc, tokens):
            cond, (then_term, then_sort), (else_term, else_sort) = tokens
            # Check that the expression is well-typed
            if then_sort != else_sort:
                raise BadType(f'Cannot interpret ITE term between arguments of type {then_sort} and {else_sort}',
                              loc, string)
            return If(cond, then_term, else_term), then_sort

        # TODO: This function is highly specific to its productions. Must be rewritten better if grammar is generalized.
        @Term.set_parse_action
        def interpret_term(string, loc, tokens):
            if len(tokens) == 1:
                return tokens[0]
            arg1, binop, arg2 = tokens

            # Check that the arguments are well-typed
            well_typed = None
            arg1_old_sort = arg1[1]
            arg2_old_sort = arg2[1]
            if binop in {'+', '-', '*'}:
                well_typed = arg1[1] == arg2[1] and arg1[1] == intsort
            else:
                # For set union we can consider individual elements as singletons (only one of the arguments)
                if binop == '|':
                    if arg1[1] in {fgsort, intsort}:
                        arg1_new_sort = sort_to_setsort[arg1[1]]
                        arg1 = SetAdd(arg1_new_sort.lattice_bottom, arg1[0]), arg1_new_sort
                    elif arg2[1] in {fgsort, intsort}:
                        arg2_new_sort = sort_to_setsort[arg2[1]]
                        arg2 = SetAdd(arg2_new_sort.lattice_bottom, arg2[0]), arg2_new_sort
                well_typed = arg1[1] == arg2[1] and arg1[1] in {fgsetsort, intsetsort}
            if not well_typed:
                raise BadType(f'Cannot operate "{binop}" over operands of type {arg1_old_sort} and {arg2_old_sort}',
                              loc, string)

            op_lookup = {
                '&': SetIntersect,
                '|': SetUnion,
                '+': lambda x, y: x + y,
                '-': lambda x, y: x - y,
                '*': lambda x, y: x * y
            }

            # The type of the interpretation is the same as the type of its operands in this case
            return op_lookup[binop](arg1[0], arg2[0]), arg1[1]

        # Grammar for relational atoms
        # Relation operations used infix. 'in' is set membership and '<', '==', etc are polymorphic.
        CompOp = pp.one_of("== != < <= > >= in")
        CompAtom = LParen + Term + CompOp + Term + RParen
        RelAtom = self.Application.copy()
        Atom = CompAtom ^ RelAtom

        # Interpretation for relational atoms
        @CompAtom.set_parse_action
        def interpret_comparison(string, loc, tokens):
            (arg1, arg1sort), binop, (arg2, arg2sort) = tokens
            # Check that the expression is well-typed
            if binop == 'in':
                well_typed = arg2sort == sort_to_setsort[arg1sort]
            else:
                # Comparisons other than equality/disequality cannot be made on Loc or Bool sort terms
                if binop not in {'==', '!='} and arg1sort in {fgsort, boolsort}:
                    well_typed = False
                else:
                    # Check that the arguments have the same sort
                    well_typed = arg1sort == arg2sort
            if not well_typed:
                raise BadType(
                    f'Cannot interpret {arg1} {binop} {arg2} between arguments of sorts {arg1sort} and {arg2sort}',
                    loc, string)
            # Define the conversion from symbols to operators considering the type of the operands
            if arg2sort == intsort:
                # Second operand is an integer
                op_lookup = {
                    '<': lambda x, y: x < y,
                    '<=': lambda x, y: x <= y,
                    '>': lambda x, y: x > y,
                    '>=': lambda x, y: x >= y
                }
            else:
                # Second operand is a set
                op_lookup = {
                    '<': z3.IsSubset,
                    '<=': lambda x, y: Or(IsSubset(x, y), x == y),
                    '>': lambda x, y: z3.IsSubset(y, x),
                    '>=': lambda x, y: Or(IsSubset(y, x), y == x)
                }
            op_lookup['in'] = z3.IsMember
            op_lookup['=='] = lambda x, y: x == y
            op_lookup['!='] = lambda x, y: x != y
            return op_lookup[binop](arg1, arg2)

        @RelAtom.add_parse_action
        def interpret_relation(string, loc, tokens):
            term, term_sort = tokens[0]
            if term_sort != boolsort:
                raise BadType(f'Expected boolean term but found {term} of sort {term_sort}',
                              loc, string)
            return term

        # Grammar for boolean combinations
        UnBoolOp = "!"  # boolean negation
        BinBoolOp = pp.one_of("& | =>")  # boolean operators used infix
        ITEFormula = LParen + IfKeyword + Formula + ThenKeyword + Formula + ElseKeyword + Formula + RParen
        Formula <<= Atom ^ (LParen + UnBoolOp + Formula + RParen) ^ (LParen + Formula + BinBoolOp + Formula + RParen) ^ ITEFormula

        # Interpretation for boolean combinations
        @ITEFormula.set_parse_action
        def interpret_ite_formula(string, loc, tokens):
            cond, then_formula, else_formula = tokens
            return If(cond, then_formula, else_formula)

        @Formula.set_parse_action
        def interpret_formula(string, loc, tokens):
            numtok = len(tokens)
            if numtok == 1:
                return tokens
            elif numtok == 2:
                # Negation is the only unary operator
                _, formula = tokens
                return Not(formula)
            else:
                arg1, binop, arg2 = tokens
                op_lookup = {
                    '&': And,
                    '|': Or,
                    '=>': Implies
                }
                return op_lookup[binop](arg1, arg2)
