"""
This module defines some general functions, classes, and constants used by several parsing modules.
"""

import pyparsing as pp

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort


# Dictionary to convert from a sort to its corresponding set sort
sort_to_setsort = {fgsort: fgsetsort, intsort: intsetsort}
# Special tokens
LParen = pp.Literal("(").suppress()
RParen = pp.Literal(")").suppress()


# decorator to suppress actions depending on a boolean value
def suppress_parse_action(parser_element, dry):
    def wrapper(func):
        if dry:
            parser_element.set_parse_action(None)
        return func
    return wrapper


# Class to capture program state
class ProgramState:
    """
    This class is initialized by a set of dictionaries that represent a program state. It is used to freeze the
    program state at a particular point to use later.
    """
    def __init__(self, vardict, funcdict, name=None):
        # Data structures for representing program state
        # vardict is a dictionary from variable names as strings to information about the variable. The info present is
        # the type of the variable and its current value as a z3.ExprRef.
        self.vardict = vardict
        # funcdict is a dictionary from data/pointer field names as strings to info about the fields. The components have
        # the same meaning as in vardict. The current value component will sometimes be a python function
        # that produces an expression equivalent to the field lookup at that point in the program.
        self.funcdict = funcdict
        # Name of the state
        self.name = name


# Exception master class
class FOSSILParserException(Exception):
    """
    This exception class defines some general utilities that many specific parsing exception classes will use.
    """
    def __init__(self, message="", loc=None, string=None):
        if loc is not None and string is not None:
            # Find the line and column number corresponding to the given location in the string
            linecol = f'{pp.lineno(loc, string)}:{pp.col(loc, string)}'
            self.message = f'{message} at {linecol}'
        else:
            self.message = message

    def __str__(self):
        return self.message


# Exception classes
class InterpretationException(FOSSILParserException):
    """
    This exception is raised when a term or formula cannot be interpreted in the current program state.
    """
    pass


class BadType(FOSSILParserException):
    """
    This exception is raised when attempting to parse an ill-typed formula.
    """
    pass


class RedeclarationException(FOSSILParserException):
    """
    This exception is raised when a variable, field, or recursive definition is given two declarations.
    """
    pass


class BadDefinitionException(FOSSILParserException):
    """
    This exception is raised when a function definition cannot be reconciled with its declaration.
    """
    pass


class UnknownExpression(FOSSILParserException):
    """
    This exception is raised when an expression in the program cannot be interpreted.
    """
    pass
