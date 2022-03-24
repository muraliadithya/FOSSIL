import z3
import pyparsing as pp

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Var, Const, Function, RecFunction, AddRecDefinition

from vcgen.utils import LParen, RParen
from vcgen.utils import RedeclarationException, UnknownExpression
from vcgen.utils import InterpretationException, BadType, BadDefinitionException
from vcgen.utils import ProgramState

from vcgen.CombinatorLogic import CombinatorLogic


# Keywords and other important symbols
# Some are suppressed since they are purely for better aesthetic of input. Some are not suppressed since they will be
# used to make decisions during the parsing
VariableDeclarationTag = pp.Literal("Var").suppress()
ConstantDeclarationTag = pp.Literal("Const").suppress()
FunctionDeclarationTag = pp.Literal("Function")
RecFunctionDeclaractionTag = pp.Literal("RecFunction")
RecFunctionDefinitionTag = pp.Literal("Def").suppress()
PreconditionTag = pp.Literal("@pre:")
PostconditionTag = pp.Literal("@post:")
AssignmentOperator = pp.Literal(":=").suppress()
Dot = pp.Literal(".").suppress()
AssumeStatementTag = pp.Literal("assume").suppress()


#### Phase 1: declarations and recursive definitions
# Data structures for representing program state
# vardict is a dictionary from variable names as strings to information about the variable. The info tracked is
# the type of the variable and its current value as a z3.ExprRef as well as a counter storing the number of copies
vardict = dict()
# funcdict is a dictionary from function names as strings to info about the function. The components have
# the same meaning as in vardict. The current value component may be a python function
# that produces an expression equivalent to the function lookup at that point in the program (for mutable functions).
funcdict = dict()
# recdefdict is a dictionary from the names of recursive definitions as strings to info about them
# The information tracked is their bodies and formal parameters as strings
# The bodies are maintained as strings since we will only be able to compute the meaning of the body given other info
# about the program state such as the FO functions.
recdefdict = dict()


# Defining a grammar for types, variables, and functions
# Grammar for basic symbols
Type = pp.one_of("Loc SetLoc Int SetInt Bool")
VarName = pp.Word(pp.alphanums)
FuncName = pp.Word(pp.alphanums)


# Interpretation of types
@Type.set_parse_action
def translate_type(string, loc, tokens):
    annotation = tokens[0]
    type_lookup = {
        'Loc': fgsort,
        'SetLoc': fgsetsort,
        'Int': intsort,
        'SetInt': intsetsort,
        'Bool': boolsort
    }
    return type_lookup[annotation]


# Grammar for declarations
VarDecl = VariableDeclarationTag + VarName + Type
ConstDecl = ConstantDeclarationTag + VarName + Type
FuncDecl = (FunctionDeclarationTag ^ RecFunctionDeclaractionTag) + FuncName + Type[2, ...]
FODecl = pp.Group(VarDecl ^ ConstDecl ^ FuncDecl)


# Interpretation for declarations
@VarDecl.set_parse_action
def store_variable(string, loc, tokens):
    var_name, var_type = tokens
    _ = vardict.get(var_name, None)
    if _ is not None:
        raise RedeclarationException(f'Variable {var_name} is redeclared', loc, string)
    info_dict = {'type': var_type, 'value': Var(var_name, var_type), 'counter': 1}
    vardict[var_name] = info_dict


@ConstDecl.set_parse_action
def store_constant(string, loc, tokens):
    var_name, var_type = tokens
    _ = vardict.get(var_name, None)
    if _ is not None:
        raise RedeclarationException(f'Constant {var_name} is redeclared', loc, string)
    # Constants cannot be overwritten, so set counter to None
    info_dict = {'type': var_type, 'value': Const(var_name, var_type), 'counter': None}
    vardict[var_name] = info_dict


@FuncDecl.set_parse_action
def store_field(string, loc, tokens):
    func_tag, func_name, func_type = tokens[0], tokens[1], tokens[2:]
    _ = funcdict.get(func_name, None)
    if _ is not None:
        raise RedeclarationException(f'Function {func_name} is redeclared', loc, string)
    # Create temporary non-api objects for recfunctions
    info_dict = {'type': func_type,
                 'value': z3.Function(func_name, *[uctsort.z3sort for uctsort in func_type]) if func_tag == 'RecFunction' else Function(func_name, *func_type)}
    funcdict[func_name] = info_dict
    if func_tag == 'RecFunction':
        recdefdict[func_name] = dict()


# Grammar for variables and functions
Variable = pp.Word(pp.alphanums)
FOFunction = pp.Word(pp.alphanums)


# Interpretation for variables
@Variable.set_parse_action
def interpret_variable(string, loc, tokens):
    var_name = tokens[0]
    var = vardict.get(var_name, None)
    if var is None:
        raise InterpretationException(f'Unknown variable {var_name}', loc, string)
    interp, sort = vardict[var_name]['value'], vardict[var_name]['type']
    return interp, sort


# Grammar for application terms
Application = pp.Forward()
Application <<= Variable ^ (pp.Combine(FOFunction + LParen) + pp.delimitedList(Application) + RParen)


# Interpretation for application terms
# A term is interpreted as a z3.ExprRef. The interpretation functions below return both the interpretation and the
# uct sort to be used when parsing formulas.
@Application.set_parse_action
def interpret_application(string, loc, tokens):
    if len(tokens) == 1:
        return tokens[0]
    else:
        func_name, args = tokens[0], tokens[1:]
        # Lookup function in program state
        if func_name in funcdict:
            func = funcdict[func_name]['value']
        else:
            raise InterpretationException(f'Unknown function {func_name}', loc, string)
        # Check that the term is well-typed
        func_signature = funcdict[func_name]['type']
        expected_sorts = func_signature[:-1]
        obtained_sorts = [arg[1] for arg in args]
        if len(expected_sorts) != len(obtained_sorts):
            raise BadType(f'Wrong number of arguments to {func_name}: expected {len(expected_sorts)} but '
                          f'obtained {len(obtained_sorts)}', loc, string)
        try:
            mismatch = next(i for i in range(len(expected_sorts)) if expected_sorts[i] != obtained_sorts[i])
            raise BadType(f'Wrong argument type for argument number {mismatch + 1} of {func_name}: '
                          f'expected {expected_sorts[mismatch]} but obtained {obtained_sorts[mismatch]}',
                          loc, string)
        except StopIteration:
            pass
        interp = func(*[arg[0] for arg in args])
        return interp, func_signature[-1]


# Grammar for annotations and other formulas. Recdef bodies will be defined using the same language.
# The term/formula language is induced over the application language defined above.
annotation_logic = CombinatorLogic(Application)
AnnotationTerm = annotation_logic.Term
AnnotationFormula = annotation_logic.Formula
# Term/Formula language that does not parse into an expression. This is useful because we just want to store
# the bodies of recursive definitions as strings until we need to instantiate them at a particular program state.
# However, the parsing will internally still finish the transformation into an expression
# and can therefore catch errors.
BareAnnotationTerm = pp.original_text_for(AnnotationTerm)
BareAnnotationFormula = pp.original_text_for(AnnotationFormula)
# Grammar for recursive definitions
RecDef = RecFunctionDefinitionTag + (pp.Combine(FuncName + LParen) + pp.Group(pp.delimitedList(VarName)) + RParen) \
         + AssignmentOperator + (BareAnnotationTerm ^ BareAnnotationFormula)


# Interpretation for recursive definitions
@RecDef.set_parse_action
def store_rec_decl(string, loc, tokens):
    def_name, formal_params, body = tokens
    # Check that the function has been declared
    recdef_info = recdefdict.get(def_name, None)
    if recdef_info is None:
        raise BadDefinitionException(f'Symbol {def_name} undeclared', loc, string)
    elif recdef_info != dict():
        raise BadDefinitionException(f'Two definitions for {def_name}', loc, string)
    # Check if the definition is well-formed (best effort)
    given_arity = len(formal_params)
    expected_arity = len(funcdict[def_name]['type']) - 1
    if given_arity != expected_arity:
        raise BadDefinitionException(f'Arity mismatch: {def_name} has arity {expected_arity} '
                                     f'but was given {given_arity} arguments', loc, string)
    recdefdict[def_name] = {'params': list(formal_params), 'body': body}


# Grammar for all predeclarations
# Terminate the declarations with an empty token so we can check whether the logic is sufficiently defined
StopDecls = pp.Empty()
Decls = FODecl[1, ...] + RecDef[...] + StopDecls


# Checking that the declarations have been made correctly.
@StopDecls.add_condition
def check_decls(string, loc, tokens):
    # Check whether every function declared as a recfunction has a definition
    no_body = [def_name for def_name, value in recdefdict.items() if value == dict()]
    if no_body:
        raise BadDefinitionException(f'The following were declared as recursive functions '
                                     f'but no definition was given: {", ".join(no_body)}')
    # Check whether footprint functions are defined for every normal recursive definition
    basic_defs = [recdef for recdef in recdefdict if not recdef.startswith('SP')]
    for recdef in basic_defs:
        if 'SP' + recdef not in recdefdict:
            raise BadDefinitionException(f'Footprint definition {"SP" + recdef} not found for definition {recdef}')
    return True


#### Phase 2: precondition, program, and postcondition
# This part of the input is separated from the previous part by the empty token StopDecls
# Datastructures to track parsing progress: precondition, program transformation formula, footprint, and postcondition
pre_state = None
pre_cond = None
trans = []
footprint = []
post_state = None
post_cond = None


# Grammar for pre and post conditions
StateMarker = PreconditionTag ^ PostconditionTag
Annotation = StateMarker + AnnotationFormula


# Interpretation for pre and post conditions
# Function to make a well-defined program state
# This involves adding definitions for recursive functions using the value of the mutable functions at that state.
@StateMarker.set_parse_action
def instantiate_prog_state(string, loc, tokens):
    state_name = tokens[0][1:-1]
    for def_name in recdefdict:
        # Declare the functions
        funcdict[def_name]['value'] = RecFunction(f'{def_name}@{state_name}', *funcdict[def_name]['type'])
        # Define the body expression
        # formal_params = [Var(f'{recdefdict[def_name]["params"][i]}@{state_name}', funcdict[def_name]['type'][i])
        #                  for i in range(len(recdefdict[def_name]['params']))]
        formal_params = [vardict[var_name]['value'] for var_name in recdefdict[def_name]['params']]
        body_string = recdefdict[def_name]['body']
        parser_element = AnnotationFormula if funcdict[def_name]['type'][-1] == boolsort else AnnotationTerm
        body = parser_element.parse_string(body_string)[0]
        # Get only the body for recursive definitions that return terms
        if funcdict[def_name]['type'][-1] != boolsort:
            body = body[0]
        AddRecDefinition(funcdict[def_name]['value'], tuple(formal_params), body)
    # Construct state
    prog_state = ProgramState(vardict, funcdict, state_name)
    if state_name == 'pre':
        global pre_state
        pre_state = prog_state
    elif state_name == 'post':
        global post_state
        post_state = prog_state


# When parsing this the StateMarker action will have already been executed, therefore formulae will be interpreted
# in the correct program state. This relies on knowledge of the order in which pyparsing executes the actions of
# sequentially ordered nonterminals.
@Annotation.set_parse_action
def store_annotation(string, loc, tokens):
    state_marker, annotation_formula = tokens
    state_name = state_marker[1:-1]
    if state_name == 'pre':
        global pre_cond
        pre_cond = annotation_formula
    elif state_name == 'post':
        global post_cond
        post_cond = annotation_formula


# Grammar for program terms and conditions
# ProgApplication = pp.Forward()
# ProgApplication <<= Variable ^ (pp.Combine(ProgApplication + Dot + FOFunction))
# Program applications have to be defined in this weird way because pyparsing has trouble with left recursion
ProgApplication = Variable + (Dot + FOFunction)[...]
# The condition language is induced over the program term language defined above.
prog_logic = CombinatorLogic(ProgApplication)
ProgTerm = prog_logic.Term
ProgCond = prog_logic.Formula


# Interpretation of program application expressions
@ProgApplication.set_parse_action
def interpret_prog_term(string, loc, tokens):
    if len(tokens) == 1:
        return tokens[0]
    (interp, interp_sort), applications = tokens[0], tokens[1:]
    # Build the sequence of applications
    for func_name in applications:
        # Check that the expression is well-typed
        func_info = funcdict.get(func_name, None)
        if func_info is None:
            raise UnknownExpression(f'Unknown function {func_name}', loc, string)
        expected_sort = func_info['type'][:-1]
        if len(expected_sort) > 1 or interp_sort != expected_sort[0]:
            raise UnknownExpression(f'Cannot apply {func_name} of type {expected_sort} '
                                    f'to argument of type {interp_sort}', loc, string)
        interp = func_info['value'](interp)
        interp_sort = func_info['type'][-1]
    return interp, interp_sort


# Grammar for program statements
AssumeStatement = AssumeStatementTag + ProgCond
AssignOrMutateStatement = ProgApplication + AssignmentOperator + ProgTerm
Statement = AssumeStatement ^ AssignOrMutateStatement
Statements = Statement[...]


# Interpretation for program statements
# TODO


Program = Decls + Annotation + Statements + Annotation
