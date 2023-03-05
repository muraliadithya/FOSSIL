from ast import ExceptHandler
import logging
import os

from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, IsMember, SetIntersect, SetUnion, SetAdd, EmptySet, IntSort, SetDifference, SetDel

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Var, Function, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver

from preprocessing import ml_to_sl, remove_comments, create_input

import z3 #debug

immutables = ['=', 'not', 'or', 'and', '=>', 'IsMember', 'IsSubset', 'SetAdd', 'SetDel','SetIntersect', 'SetUnion', '<', '>', '>=', '<=', '+', '-']
supportTag = 'Sp'

#Add logs into vcgen.txt, which will be in the path the code is run on
logfile = 'logs/vcgen.txt'
os.makedirs(os.path.dirname(logfile), exist_ok=True)
with open(logfile, 'w'):
    pass
logging.basicConfig(filename=logfile, level=logging.INFO)
with open(logfile, 'w'):
    pass

# --------------------GLOBAL-------------------------------
vardict = {}                                                        # Dictionary to store variables
funcdict = {}                                                       # Dictionary to store functions
recdefdict = {}                                                     # Dictionary for the recusive definitions
freevardict = {'Loc':[],'SetLoc':[],'Int':[],'SetInt':[],'Bool':[]} # Will add free vars based on max arity of fn.
modified_vars = []                                                  # Modified_vars used for frame rule
alloc_set = fgsetsort.lattice_bottom                                #
has_mutated = 0                                                     # If == 1, need to update recfns
number_of_function_calls = 0                                        #
lemma_set = set()                                                   # lemmas to be instantiated
lemma_description = []                                              #
# -----------------------------------------------

def type_parser(input_type):
    '''Going from strings to types:'''
    if input_type == 'Loc':
        return fgsort
    if input_type == 'SetLoc':
        return fgsetsort
    if input_type == 'Int':
        return intsort
    if input_type == 'SetInt':
        return intsetsort
    if input_type == 'Bool':
        return boolsort
    raise Exception(f'Allowed types are: Loc SetLoc Int SetInt Bool. Given: {input_type}')


def var_parser(varinfo):
    ''''Adding to var_dict: Input of the form ['Var', 'x', 'type']'''
    if len(varinfo)!=3:
        raise Exception(f'Variable/Constant input error. Given: {varinfo}')
    tag, name, input_type = varinfo
    z3_type = type_parser(input_type)
    if tag == 'Var':
        z3_var = Var(name+'0', z3_type)
        vardict[name] = {'z3name': z3_var,'z3type': z3_type, 'counter': 0}
    elif tag == 'Const':
        z3_var = Const(name, z3_type)
        vardict[name] = {'z3name': z3_var,'z3type': z3_type, 'counter': None}
    else:
        raise Exception(f'Invalid Var/Const tag {varinfo}')


def func_parser(funcinfo):
    '''Adding to func_dict. Input of the form [TAG, NAME, type, type....., output_type]
    All input types are the same.
    
    '''
    if len(funcinfo)<4:
        raise Exception(f'Function input error: insufficient no. of arguments: {funcinfo}')
    tag  = funcinfo[0]
    if tag == 'RecFunction':
        name, type_info =  funcinfo[1], funcinfo[2:]
    elif tag == 'Function':
        name, type_info, default_value =  funcinfo[1], funcinfo[2:-1], funcinfo[-1]

    # The following looks at a function's input types and creates free variables if necessary.
    # If the max no. of Loc in a fn is k, there will be k free_Loc variables created.
    type_of_inputs = type_info[0]
    for input_type in type_info[:-1]:
        if not(input_type == type_of_inputs):
            raise Exception('A function input types must be the same')
        
    no_of_inputs = len(type_info) - 1
    no_of_freevars_sofar = len(freevardict[type_of_inputs])
    if no_of_inputs > no_of_freevars_sofar:
        for i in range(no_of_freevars_sofar,no_of_inputs):
            freevardict[type_of_inputs].append(Var('free_'+type_of_inputs+str(i), type_parser(type_of_inputs)))


    z3_type = [type_parser(x) for x in type_info]
    if tag == 'Function':
        z3_func = Function(name+'0', *z3_type)
        interpreted_dv = interpret_ops(default_value)
        funcdict[name] = {'z3name': z3_func, 'z3type': z3_type, 'counter': 0,'input_type': type_of_inputs, 'no_inputs': no_of_inputs, 'default_value': interpreted_dv}
    elif tag == 'RecFunction':
        z3_func = Function(name+'0', *z3_type)
        recdefdict[name] = {'z3name': z3_func, 'z3type': z3_type, 'description': [],
                                'counter': 0, 'init': z3_func, 'input_type': type_of_inputs,'no_inputs': no_of_inputs, 'in_call': []}
        #...............
        if name[:2]!= 'SP':
            typelist = [type_parser(i) for i in type_info[:-1]]
            z3_sptype = [*typelist,fgsetsort]       #Only really makes sense in (F name type1 type2)
            
            z3_spfunc = Function('SP'+name+'0',*z3_sptype)
            recdefdict['SP'+name] = {'z3name': z3_spfunc, 'z3type': z3_sptype, 'description': [],
                                        'counter': 0, 'init': z3_spfunc,'input_type': type_of_inputs,'no_inputs': no_of_inputs, 'in_call': []}
        else:
            raise Exception('Functions not allowed to start with SP')
        #..............
    else:
        raise Exception(f'Tag error. Given: {tag} in {funcinfo}')


def var_update(name):
    '''Update variables and counters'''
    if name in vardict:
        counter, z3_type = vardict[name]['counter'], vardict[name]['z3type']
        counter_new = counter+1
        var_new = Var(name+str(counter_new), z3_type)
        vardict[name]['z3name'], vardict[name]['counter'] = var_new, counter_new
    else:
        raise Exception(f' Undeclared variable {name}')

def func_update(name):
    '''Update functions(and rec functions) and counters'''
    if name in funcdict:
        z3_type,counter =  funcdict[name]['z3type'], funcdict[name]['counter']
        counter_new = counter+1
        func_new = Function(name+str(counter_new), *z3_type)
        funcdict[name]['z3name'], funcdict[name]['counter'] = func_new, counter_new
    elif name in recdefdict:
        z3_type, counter = recdefdict[name]['z3type'], recdefdict[name]['counter']
        counter_new = counter+1
        func_new = Function(name+str(counter_new), *z3_type)
        recdefdict[name]['z3name'], recdefdict[name]['counter'] = func_new, counter_new
    else:
        raise Exception(f' Undeclared function {name}')


def interpret_ops(iplist):
    '''Takes an input and interprets into usable format for the nat proof solver'''
    if isinstance(iplist,str) or len(iplist) == 1:
        return interpret_basics(iplist)
    operator = iplist[0]
    if operator == 'not':
        return interpret_not(iplist)
    if operator == '=>':
        return interpret_imp(iplist)
    if operator == '=':
        return interpret_eq(iplist)
    if operator == 'ite':
        return interpret_ite(iplist)
    if operator == 'and':
        return interpret_and(iplist)
    if operator == 'or':
        return interpret_or(iplist)
    if operator == 'assume':
        return interpret_assume(iplist)
    if operator == 'assign':
        return interpret_assign(iplist)
    if operator == 'RecDef':
        return interpret_recdef(iplist)
    if operator in funcdict:
        return interpret_func(iplist)
    if operator in recdefdict:
        return interpret_recfunc(iplist)

    if operator == 'SetAdd':
        return interpret_setadd(iplist)
    if operator == 'SetUnion':
        return interpret_setunion(iplist)
    if operator == 'SetDel':
        return interpret_setdel(iplist)
    if operator == 'SetIntersect':
        return interpret_setintersect(iplist)
    if operator == 'IsSubset':
        return interpret_issubset(iplist)
    if operator == 'IsEmpty':
        return interpret_isempty(iplist)                  
    if operator == 'IsMember':
        return interpret_ismember(iplist)
    if operator == 'Sp':
        return support(iplist[1])
    if operator == 'Old':
        return interpret_old(iplist)

    if operator == '<':
        return interpret_less(iplist)
    if operator == '>':
        return interpret_greater(iplist)
    if operator == '<=':
        return interpret_leq(iplist)
    if operator == '>=':
        return interpret_geq(iplist)
    if operator == '+':
        return interpret_plus(iplist)
    if operator == '-':
        return interpret_minus(iplist)
    if operator == 'IntConst':
        return interpret_int(iplist)

    if operator == 'call':
        return function_call(iplist)
    if operator == 'alloc':
        return interpret_alloc(iplist)
    if operator == 'free':                  
        interpret_free(iplist)
    if operator == 'lemma':
        interpret_lemma(iplist)
    if operator == 'antiSp':
        return interpret_antisp(iplist)
    raise Exception(f'Invalid Tag {operator} in {iplist}')

#---------(1)--------------
def interpret_basics(iplist):
    '''Interpret basic inputs'''
    if isinstance(iplist, str): # if-else here since we allow users to say x as well as (x).
        x = iplist
    else:
        x = iplist[0]
    if x == 'True':
        return True
    if x == 'False':
        return False
    if x == 'EmptySetLoc':
        return fgsetsort.lattice_bottom
    if x == 'EmptySetInt':
        return intsetsort.lattice_bottom
    if x in vardict:
        return vardict[x]['z3name']

    raise Exception(f' Undeclared/invalid constant/variable {iplist}')

def interpret_not(iplist):
    '''(not X) -> Not(X) '''
    operands = iplist[1:]
    if len(operands) != 1:
        raise Exception(f'not operator is unary. Given {iplist}')
    return Not(interpret_ops(operands[0]))

def interpret_imp(iplist):
    '''(imp A B) -> Implies(A,B)'''
    operands = iplist[1:]
    if len(operands) != 2:
        raise Exception(f'implies takes two arguments. Given: {iplist}')
    op1, op2 = operands
    return Implies(interpret_ops(op1),interpret_ops(op2))

def interpret_eq(iplist):
    '''(= A B) -> A==B'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)==interpret_ops(op2))
    raise Exception(f'Equality check(=) takes two arguments. Given {iplist}')

def interpret_ite(iplist):
    '''(ite A B C) -> If(A,B,C)'''
    operands = iplist[1:]
    if len(operands) == 3:
        op1, op2, op3 = operands
        return If(interpret_ops(op1),interpret_ops(op2),interpret_ops(op3))
    raise Exception (f'If-Then-Else takes 3 arguments. Given: {iplist}')

def interpret_and(iplist):
    '''(and A1 A2 A3 ...) -> And(A1,A2,...)'''
    operands = iplist[1:]
    return And(*[interpret_ops(op) for op in operands])

def interpret_or(iplist):
    '''(or A1 A2 ...) -> Or(A1,A2,...)'''
    operands = iplist[1:]
    return Or(*[interpret_ops(op) for op in operands])

def interpret_assume(iplist):
    '''(assume X) -> X
        Used to assume statements for the vc'''
    operands = iplist[1:]
    if len(operands)==1:
        return interpret_ops(operands[0])
    raise Exception(f'Assume takes only one argument: (assume (arg)). Given: {iplist}')

def interpret_assign(iplist):
    '''(assign X Y) where X can either be a variable or a mutation
        x:= Y will update x (increment counter to make an updated variable) to be Y
        (func x) := Y will update the function func' to say -> 
                        if arg is x then Y else (func arg) '''
    global modified_vars
    operands = iplist[1:]
    if len(operands)==2:
        lhs, rhs = operands
        if (isinstance(lhs,str) and (lhs in vardict)) or (len(lhs)==1 and (lhs[0] in vardict)): #LHS is a variable
            interpreted_rhs = interpret_ops(rhs)
            var_update(lhs)
            interpreted_lhs = interpret_ops(lhs)
            return interpreted_lhs==interpreted_rhs
        if lhs[0] in funcdict:  #if mutation
            func = lhs[0]
            to_check = []
            free_vars_used = []
            for i in range(1,len(lhs)):
                argument = interpret_ops(lhs[i])
                modified_vars.append(argument)
                to_check.append(freevardict[funcdict[func]['input_type']][i-1] == argument)
                free_vars_used.append(freevardict[funcdict[func]['input_type']][i-1])

            new_func_definition = If(And(*to_check),interpret_ops(rhs), funcdict[func]['z3name'](*free_vars_used))
            func_update(func)
            new_func = funcdict[func]['z3name'](*free_vars_used)
            logging.info('Mutation: %s = %s' %(new_func,new_func_definition))
            AddAxiom((*free_vars_used,), new_func == new_func_definition)
            global has_mutated
            has_mutated = 1 #indicates recdefs need to be updated. Will do when necessary.
            return None
        raise Exception(f'Invalid assignment/mutation {iplist}')
    raise Exception(f'Invalid number of arguments to assign operator {iplist}')

def interpret_recdef(iplist):
    ''' (RecDef (func args) (recursivedefn)) . Add a recursive definition for function func
        Specifically for RecDef, not calls to recursive functions.
        In a program, for each RecFunction, there should only be one of these.
        
        Note: For updates to recursive functions, a description of the function is needed. This will be
        added in the main VC function    
    '''
    operands = iplist[1:]
    if len(operands) != 2:
        raise Exception('Invalid arguments on RecDef')
    func_info, func_definition = operands
    if func_info[0] in recdefdict:
        func, spfunc, args = func_info[0], 'SP'+func_info[0], func_info[1:]
        if func_info[0][:2]!= 'SP':
            s1 = recdefdict[spfunc]['z3name']
            s2 = [interpret_ops(v) for v in args]
            s3 = support(func_definition)
            logging.info('Adding support of recdef: (%s, %s, %s )' %(s1,s2,z3.simplify(s3)))
            AddRecDefinition(s1,tuple(s2),s3)
        a1 =recdefdict[func]['z3name']
        a2 = [interpret_ops(v) for v in args]
        a3 = interpret_ops(func_definition)
        logging.info('Adding recdef: (%s, %s,%s )' %(a1,a2,z3.simplify(a3)))
        AddRecDefinition(a1,tuple(a2),a3)

def interpret_func(iplist):
    '''(func args) -> func(args)
        Used for non recursive functions'''
    operator, operands = iplist[0], iplist[1:]
    return funcdict[operator]['z3name'](*[interpret_ops(op) for op in operands])

def interpret_recfunc(iplist):
    '''(recfunc args) -> recfunc(args)
        Specifically for calling a fn, not recursive definitions. When a recfunc is called,
        need to check if it has been updated in accordance with mutations'''
    operator, operands = iplist[0], iplist[1:]
    global has_mutated
    global lemma_description
    if has_mutated == 1:        # if a function has been changed and we see a recfunc called, we update the defn, then apply the recfn.
        has_mutated = 0
        for i in recdefdict:
            func_update(i)
        for i in recdefdict:
            if i[:2] != 'SP':
                interpret_recdef(recdefdict[i]['description'])# interpret_recdef will make a defn for our recfunction, as well as its support
        
        for i in lemma_description:
            instantiate_lemma(i)

    return recdefdict[operator]['z3name'](*[interpret_ops(op) for op in operands])

def interpret_setadd(iplist):
    '''(SetAdd X elt) -> SetAdd(X,elt)
        Add element elt into set X'''
    operands = iplist[1:]
    if len(operands)<2:
        raise Exception('Format is (SetAdd set elt1 elt2...)')
    return_set = interpret_ops(operands[0])
    for i in range(1,len(operands)):
        return_set = SetAdd(return_set,interpret_ops(operands[i]))
    return return_set

def interpret_setdel(iplist):
    '''(SetAdd X elt) -> SetAdd(X,elt)
        Add element elt into set X'''
    operands = iplist[1:]
    if len(operands)<2:
        raise Exception('Format is (SetAdd set elt1 elt2...)')
    return_set = interpret_ops(operands[0])
    for i in range(1,len(operands)):
        return_set = SetDel(return_set,interpret_ops(operands[i]))
    return return_set

def interpret_setunion(iplist):
    '''(SetUnion X1 X2 X3...) -> Union of X1 X2 X3...'''
    operands = iplist[1:]
    return SetUnion(*[interpret_ops(op) for op in operands])

def interpret_setintersect(iplist):
    '''(SetIntersect X1 X2 X3...) -> Intersection of X1 X2 X3...'''
    operands = iplist[1:]
    return SetIntersect(*[interpret_ops(op) for op in operands])

def interpret_issubset(iplist):
    '''(IsSubset X Y) -> True if X is a subset of Y else False'''
    operands = iplist[1:]
    if len(operands)==2:
        return IsSubset(interpret_ops(operands[0]), interpret_ops(operands[1]))
    raise Exception('(IsSubset X Y) checks if X is a subset of Y')

def interpret_isempty(iplist):
    '''(IsEmpty X) -> Check if set X is empty'''
    operands = iplist[1:]
    return IsSubset(interpret_ops(operands[0]),EmptySet(IntSort()))    #?

def interpret_ismember(iplist):
    '''(IsMember x Y) -> CHeck if x is in Y'''
    operands = iplist[1:]
    if len(operands) == 2:
        return IsMember(interpret_ops(operands[0]),interpret_ops(operands[1]))
    raise Exception('(IsMember x Y) checks is x is a member of set Y.')

def interpret_old(iplist):
    '''(Old (recfunc args)) -> apply the initial recfunc (before mutations) onto args'''
    operands = iplist[1:]
    if len(operands) == 1:
        func, arguments = operands[0][0], operands[0][1:]
        if func in recdefdict:
            return recdefdict[func]['init'](*[interpret_ops(op) for op in arguments])
        raise Exception(f'{func} is not a recursive function')
    raise Exception(f'Multiple arguments given to Old tag: {iplist}')

def interpret_less(iplist):
    ''' (< a b) -> check if a<b'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)<interpret_ops(op2))
    raise Exception(f'< takes two arguments. Given {iplist}')

def interpret_greater(iplist):
    '''(> a b) -> check if a>b'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)>interpret_ops(op2))
    raise Exception(f'> takes two arguments. Given {iplist}')

def interpret_leq(iplist):
    '''(<= a b) -> check if a<=b'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)<=interpret_ops(op2))
    raise Exception(f'<= takes two arguments. Given {iplist}')

def interpret_geq(iplist):
    '''(>= a b) -> check if a>=b'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)>=interpret_ops(op2))
    raise Exception(f'>= takes two arguments. Given {iplist}')

def interpret_plus(iplist):
    '''(+ a b) -> a+b'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)+interpret_ops(op2))
    raise Exception(f'+ takes two arguments. Given {iplist}')

def interpret_minus(iplist):
    '''(- a b) -> a-b'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)-interpret_ops(op2))
    raise Exception(f'- takes two arguments. Given {iplist}')

def interpret_int(iplist):
    '''(IntConst x) -> integer x'''
    operands = iplist[1:]
    if isinstance(operands,str):
        pass
    else:
        if isinstance(operands[0],str):
            operands = operands[0]
        else:
            raise Exception(f'Invalid integer declaration {iplist}')
    return int(operands)

def function_call(iplist):  # add a var update somewhere here in case someone uses an allocated var in return?
    operands = iplist[1:]
    if len(operands) == 2:
        global alloc_set
        global number_of_function_calls
        number_of_function_calls = number_of_function_calls + 1
        op1, op2 = operands
        sp_pre = support(op1)
               
        old_alloc_rem = SetDifference(alloc_set,sp_pre)

        for i,elt in funcdict.items():
            # new_unint_fn = Function(elt['z3name']+'_unint_'+str(no_fc),*elt['z3type'])
            new_unint_fn = Function(i+'_unint_'+str(number_of_function_calls),*elt['z3type'])
            input_type = elt['input_type']
            no_inputs = elt['no_inputs']
            fv_used = freevardict[input_type][:no_inputs]
            fv_set = fgsetsort.lattice_bottom
            for j in fv_used:
                fv_set = SetAdd(fv_set,j)
            y = If(IsSubset(fv_set,old_alloc_rem),elt['z3name'](*fv_used),new_unint_fn(*fv_used))
            func_update(i)
            x = elt['z3name'](*fv_used)
            logging.info(f'Function Call: {x} = {y}')
            AddAxiom((*fv_used,), x == y)
        global has_mutated
        has_mutated = 0
        for i in recdefdict:
            func_update(i)
        for i in recdefdict:
            if i[:2] != 'SP':
                interpret_recdef(recdefdict[i]['description'])# interpret_recdef will make a defn for our recfunction, as well as its support

        global lemma_description
        for i in lemma_description:
            instantiate_lemma(i)

        sp_post = support(op2)

        alloc_set = SetUnion(old_alloc_rem,sp_post)

        to_assume = interpret_ops(op2)   #dafdsfdsfdsfadsfdsfadfd
        for i in recdefdict:
            recdefdict[i]['in_call'].append(recdefdict[i]['z3name'])
            
        return And(to_assume,IsSubset(SetIntersect(old_alloc_rem,sp_post),fgsetsort.lattice_bottom))    #changed from just returning to_assume
    raise Exception('Bad function call')
    
def interpret_alloc(iplist):
    operands = iplist[1:]
    if len(operands) == 1:
        x = operands[0]
        if isinstance(x,str):
            pass
        else:   #add exception
            x = x[0]
    global alloc_set
    
    var_update(x)
    alloc_var = vardict[x]['z3name']
    to_return = [Not(IsMember(alloc_var, alloc_set))]
    alloc_set = SetAdd(alloc_set, alloc_var)
    for i, elt in funcdict.items():
        to_return.append(elt[alloc_var] == elt['default_value'])
            
    return And(*[to_return])

def interpret_free(iplist):
    operands = iplist[1:]
    if len(operands) == 1:
        x = operands[0]
        if isinstance(x,str):
            pass
        else:
            x = x[0]
    global alloc_set
    alloc_set = SetDel(alloc_set, vardict[x]['z3name'])
    



def interpret_lemma(iplist):
    global lemma_description
    operands = iplist[1:]
    lemma_description.append(operands)
    instantiate_lemma(operands)

#--------------------------------------------------------------------------
#--------------------------------------------------------------------------
def interpret_antisp(iplist):
    '''(antiSp X) -> X '''
    operands = iplist[1:]
    if len(operands) != 1:
        raise Exception(f'not operator is unary. Given {iplist}')
    return interpret_ops(operands[0])
#---------------------------------------------------------------------------
#---------------------------------------------------------------------------
def instantiate_lemma(operands):        #this 'instantiates' a lemma
    
    global lemma_set                    # (lemma (args) (body) )
    if len(operands)==2:
        argop, bodyop   = operands
        arglist = []
        for i in argop:
            if isinstance(i,str):
                if i in vardict:
                    arglist.append(vardict[i]['z3name'])
            elif len(i)==1:
                if i[0] in vardict:
                    arglist.append(vardict[i[0]]['z3name'])
            else:
                raise Exception(f'Invalid arguments in {operands}')

        argtuple = tuple(arglist)
        body = interpret_ops(bodyop)
        lemma_set.add((argtuple,body))
    else:
        raise Exception(f'lemma format (args) (body). Given {operands}')


#--------------------Find Support--------------------------------------------------
def support(iplist):
    '''Find the support of the input'''
    
    if isinstance(iplist,str) or len(iplist)==1:
        return support_basics(iplist)
    operator = iplist[0]
    if operator == 'IntConst':
        return fgsetsort.lattice_bottom
    if operator in immutables:
        return support_immut(iplist)
    if operator == 'ite':
        return support_ite(iplist)
    if operator == supportTag:
        return support_support(iplist)
    if (operator in funcdict) or (operator in recdefdict):
        return support_func(iplist)
    if operator == 'Old':
        return support_old(iplist)
    if operator == 'antiSp':
        return support_antisp(iplist)
    raise Exception(f'Invalid support operation {iplist}')

def support_basics(iplist):
    '''Support of var/const is the empty set'''
    if isinstance(iplist,str):
        x = iplist
    else:
        x = iplist[0]
    if x == 'True' or x == 'False' or x == 'EmptySetLoc' or x == 'EmptySetInt'  or (x in vardict):
        return fgsetsort.lattice_bottom
    raise Exception(f'support basics failure {iplist}')

def support_func(iplist):
    '''Say func dict is just mutable functions.'''
    operands = iplist[1:]


    sp_terms = SetUnion(*[support(t) for t in operands])

    if iplist[0] in funcdict:
        terms = fgsetsort.lattice_bottom
        term_list = [interpret_ops(t) for t in operands]
        for i in term_list:
            terms = SetAdd(terms, i)
        return SetUnion(terms,sp_terms)
    if iplist[0] in recdefdict:
        # if iplist[0][:2] == 'SP':
        #     return interpret_ops(iplist)
        # pp = ['SP'+iplist[0]]+operands
        # ipp = interpret_ops(pp)
        # return SetUnion(sp_terms, ipp)
        if iplist[0][:2] == 'SP':
            ipp = interpret_ops(iplist)
        else:
            pp = ['SP'+iplist[0]]+operands
            ipp = interpret_ops(pp)
        return SetUnion(sp_terms, ipp)
    raise Exception(f'Invalid support on functionos in {iplist}')


def support_immut(iplist):
    '''Support of immutables (see beginning of the file to see the immutables)'''
    operands = iplist[1:]
    return SetUnion(*[support(t) for t in operands ])

def support_ite(iplist):
    '''Support of if then else'''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'ite' and len(operands) == 3:
        op1, op2, op3 = operands
        x = If(interpret_ops(op1), SetUnion(support(op1),support(op2)), SetUnion(support(op1),support(op3)))
        return x      #?!
    raise Exception(f'Invalid if-then-else support given in {iplist}')

def support_support(iplist):
    '''Support of support -> support'''
    operator, operands = iplist[0], iplist[1:]
    if operator == supportTag and len(operands)==1:
        return support(operands[0])
    raise Exception(f'Support is a unary operator. Invalid support {iplist}')

def support_old(iplist):
    '''(Sp (Old (recfunc X))) -> (Old (Sp (recfunc X)))'''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'Old' and len(operands)==1:
        recfn, args = operands[0][0], operands[0][1:]
        if recfn in recdefdict:
            if recfn[:2] == 'SP':
                return interpret_old(['Old',operands[0]])
            elif recfn[:2] != 'SP':
                sp_old = interpret_old(['Old',['SP'+recfn]+args])
                sp_terms = SetUnion(*[support(t) for t in args])
                return SetUnion(sp_old, sp_terms)

        raise Exception(f'Invalid rec def in support old operation {iplist}')
    raise Exception(f'Invalid tag in support old {iplist}')
#----------------------------------------------------------------------------------
#----------------------------------------------------------------------------------
def support_antisp(iplist):
    '''(Sp (antiSp X)) -> EmptySetLoc'''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'antiSp' and len(operands)==1:
        return fgsetsort.lattice_bottom
    raise Exception(f'Invalid tag in support old {iplist}')
#----------------------------------------------------------------------------------
#----------------------------------------------------------------------------------


def vc(user_input):
    '''VC generation'''
    nc_uip = ml_to_sl(remove_comments(user_input))
    code_line = [create_input(i) for i in nc_uip]
    logging.info(f'vc input list: {code_line}')
    print('done creating input list')
    global alloc_set
    global lemma_set
    transform = []

    for i in code_line:
        tag = i[0]
        if tag =='Var' or tag == 'Const':
            var_parser(i)
        elif tag == 'Function' or tag == 'RecFunction':
            func_parser(i)
        elif tag == 'Pre':
            precond = interpret_ops(i[1])
            alloc_set = support(i[1])
            logging.info(f'Initial Alloc Set: {z3.simplify(alloc_set)}')
        elif tag == 'Post':
            postcond = interpret_ops(i[1])
            sp_postcond = support(i[1])
            rp = 0
        elif tag == 'RelaxedPost':
            postcond = interpret_ops(i[1])
            sp_postcond = support(i[1])
            rp = 1
        elif tag == 'SupportlessPost':      #for testing
            postcond = interpret_ops(i[1])
            sp_postcond = support(i[1])
            rp = 2

        elif tag == 'RecDef':
            name = i[1][0]
            spname = 'SP'+i[1][0]
            if name in recdefdict:
                recdefdict[name]['description']  = i
                z3_name = recdefdict[name]['z3name']
                recdefdict[name]['init'] = z3_name
                recdefdict[spname]['init'] = recdefdict[spname]['z3name']
            else:
                raise Exception('Bad RecDef %s' %name)
            interpret_ops(i)
        elif (tag == 'assign') and not(isinstance(i[1],str) or (len(i[1])==1)): #i.e add axiom
            interpret_ops(i)
        elif (tag == 'free'):
            interpret_free(i)
        elif (tag == 'alloc'):
            intops = interpret_alloc(i)
            transform.append(intops)
        elif (tag == 'lemma'):
            interpret_lemma(i)
        else:
            intops = interpret_ops(i)
            logging.info('Line of code: %s' %intops)
            transform.append(intops)
    print('done preprocessing')
    mv = [*set(modified_vars)]
    modif_set = fgsetsort.lattice_bottom
    for i in mv:
        modif_set = SetAdd(modif_set,i)
    logging.info('Modified set is %s' %z3.simplify(modif_set))
    for i in recdefdict:
        if i[:2]=='SP':
            pass
        else:
            # logging.info('Frame assumptions:')

            fv_used = []
            for j in range(recdefdict[i]['no_inputs']):
                fv_used.append(freevardict[recdefdict[i]['input_type']][j])
        
            a = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['init'](*fv_used)), fgsetsort.lattice_bottom),recdefdict[i]['init'](*fv_used) == recdefdict[i]['z3name'](*fv_used))
            # logging.info(z3.simplify(a))
            AddAxiom((*fv_used,), a)
            b = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['init'](*fv_used)), fgsetsort.lattice_bottom),recdefdict['SP'+i]['init'](*fv_used) == recdefdict['SP'+i]['z3name'](*fv_used))
            # logging.info(z3.simplify(b))
            AddAxiom((*fv_used,), b)

            for version_in_function_call in recdefdict[i]['in_call']:
                a = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['init'](*fv_used)), fgsetsort.lattice_bottom),version_in_function_call(*fv_used) == recdefdict[i]['z3name'](*fv_used))

                AddAxiom((*fv_used,), a)
            for version_in_function_call in recdefdict['SP'+i]['in_call']:            
                b = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['init'](*fv_used)), fgsetsort.lattice_bottom),version_in_function_call(*fv_used) == recdefdict['SP'+i]['z3name'](*fv_used))
                AddAxiom((*fv_used,), b)
            for j in range(len(recdefdict[i]['in_call'])):
                a = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['in_call'][j](*fv_used)), fgsetsort.lattice_bottom),recdefdict[i]['in_call'][j](*fv_used) == recdefdict[i]['z3name'](*fv_used))
                
                AddAxiom((*fv_used,), a)
                b = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['in_call'][j](*fv_used)), fgsetsort.lattice_bottom),recdefdict['SP'+i]['in_call'][j](*fv_used) == recdefdict['SP'+i]['z3name'](*fv_used))
                AddAxiom((*fv_used,), b)





    logging.info(f'Final alloc set: {z3.simplify(alloc_set)}')
    logging.info(f'Sp of postcondition: {z3.simplify(sp_postcond)}')
    # print('sp of postcond:', sp_postcond)
    if rp == 0:
        goal =  Implies(And(precond,*[t for t in transform]), And(postcond,sp_postcond == alloc_set))
        # goal =  Implies(And(precond,*[t for t in transform]), postcond)
    elif rp == 1:
        goal =  Implies(And(precond,*[t for t in transform]), And(postcond, IsSubset(sp_postcond,alloc_set)))
    elif rp == 2:
        goal =  Implies(And(precond,*[t for t in transform]), postcond)
    else:
        raise Exception ('No postcondition given')
    for i in lemma_set:
        logging.info(f'Lemma : {i}')
    logging.info(f'Goal: {goal}')
    # print('goal:->',goal)
    np_solver = NPSolver()
    np_solver.options.depth = 1
    print(np_solver.options.instantiation_mode)
    print('checking validity...')
    solution = np_solver.solve(goal,lemma_set)
    if not solution.if_sat:
        logging.info('goal is valid')
        print('goal is valid')
    else:
        logging.info('goal not proven')
        print('goal not proven')