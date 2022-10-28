from ast import ExceptHandler
import logging
import os

import z3 #debug

from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, IsMember, SetIntersect, SetUnion, SetAdd, EmptySet, IntSort, SetDifference, SetDel

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Var, Function, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver


#-----tags -------------
immutables = ['=', 'not', 'or', 'and', '=>', 'IsMember', 'IsSubset', 'SetAdd', 'SetIntersect', 'SetUnion', '<', '>', '>=', '<=', '+', '-']
supportTag = 'Sp'
verbose = 0 #Set verbose to 1 in order for print statements to be executed
def printf(*a):
    '''Print if verbose is set to 1'''
    if verbose != 0:
        print(*a)
#---------------------------------------------------------------
#Add logs into vcgen.txt, which will be in the path the code is run on
logfile = 'logs/vcgen.txt'
os.makedirs(os.path.dirname(logfile), exist_ok=True)
with open(logfile, 'w'):
    pass
logging.basicConfig(filename=logfile, level=logging.INFO)
with open(logfile, 'w'):
    pass
#---------------------------------------------------------------
def listify(input_string):
    '''The following is to convert the user input to the input for the vc functions.'''
    sofar=[]
    parpair= []
    counter = 0
    foundp = 0
    for i,elt in enumerate(input_string):
        if elt=='(' :
            counter = counter+1
            if foundp == 0:
                foundp = 1
                x = i
        if elt==')':
            counter = counter-1
        if foundp == 1:
            if counter == 0:
                #found '(' and its corresponding ')'
                y = i
                parpair.append((x,y))
                foundp = 0 #move on
    if len(parpair) == 0:
        sofar.append(input_string)
        return sofar
    first = input_string[:(parpair[0][0])]
    last = input_string[(parpair[-1][1])+1:]
    if len(first)==0:
        pass
    else:
        em = 0
        for i in first:
            if i!=' ':
                em = 1
                break
        if em == 1:
            sofar.append(first)
    for i in range(len(parpair)-1):
        x,y = parpair[i][0], parpair[i][1]
        z = parpair[i+1][0]

        sofar.append(listify(input_string[x+1:y]))
        now = input_string[y+1:z]
        if len(now)==0:
            pass
        else:
            em = 0
            for i in now:
                if i!=' ':
                    em =1
                    break
            if em == 1:
                sofar.append(now)
    secondlast = input_string[parpair[-1][0]+1:parpair[-1][1]]
    sofar.append(listify(secondlast))
    if len(last)==0:
        pass
    else:
        em = 0
        for i in last:
            if i!=' ':
                em = 1
                break
        if em == 1:
            sofar.append(last)
    return sofar

def make_list(semip_list): #elements can be strings or lists
    '''lisftify doesn't take stuff like 'list x' and give ['list', 'x]. It keeps it as ['list x'].
       make_list takes care of this. Assuming the input is given correctly, everytime a space is
       followed by something, it is safe to split'''
    def string_to_list(s):
        l = []
        if len(s)<= 1: #must be non empty if input is correct
            if len(s) == 0 or s== ' ':
                return l
            l.append(s)
            return l
        i = 0
        while i<len(s):
            if s[i] != ' ':
                if i==0 or s[i-1]==' ':
                    for j in range(i,len(s)):
                        if j==len(s)-1 or s[j+1]==' ':
                            l.append(s[i:j+1])
                            i=j+2
                            break
            else:
                i=i+1
        return l

    newlist = []


    for i in semip_list:
        if isinstance(i,str):
            x = string_to_list(i)
            for j in x:
                newlist.append(j)
        else:
            newlist.append(make_list(i))
    return newlist


def create_input(input_string):
    ''''Take a use given input and convert it into the input format used by the vc method '''
    return make_list(listify(input_string))[0]
# Note about the input: Spacing is important. create_input will
# see =xy as a single word, but will see = x y as 3.
# ---------------------------------------------------
#Dictionary to store variables:
vardict = {}
#Dictionary to store functions:
funcdict = {}
#Dictionary for the recusive definitions:
recdefdict = {}
#Adding a variable to use in mutations
free_var = Var('free_var', fgsort) # might need to change this when extending to other sorts; multiple input mutates?
freevardict = {'Loc':[],'SetLoc':[],'Int':[],'SetInt':[],'Bool':[]}
#List to store the Modified variables:
modified_vars = []
#set of allocated locations:
alloc_set = EmptySet(IntSort())                                  #??
#Variable keeping track of whether a new mutation has happened
has_mutated = 0
#Variable keeping track of the number of function calss
no_fc = 0
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
    tag, name, iptype = varinfo
    z3_type = type_parser(iptype)
    if tag == 'Var':
        z3_var = Var(name+'0', z3_type)
        vardict[name] = {'z3name': z3_var,'z3type': z3_type, 'counter': 0}
    elif tag == 'Const':
        z3_var = Const(name, z3_type)
        vardict[name] = {'z3name': z3_var,'z3type': z3_type, 'counter': None}


def func_parser(funcinfo):
    print('what->',funcinfo)
    '''Adding to func_dict'''
    if len(funcinfo)<4:
        raise Exception(f'Function input error: insufficient no. of arguments: {funcinfo}')
    tag, name, iptype = funcinfo[0], funcinfo[1], funcinfo[2:]

    # The following looks at a function's input types and creates free variables if necessary.
    # If the max no. of Loc in a fn is k, there will be k free_Loc variables created.
    type_of_inputs = iptype[0]
    no_of_inputs = len(iptype) - 1
    no_of_freevars_sofar = len(freevardict[type_of_inputs])
    if no_of_inputs > no_of_freevars_sofar:
        for i in range(no_of_freevars_sofar,no_of_inputs):
            freevardict[type_of_inputs].append(Var('free_'+type_of_inputs+str(i), type_parser(type_of_inputs)))


    z3_type = [type_parser(x) for x in iptype]
    print('iptype->',iptype)
    if tag == 'Function':
        z3_func = Function(name+'0', *z3_type)
        funcdict[name] = {'z3name': z3_func, 'z3type': z3_type, 'counter': 0,'input_type': type_of_inputs, 'no_inputs': no_of_inputs}
    elif tag == 'RecFunction':
        z3_func = Function(name+'0', *z3_type)
        recdefdict[name] = {'z3name': z3_func, 'z3type': z3_type, 'description': [],
                                'subfunctions': [], 'counter': 0, 'init': z3_func, 'input_type': type_of_inputs,'no_inputs': no_of_inputs}
        #...............
        if name[:2]!= 'SP':
            print('fdfadsfdaf:', funcinfo[2:-1],'ffffffffffffffffffffff---','Set'+funcinfo[2])
            typelist = [type_parser(i) for i in funcinfo[2:-1]]
            z3_sptype = [*typelist,type_parser('Set'+funcinfo[2])]       #Only really makes sense in (F name type1 type2)
            
            z3_spfunc = Function('SP'+name+'0',*z3_sptype)
            recdefdict['SP'+name] = {'z3name': z3_spfunc, 'z3type': z3_sptype, 'description': [],
                                         'subfunctions': [], 'counter': 0, 'init': z3_spfunc,'input_type': type_of_inputs,'no_inputs': no_of_inputs}
        #..............
    else:
        raise Exception(f'Tag error. Given: {tag} in {funcinfo}')


def var_update(name):
    '''Update variables and counters'''
    if name in vardict:
        counter, z3_type = vardict[name]['counter'], vardict[name]['z3type']
        c_new = counter+1
        var_new = Var(name+str(c_new), z3_type)
        vardict[name]['z3name'], vardict[name]['counter'] = var_new, c_new
    else:
        raise Exception(f' Undeclared variable {name}')

def func_update(name):
    '''Update functions(and rec functions) and counters'''
    if name in funcdict:
        z3_type,counter =  funcdict[name]['z3type'], funcdict[name]['counter']
        c_new = counter+1
        func_new = Function(name+str(c_new), *z3_type)
        funcdict[name]['z3name'], funcdict[name]['counter'] = func_new, c_new
    elif name in recdefdict:
        z3_type, counter = recdefdict[name]['z3type'], recdefdict[name]['counter']
        c_new = counter+1
        func_new = Function(name+str(c_new), *z3_type)
        recdefdict[name]['z3name'], recdefdict[name]['z3type'], recdefdict[name]['counter'] = func_new, z3_type, c_new
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


#---------(2)---------------
def interpret_not(iplist):
    '''(not X) -> Not(X) '''
    operands = iplist[1:]
    if len(operands) != 1:
        raise Exception(f'not operator is unary. Given {iplist}')
    return Not(interpret_ops(operands[0]))

#----------(3)-----------------
def interpret_imp(iplist):
    '''(imp A B) -> Implies(A,B)'''
    operands = iplist[1:]
    if len(operands) != 2:
        raise Exception(f'implies takes two arguments. Given: {iplist}' %iplist)
    op1, op2 = operands
    return Implies(interpret_ops(op1),interpret_ops(op2))

#---------------(4)-------------------
def interpret_eq(iplist):
    '''(= A B) -> A==B'''
    operands = iplist[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)==interpret_ops(op2))
    raise Exception(f'Equality check(=) takes two arguments. Given {iplist}')

#----------------(5)----------------------------
#-------------------(6)-------------------------
def interpret_ite(iplist):
    '''(ite A B C) -> If(A,B,C)'''
    operands = iplist[1:]
    if len(operands) == 3:
        op1, op2, op3 = operands
        return If(interpret_ops(op1),interpret_ops(op2),interpret_ops(op3))
    raise Exception (f'If-Then-Else takes 3 arguments. Given: {iplist}')

#--------------------(7)-------------------------
def interpret_and(iplist):
    '''(and A1 A2 A3 ...) -> And(A1,A2,...)'''
    operands = iplist[1:]
    return And(*[interpret_ops(op) for op in operands])

#--------------------(8)--------------------------
def interpret_or(iplist):
    '''(or A1 A2 ...) _. Or(A1,A2,...)'''
    operands = iplist[1:]
    return Or(*[interpret_ops(op) for op in operands])

#--------------------(9)----------------------------
def interpret_assume(iplist):
    '''(assume X) -> X
        Used to assume statements for the vc'''
    operands = iplist[1:]
    if len(operands)==1:
        return interpret_ops(operands[0])
    raise Exception(f'Assume takes only one argument: (assume (arg)). Given: {iplist}')

#---------------------(10)----------------------------


#----------------------(11)------------------------------

def interpret_assign(iplist):
    '''(assign X Y) where X can either be a variable or a mutation
        x:= Y will update x (increment counter to make an updated variable) to be Y
        (func x) := Y will update the function func' to say -> 
                        if arg is x then Y else (func arg) '''
    global modified_vars
    operands = iplist[1:]
    if len(operands)==2:
        op1, op2 = operands
        if (isinstance(op1,str) and (op1 in vardict)) or (len(op1)==1 and (op1[0] in vardict)): #LHS is a variable
            rhs = interpret_ops(op2)
            var_update(op1)
            lhs = interpret_ops(op1)
            return lhs==rhs
        if op1[0] in funcdict:  #if mutation
            func = op1[0]
            arg_list = []
            for i in range(1,len(op1)):
                if isinstance(op1[i],str):  #type check here?
                    arg_list.append(op1[i])
                elif len(op1[i]) == 1:
                    arg_list.append(op1[i][0])
                else:
                    raise Exception(f'Bad variable declaration {op1[i]}')
            to_check = []
            fv_used = []
            for i,arg in enumerate(arg_list):
                if arg in vardict:
                    modified_vars.append(vardict[arg]['z3name'])
                    to_check.append(freevardict[funcdict[func]['input_type']][i] == vardict[arg]['z3name'])
                    fv_used.append(freevardict[funcdict[func]['input_type']][i])

                else:
                    raise Exception(f'Invalid Variable {arg} ')
            y = If(And(*to_check),interpret_ops(op2), funcdict[func]['z3name'](*fv_used))
            func_update(func)
            x = funcdict[func]['z3name'](*fv_used)
            logging.info('Mutation: %s = %s' %(x,y))
            AddAxiom((*fv_used,), x == y)
            global has_mutated
            has_mutated = 1
            return None
        raise Exception(f'Invalid assignment/mutation {iplist}')
    raise Exception(f'Invalid number of arguments to assign operator {iplist}')

#-------------------------(12)-------------------------------------------
def interpret_recdef(iplist):
    ''' (RecDef (func args) (recursivedefn)) . Add a recursive definition for function func
        Specifically for RecDef, not calls to recursive functions.
        In a program, for each RecFunction, there should only be one of these.'''
    operands = iplist[1:]
    op1, op2 = operands
    if op1[0] in recdefdict:
        func, spfunc, args = op1[0], 'SP'+op1[0], op1[1:]
        #......................................................
        if op1[0][:2]!= 'SP':
            s1 = recdefdict[spfunc]['z3name']
            s2 = [interpret_ops(v) for v in args]
            s3 = support(op2)
            # print('s3->',z3.simplify(s3))
            logging.info('Adding support of recdef: (%s, %s, %s )' %(s1,s2,z3.simplify(s3)))
            AddRecDefinition(s1,tuple(s2),s3)
        #..........................................................
        a1 =recdefdict[func]['z3name']
        a2 = [interpret_ops(v) for v in args]
        a3 = interpret_ops(op2)
        logging.info('Adding recdef: (%s, %s, ,%s )' %(a1,a2,z3.simplify(a3)))
        # print('a3->',z3.simplify(a3))
        AddRecDefinition(a1,tuple(a2),a3)
        #This creates an initial definition of func, and  also adds a description of it into 
        # the recdefdict. When this is called in the program. We can get this description and 
        # update if needed.

#-------------------------(13)----------------------------------------------
def interpret_func(iplist):
    '''(func args) -> func(args)
        Used for non recursive functions'''
    operator, operands = iplist[0], iplist[1:]
    return funcdict[operator]['z3name'](*[interpret_ops(op) for op in operands])

#--------------------------(14)---------------------------------------------
def interpret_recfunc(iplist):
    '''(recfunc args) -> recfunc(args)
        Specifically for function calls, not recursive definitions. When a recfunc is called,
        need to check if it has been updated in accordance with mutations'''
    operator, operands = iplist[0], iplist[1:]
    global has_mutated
    if has_mutated == 1:        # if a function has been changed and we see a recfunc called, we update the defn, then apply the recfn.
        has_mutated = 0
        for i in recdefdict:
            func_update(i)
        for i in recdefdict:
            if i[:2] != 'SP':
                interpret_recdef(recdefdict[i]['description'])# interpret_recdef will make a defn for our recfunction, as well as its support

    return recdefdict[operator]['z3name'](*[interpret_ops(op) for op in operands])



#----------------------------(15)---------------------------------------------
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

#-------------------------------(16)--------------------------------------------
def interpret_setunion(iplist):
    '''(SetUnion X1 X2 X3...) -> Union of X1 X2 X3...'''
    operands = iplist[1:]
    return SetUnion(*[interpret_ops(op) for op in operands])

#-------------------------------(17)--------------------------------------------
def interpret_setintersect(iplist):
    '''(SetIntersect X1 X2 X3...) -> Intersection of X1 X2 X3...'''
    operands = iplist[1:]
    return SetIntersect(*[interpret_ops(op) for op in operands])

#--------------------------------(18)-------------------------------------------
def interpret_issubset(iplist):
    '''(IsSubset X Y) -> True if X is a subset of Y else False'''
    operands = iplist[1:]
    if len(operands)==2:
        return IsSubset(interpret_ops(operands[0]), interpret_ops(operands[1]))
    raise Exception('(IsSubset X Y) checks if X is a subset of Y')

#---------------------------------(19)------------------------------------------
def interpret_isempty(iplist):
    '''(IsEmpty X) -> Check if set X is empty'''
    operands = iplist[1:]
    return IsSubset(interpret_ops(operands[0]),EmptySet(IntSort()))    #?

#---------------------------------(20)------------------------------------------
def interpret_ismember(iplist):
    '''(IsMember x Y) -> CHeck if x is in Y'''
    operands = iplist[1:]
    if len(operands) == 2:
        return IsMember(interpret_ops(operands[0]),interpret_ops(operands[1]))
    raise Exception('(IsMember x Y) checks is x is a member of set Y.')

#---------------------------------(21)-------------------------------------------
def interpret_old(iplist):
    '''(Old (recfunc args)) -> apply the initial recfunc (before mutations) onto args'''
    operands = iplist[1:]
    if len(operands) == 1:
        func, arguments = operands[0][0], operands[0][1:]
        if func in recdefdict:
            return recdefdict[func]['init'](*[interpret_ops(op) for op in arguments])
        raise Exception(f'{func} is not a recursive function')
    raise Exception(f'Multiple arguments given to Old tag: {iplist}')

#---------------------------------------------------------------------------------------
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
        raise Exception(f'Invalid integer declaration {iplist}')
    return int(operands)

def function_call(iplist):
    operands = iplist[1:]
    if len(operands) == 2:
        global alloc_set
        global no_fc
        no_fc = no_fc + 1

        op1, op2 = operands
        sp_pre = support(op1)
        sp_post = support(op2)
        to_assume = interpret_assume(['assume', op2])        
        old_alloc_rem = SetDifference(alloc_set,sp_pre)

        for i,elt in funcdict.items():
            new_unint_fn = Function(elt['z3name']+'_unint_'+str(no_fc),*elt['z3type'])
            input_type = elt['input_type']
            no_inputs = elt['no_inputs']
            fv_used = freevardict[input_type][:no_inputs]
            fv_set = EmptySet(IntSort())
            for i in fv_used:
                fv_set = SetAdd(fv_set,i)
            y = If(IsSubset(fv_set,old_alloc_rem),elt['z3name'](*fv_used),new_unint_fn(*fv_used))
            func_update(i)
            x = elt['z3name'](*fv_used)
            logging.info(f'Function Call: {x} = {y}')
            AddAxiom((*fv_used,), x == y)
        global has_mutated
        alloc_set = SetUnion(old_alloc_rem,sp_post)
        has_mutated = 0
        for i in recdefdict:
            func_update(i)
        for i in recdefdict:
            if i[:2] != 'SP':
                interpret_recdef(recdefdict[i]['description'])# interpret_recdef will make a defn for our recfunction, as well as its support



        return to_assume
    
def interpret_alloc(iplist):
    operands = iplist[1:]
    if len(operands) == 1:
        x = operands[0]
        if isinstance(x,str):
            pass
        else:
            x = x[0]
    global alloc_set
    alloc_var = vardict[x]['z3name']
    var_update(x)
    SetAdd(alloc_set, vardict[x]['z3name'])

def interpret_free(iplist):
    operands = iplist[1:]
    if len(operands) == 1:
        x = operands[0]
        if isinstance(x,str):
            pass
        else:
            x = x[0]
    global alloc_set
    SetDel(alloc_set, vardict[x]['z3name'])


#----------------------------------------------------------------------------------
def sub_functions(recdef_list):
    '''given a rec def, find all other functions this depends on'''
    def find_func_in_list(l):
        funcs = []
        if isinstance(l,str):
            if (l in recdefdict) or (l in funcdict):
                funcs.append(l)

        else:
            for i in l:
                x = find_func_in_list(i)
                funcs = funcs+x
        return funcs            #gives list of functions in a recdef, with repeats.

    tag, name, defn = recdef_list
    if tag != 'RecDef':
        raise Exception('Not a recursive function')
    if name[0] in recdefdict:
        p = find_func_in_list(defn)
        q = [*set(p)]               #removes duplicates
        r = []
        for i in q:
            if i!=name[0]:
                r.append(i)
    return r


#--------------------Find Support--------------------------------------------------
def support(iplist):
    '''Find the support of the input'''
    
    if isinstance(iplist,str) or len(iplist)==1:
        return support_basics(iplist)
    operator = iplist[0]
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
    raise Exception(f'Invalid support operation {iplist}')

def support_basics(iplist):
    '''Support of var/const is the empty set'''
    if isinstance(iplist,str):
        x = iplist
    else:
        x = iplist[0]
    if x == 'True' or x == 'False' or x == 'EmptySetLoc' or x == 'EmptySetInt'  or (x in vardict):
        return EmptySet(IntSort())
    raise Exception('support basics failure')

def support_func(iplist):
    '''Say func dict is just mutable functions.'''
    operands = iplist[1:]

    terms = fgsetsort.lattice_bottom
    term_list = [interpret_ops(t) for t in operands]
    for i in term_list:
        terms = SetAdd(terms, i)

    sp_terms = SetUnion(*[support(t) for t in operands])

    if iplist[0] in funcdict:
        return SetUnion(terms,sp_terms)
    if iplist[0] in recdefdict:
        if iplist[0][:2] == 'SP':
            return interpret_ops(iplist)
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
                operands[0][0] = 'SP'+recfn
                sp_old = interpret_old(['Old',operands[0]])
                sp_terms = SetUnion(*[support(t) for t in args])
                return SetUnion(sp_old, sp_terms)

        raise Exception(f'Invalid rec def in support old operation {iplist}')
    raise Exception(f'Invalid tag in support old {iplist}')

#----------------------------------------------------------------------------------
#----------------------------------------------------------------------------------

def remove_comments(user_input):
    '''Remove comments in the input file'''
    for i in range(len(user_input)):
        user_input[i] = user_input[i].rstrip('\n')
    is_comment = 0
    upip = []
    for i in user_input:
        if len(i) == 0:
            pass
        elif is_comment == 0:
            q = 0
            store = -1
            j = 0
            while j < len(i)-1:
                if i[j:j+2] == '/*':
                    is_comment = is_comment + 1
                    if store == -1:
                        q = 1
                        store = j
                    j = j+2
                elif i[j:j+2] == '*/':
                    is_comment = is_comment - 1
                    j = j+2
                else:
                    j = j+1
            if q == 0:
                upip.append(i)
            elif store == 0:
                pass
            else:
                upip.append(i[:store])

        else:
            if len(i)>1:
                j = 0
                while j < len(i)-1:
                    if i[j:j+2] == '/*':
                        is_comment = is_comment + 1
                        j = j+2
                    elif i[j:j+2] == '*/':
                        is_comment = is_comment - 1
                        j = j+2
                    else:
                        j = j+1
    return upip
#assume comments have been removed

def ml_to_sl(user_input):
    '''Convert codes in multiple lines into a single line'''
    upip = []
    current_formula = ''
    np = 0
    for i in user_input:
        if np >= 0:
            current_formula = current_formula + ' ' + i
        for j in i:
            if j == '(':
                np = np+1
            elif j == ')':
                np = np-1
                if np < 0:
                    raise Exception('Two inputs in same line')

        if np == 0:
            upip.append(current_formula)
            current_formula = ''
    return upip

    


#Below we club together everything so far to get a vc function.
#We assume input is given in the right format.


def vc(user_input):
    '''VC generation'''
    nc_uip = ml_to_sl(remove_comments(user_input))
    code_line = [create_input(i) for i in nc_uip]
    logging.info(f'vc input list: {code_line}')
    #printf(code_line)
    printf('done creating input list')
    global alloc_set
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
        elif tag == 'RecDef':
            name = i[1][0]
            spname = 'SP'+i[1][0]
            if name in recdefdict:
                recdefdict[name]['description'], recdefdict[name]['subfunctions']  = i, sub_functions(i)
                z3_name = recdefdict[name]['z3name']
                recdefdict[name]['init'] = z3_name
                recdefdict[spname]['init'] = recdefdict[spname]['z3name']
            else:
                raise Exception('Bad RecDef %s' %name)
            interpret_ops(i)
        elif (tag == 'assign') and not(isinstance(i[1],str) or (len(i[1])==1)): #i.e add axiom
            interpret_ops(i)
        # elif (tag == 'call'): #handles in else case
        #     to_assume = function_call(i)    #this will return the post cond of the call,
        #     transform.append(to_assume)     #while also updating the allocated set
        elif (tag == 'free'):
            interpret_free(i)
        elif (tag == 'alloc'):
            interpret_alloc(i)
        else:
            intops = interpret_ops(i)
            logging.info('Line of code: %s' %intops)
            transform.append(intops)
    print('done preprocessing')
    #frame condition:#assume just 1 var for now
    mv = [*set(modified_vars)]
    modif_set = fgsetsort.lattice_bottom
    for i in mv:
        modif_set = SetAdd(modif_set,i)
    logging.info('Modified set is %s' %z3.simplify(modif_set))
    for i in recdefdict:
        if i[:2]=='SP':
            pass
        else:
            logging.info('Frame assumptions:')

            fv_used = []
            for j in range(recdefdict[i]['no_inputs']):
                fv_used.append(freevardict[recdefdict[i]['input_type']][j])
        
            a = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['init'](*fv_used)), fgsetsort.lattice_bottom),recdefdict[i]['init'](*fv_used) == recdefdict[i]['z3name'](*fv_used))
            logging.info(z3.simplify(a))
            AddAxiom((*fv_used,), a)
            b = Implies(IsSubset(SetIntersect(modif_set,recdefdict['SP'+i]['init'](*fv_used)), fgsetsort.lattice_bottom),recdefdict['SP'+i]['init'](*fv_used) == recdefdict['SP'+i]['z3name'](*fv_used))
            logging.info(z3.simplify(b))
            AddAxiom((*fv_used,), b)
    printf('\nvardict:',vardict,'\nFuncdict:',funcdict,'\nRecdefdict:', recdefdict)
    logging.info(f'Final Allocated Set: {z3.simplify(alloc_set)}')
    logging.info(f'Support of postcond: {z3.simplify(sp_postcond)}')
    goal =  Implies(And(precond,*[t for t in transform]), And(postcond, alloc_set == sp_postcond))
    # goal =  Implies(And(precond,*[t for t in transform]), postcond)
    print(goal)
    logging.info('Pre: %s' % precond)
    logging.info('Tranform: %s' % transform)
    logging.info('Post: %s' % postcond)
    np_solver = NPSolver()
    np_solver.options.depth = 1
    solution = np_solver.solve(goal)
    if not solution.if_sat:
        logging.info('goal is valid')
        print('goal is valid')
    else:
        logging.info('goal is invalid')
        print('goal is invalid')
    return goal



# def vc_mult(user_input):
    
#     global vardict
#     global funcdict
#     global recdefdict
#     global freevardict
#     global modified_vars
#     global alloc_set
#     global has_mutated
#     global no_fc 
#     nc_uip = ml_to_sl(remove_comments(user_input))
#     code_line = [create_input(i) for i in nc_uip]
#     logging.info(f'vc input list: {code_line}')
#     #printf(code_line)
#     printf('done creating input list')
#     vcs_in_file = []
#     current_vc = []
#     j = 0
#     while j <len(code_line):
#         if code_line[j] == ['END']:   #user input is (END)
#             vcs_in_file.append(current_vc)
#             current_vc = []
#         elif j == len(code_line)-1:
#             current_vc.append(code_line[j])
#             vcs_in_file.append(current_vc)
#             current_vc = []
#         else:
#             current_vc.append(code_line[j])
#         j = j+1
#     print(len(vcs_in_file))
#     for i in vcs_in_file:
#         vardict = {}
#         funcdict = {}
#         recdefdict = {}
#         freevardict = {'Loc':[],'SetLoc':[],'Int':[],'SetInt':[],'Bool':[]}
#         modified_vars = []
#         alloc_set = EmptySet(IntSort())
#         has_mutated = 0
#         no_fc  = 0
#         vc(i)
    



#####################################################################################
# t1 = ['(Const nil Loc)', '(Var x Loc)','(Var y Loc)','(Var var1 Loc)']
# t2 = ['(Function next Loc Loc)']
# t3 = ['(RecFunction list Loc Bool)']
# t5 = ['(RecDef (list var1) (ite (= var1 nil) True (and (not (IsMember (var1) (SPlist (next var1)))) (list (next var1)))) )'] 
# t6 = ['(Pre (list x))']
# t7 = ['(assume (!= x nil))','(:= y (. x next))','(assume (!= y nil))']
# t8 = ['(:= (. x next) (. y next))', '(:= (. y next) x)']
# t9 = ['(:= x y)']
# t10 = ['(Post (list x))']
# t = t1+t2+t3+t5+t6+t7+t8+t9+t10
# vc(t)
