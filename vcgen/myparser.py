from ast import operator
import importlib_resources
from configparser import SafeConfigParser
from decl_api import AddAxiom
import z3
from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, Union, SetIntersect, SetComplement, EmptySet, SetUnion, SetAdd
import pyparsing as pp

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Consts, Var, Vars, Function, RecFunction, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver
import naturalproofs.proveroptions as proveroptions
from naturalproofs.pfp import make_pfp_formula


from vcgen.utils import LParen, RParen
from vcgen.utils import RedeclarationException, UnknownExpression
from vcgen.utils import InterpretationException, BadType, BadDefinitionException
from vcgen.utils import ProgramState

from vcgen.CombinatorLogic import CombinatorLogic


#Fixing the input format:
#'(Var x type)'
#'(Const y type)'
#'(RecDef name type type...)'

def listify(string):
    sofar=[]
    parpair= []
    counter = 0
    foundp = 0
    nextlinekey = -1
    for i in range(len(string)-1):
        if string[i:i+2]=="\n":
            nextlinekey = i
    if nextlinekey!= -1:
        string = string[:nextlinekey]

    for i in range(len(string)):
        if string[i]=='(' :
            counter = counter+1
            if foundp == 0:
                foundp = 1
                x = i
        if string[i]==')':
            counter = counter-1
        if foundp == 1:
            if counter == 0:
                #found '(' and its corresponding ')'
                y = i
                parpair.append((x,y))
                foundp = 0 #move on
    if len(parpair) == 0:
        sofar.append(string)
        return sofar
    first = string[:(parpair[0][0])]
    last = string[(parpair[-1][1])+1:]
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

        sofar.append(listify(string[x+1:y]))
        now = string[y+1:z]
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
    secondlast = string[parpair[-1][0]+1:parpair[-1][1]]
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
    #this doesn't take stuff like 'list x' and give ['list', 'x]. It keeps it as ['list x']
    #Next we will take care of this. Assuming the input is given correctly,
    #everytime we see a space followed by something, we can safely split.
def make_list(list): #elements can be strings or lists
    def string_to_list(s):
        l = []
        whitespace = 1
        if len(s)<= 1: #must be non empty if input is correct
            if len(s) == 0 or s== ' ':
                return l
            else:
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


    for i in list:
        if type(i) == str:
            x = string_to_list(i)
            for j in x:
                newlist.append(j)
        else:
            newlist.append(make_list(i))
    return newlist

            
def create_input(string):
    return make_list(listify(string))[0]            #0?
# x = '(pre (and (list (next x)) (not (= x y))))'
# y = create_input(x)
# print(x)
# print(y)
#print(create_input('(RecDef list Int Bool)'))


#Note about the input: Spacing is important. create_input will see =xy as a single word, but will see = x y as 3.


#We will assume the program is in SSA for now.
#Dictionary to store variables:
vardict = dict()
#Dictionary to store functions:
funcdict = dict()
#Dictionary for the recusive definitions:
recdefdict = dict()
#Adding a variable to use in mutations
free_var = Var('free_var', fgsort)
#might need to change this when extending to other sorts; multiple input mutates?
modified_vars = []
#A program will be given as a list of strings, with strings being as above.

#Going from strings to types:
def type_parser(string):
    if string == 'Loc':
        return fgsort
    elif string == 'SetLoc':
        return fgsetsort
    elif string == 'Int':
        return intsort
    elif string == 'SetInt':
        return intsetsort
    elif string == 'Bool':
        return boolsort
    else:
        raise Exception('Unknown type detected')







#Adding to var_dict:
# Variables are given in the input as (Var x type). In our list notation, this will correspond to
# ['Var', 'x', 'type']. The 'Var' tag will be checked elsewhere, since we have to figure out if something is
# a variable before using this method.
def var_parser(varinfo):
    if len(varinfo)!=3:
        raise Exception('Variable/Constant input error: Should be of the form (Var name type) or (Const name type)')
        #Can just reuse this for constants as well
    else:
        tag, name, type = varinfo
        z3_type = type_parser(type)
        if tag == 'Var':
            z3_var = Var(name+'0', z3_type)
            vardict[name] = (z3_var, z3_type, 0)
        elif tag == 'Const':
            z3_var = Const(name, z3_type)
            vardict[name] = (z3_var, z3_type,None)


def func_parser(funcinfo):
    if len(funcinfo)<4:
        raise Exception('Function input error: <=3 arguments given when expecting at least 4. (Function name type type ... )')
    else:
        tag, name, type = funcinfo[0], funcinfo[1], funcinfo[2:]
        z3_type = [type_parser(x) for x in type]
        
        if tag == 'Function':
            z3_func = Function(name+'0', *z3_type)
            funcdict[name] = (z3_func, z3_type, 0)
        elif tag == 'RecFunction':
            z3_func = Function(name+'0', *z3_type)
            recdefdict[name] = (z3_func, z3_type, [], [],0) #the list will be replaced with the fn def 
        else:
            raise Exception('Wrong function/recfunction tag')

def var_update(name):
    if name in vardict.keys():
        var_name, z3_type, counter = vardict[name]
        var_new = Var(name+str(counter+1), z3_type)
        vardict[name] = (var_new, z3_type, counter+1)
    else:
        raise Exception('Not a declared variable')

def func_update(name):
    if name in funcdict.keys():
        func_name, z3_type, counter = funcdict[name]
        func_new = Function(name+str(counter+1), *z3_type)
        funcdict[name] = (func_new, z3_type, counter+1)
    elif name in recdefdict.keys():
        func_name, z3_type, description, subfns, counter = recdefdict[name]
        func_new = Function(name+str(counter+1), *z3_type)
        recdefdict[name] = (func_new, z3_type, description, subfns,counter+1)
    else:
        raise Exception('Not a declared function')


#--------------ABOUT UPDATING-----------------
#The dictionaries store variables/functions along with the info needed to calculate the 'next update', i.e
#to declare next1 from next0. Note that the key in the dictionary will be 'next' and not 'next1'.
#When considering recursive definitions. This means that we can just reuse the same definition each time
# and the dictionary will take care of updating each 'sub-function' of the recursive definition to the latest
#version.
#???-> except maybe the fuction name itself?
#---------------------------------------------


#Interpretting the input strings:
# The input list will be of the form ['operator', operand 1, operand 2,...] where each operand could be another list
# or a string (which just means it is a variable/const).
# What operators do we allow?
# (1)  x ->    x    ,                'True' -> True etc
# (2)  (not x)                           -> Not(x)
# (3)  (imp x y)                         -> Implies(x,y)
# (4)  (= x y)                           -> x==y
# (5)  (!= x y)                          -> Not(x==y)
# (6)  (ite x y z)                       -> If(x,y,z)
# (7)  (and x y z...)                    -> And(x,y,z,...)
# (8)  (or x y z...)                     -> Or(x,y,z,...)
# (9)  (assume x)                        -> x
# (10) (. x next)                        -> next(x)      #application
# (11) (:= x y)                          -> x==y         #assignment
# (12) (RecDef (func x..) (def_of_func)) -> AddRecDef(func, x..., def_of_func(x..)) #define recursive function
# (13),(14) (func x..)                   -> func(x ..)   #function application v2
# (15) (SetAdd set x y ...)              -> setU{x,y,...}
# (16) (Union set1 set2)                 -> set1Uset2
# (17) (Intersect set1 set2)             -> set1 intersection set2
# (18) (IsSubset set1 set2)              ->   Check if set1 is a subset of set2
# (19) (IsEmpty set)                     -> Check if set is empty

#The interpret_ops function goes through string like above and finds how to interpret it is.
#There are individual interpret functions for each kind of operator. See below. These are marked with the
# numbering as above.
def interpret_ops(list):
    if type(list) == str or len(list)==1:
        return interpret_basics(list)
    operator = list[0]
    if operator == 'not' or operator == 'Not':
        return interpret_not(list)
    elif operator == 'imp' or operator == 'Imp' or operator == 'Implies':
        return interpret_imp(list)
    elif operator == '=':
        return interpret_eq(list)
    elif operator == '!=':
        return interpret_neq(list)
    elif operator == 'ite':
        return interpret_ite(list)
    elif operator == 'and' or operator == 'And':
        return interpret_and(list)
    elif operator == 'or' or operator == 'Or':
        return interpret_or(list)
    elif operator == 'assume' or operator == 'Assume':
        return interpret_assume(list)
    elif operator == '.':
        return interpret_dot(list)
    elif operator == ':=':
        return interpret_assign(list)
    elif operator == 'RecDef':
        return interpret_recdef(list)
    elif operator in funcdict.keys():
        return interpret_func(list)
    elif operator in recdefdict.keys():
        return interpret_recfunc(list)
    elif operator == 'SetAdd':
        return interpret_setadd(list)
    elif operator == 'Union' or operator == 'SetUnion':
        return interpret_setunion(list)
    elif operator == 'Intersect' or operator == 'SetIntersect':
        return interpret_setintersect(list)
    elif operator == 'IsSubset':
        return interpret_issubset(list)
    elif operator == 'IsEmpty':
        return interpret_isempty(list)

#---------(1)--------------
def interpret_basics(list):
                                         #the two cases are when the input variable is given without brackets
    if type(list) == str:             #and if it is. for example (func x (y))-> ['fun', 'x', ['y']] 
        x = list                      #This then does func( interpret_ops('x'), interpret_ops(['y']))
    else:
        x = list[0]
    if x == 'True':
        return True
    elif x == 'False':
        return False
    elif x == 'EmptySet':
        return fgsetsort.lattice_bottom
    elif x in vardict.keys():
        return vardict[x][0]



#---------(2)---------------
def interpret_not(list):

    operator, operands = list[0], list[1:]
    if len(operands) != 1:
        raise Exception('not operator is unary. Either no argument or more than one argument was given')
    else:
        return Not(interpret_ops(operands[0]))

#----------(3)-----------------
def interpret_imp(list):
    operator, operands = list[0], list[1:]
    if len(operands) != 2:
        raise Exception('implies takes two arguments')
    else:
        op1, op2 = operands
        return Implies(interpret_ops(op1),interpret_ops(2))

#---------------(4)-------------------
def interpret_eq(list):
    operator, operands = list[0], list[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return (interpret_ops(op1)==interpret_ops(op2))
    else:
        raise Exception('Equality check(=) takes two arguments')


#----------------(5)------------------------
def interpret_neq(list):
    #shorthand for Not(x==y)
    operator, operands = list[0], list[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return Not((interpret_ops(op1)==interpret_ops(op2)))
    else:
        raise Exception ('!= takes two arguments')

#-------------------(6)-------------------------
def interpret_ite(list):
    operator, operands = list[0], list[1:]
    if len(operands) == 3:
        op1, op2, op3 = operands
        return If(interpret_ops(op1),interpret_ops(op2),interpret_ops(op3))
    else:
        raise Exception ('If-Then-Else takes 3 arguments')

#--------------------(7)-------------------------
def interpret_and(list):
    operator, operands = list[0], list[1:]
    return And(*[interpret_ops(op) for op in operands])

#--------------------(8)--------------------------
def interpret_or(list):
    operator, operands = list[0], list[1:]
    return Or(*[interpret_ops(op) for op in operands])

#--------------------(9)----------------------------
def interpret_assume(list):
    operator, operands = list[0], list[1:]
    if len(operands)==1:
        return interpret_ops(operands[0])
    else:
        raise Exception('Assume takes only one argument: (assume (arg))')

#---------------------(10)----------------------------
def interpret_dot(list):
    operator, operands = list[0], list[1:]
    if len(operands)==2:
        op1, op2 = operands
        if op2 in funcdict.keys():
            return funcdict[op2][0](vardict[op1][0])
        else:
            raise Exception('function not defined')
    else:
        raise Exception('Application takes two arguments: (. x function)')

#----------------------(11)------------------------------

def interpret_assign(list):
    operator, operands = list[0], list[1:]
    if len(operands)==2:
        op1, op2 = operands
        if len(op1) == 1 or type(op1)==str: #LHS is a variable

            rhs = interpret_ops(op2)
            var_update(op1)
            lhs = interpret_ops(op1)
            return (lhs==rhs)
            
        elif len(op1) == 3 :
            dot , var, func = op1
            #itetag, o1, o2, o3 = op2
            if func in funcdict.keys():
                if var in vardict.keys():
                    modified_vars.append(vardict[var][0])
                    # x.func = Y -> func'(var) = if var==x then Y else func(var)
                    y = If(free_var==vardict[var][0],interpret_ops(op2), funcdict[func][0](free_var))
                    func_update(func)
                    x = funcdict[func][0](free_var)

                    # def fp(recs_to_update):
                    #     check =[]
                    #     for i in recs_to_update:
                    #         check.append(i)
                    #     funcs_in_funcs = []
                    #     for name in recdefdict.keys():      #recdefdict[name] = (fn, type, description, sub_functions, counter)
                    #         for i in recs_to_update:
                    #             if i in recdefdict[name][3]: #If func is a subfuction, then need to update defn of this rec function.
                    #                 recs_to_update.append(name)
                    #     recs_to_update1 = recs_to_update+funcs_in_funcs
                    #     recs_to_update = [*set(recs_to_update1)]
                    #     s=0
                    #     for i in check:
                    #         for j in recs_to_update:
                    #             if i==j:
                    #                 pass
                    #             else:
                    #                 s=1
                    #                 break
                    #         if s==1:
                    #             break
                    #     if s==0:
                    #         return recs_to_update
                    #     else:
                    #         return fp(recs_to_update)
                    # p = []
                    # for name in recdefdict.keys():
                    #     if func in recdefdict[name][3]:
                    #         p.append(name)
                    # #p stores all the recursive functions that are directly affected by the mutation
                    # #The fp function: For each recdef function, it looks at the subfunctions and sees if 
                    # # one of the directly affected recdefs are in another rec def. 
                    # #If we reach a fix point, we stop. Other wise, call the function again.
                    # print('pfdafd',p)
                    # rec_functions_to_update = fp(p)
                   

                    #print('AddAxiom-->',(free_var,),x == y)
                    AddAxiom((free_var,),x == y)
                    for i in recdefdict.keys():
                        func_update(i)
                    for i in recdefdict.keys():
                        interpret_recdef(recdefdict[i][2])



    else:
        raise Exception('Assignment/mutation takes two arguments: (:= x y)')


#-------------------------(12)-------------------------------------------
def interpret_recdef(list):
    #Specifically for RecDef, not calls to recursive functions (see interpret_recfunc (14) for this).
    #In a program, for each RecFunction, there should only be one of these.
    operator, operands = list[0], list[1:] 
    #format is (RecDef (function (x) (y)...) (recursive definition))
    op1, op2 = operands
    if op1[0] in recdefdict.keys():


        func, vars = op1[0], op1[1:]
        #print('AddRecDefn~~>',recdefdict[func][0],*[interpret_ops(v) for v in vars],interpret_ops(op2))
        AddRecDefinition(recdefdict[func][0],*[interpret_ops(v) for v in vars],interpret_ops(op2))
        #This creates an initial definition of func, and  also adds a description of it into 
        # the recdefdict. When this is called in the program. We can get this description and 
        # update the definition if needed.

#-------------------------(13)----------------------------------------------
def interpret_func(list):
    operator, operands = list[0], list[1:]
    return funcdict[operator][0](*[interpret_ops(op) for op in operands]) 

#--------------------------(14)---------------------------------------------
def interpret_recfunc(list):
    #Specifically for function calls, not recursive definitions (see interpret_recdef (12) for this).
    operator, operands = list[0], list[1:]
    # #Note: At any point in the program. If we see a recursive function called, we need to define it again
    # # / make sure the version we have is the latest one.
    return recdefdict[operator][0](*[interpret_ops(op) for op in operands])



#----------------------------(15)---------------------------------------------
def interpret_setadd(list):
    operator, operands = list[0], list[1:]
    if len(operands)<2:
        raise Exception('Format is (SetAdd set elt1 elt2...)')
    else:
        set = interpret_ops(operands[0])
        for i in range(1,len(operands)):
            set = SetAdd(set,interpret_ops(operands[i]))
        return set

#-------------------------------(16)--------------------------------------------
def interpret_setunion(list):
    operator, operands = list[0], list[1:]
    return Union(*[interpret_ops(op) for op in operands])

#-------------------------------(17)--------------------------------------------
def interpret_setintersect(list):
    operator, operands = list[0], list[1:]
    return SetIntersect(*[interpret_ops(op) for op in operands])

#--------------------------------(18)-------------------------------------------
def interpret_issubset(list):
    operator, operands = list[0], list[1:]
    if len(operands)==2:
        return IsSubset(interpret_ops(operands[0]), interpret_ops(operands[1]))
    else:
        raise Exception('(IsSubset X Y) checks if X is a subset of Y')

#---------------------------------(19)------------------------------------------
def interpret_isempty(list):
    operator, operands = list[0], list[1:]
    return IsSubset(interpret_ops(operands[0]),fgsetsort.lattice_bottom)    #?





#----------------------------------------------------------------------------------
def sub_functions(list):    #given a rec def, find all other functions this depends on
    def find_func_in_list(l):
        funcs = []
        if type(l)==str:
            if l in recdefdict.keys() or l in funcdict.keys():
                funcs.append(l)

        else:
            for i in l:
                x = find_func_in_list(i)
                funcs = funcs+x
        return funcs            #gives list of functions in a recdef, with repeats.

    tag, name, recdef = list
    if tag != 'RecDef':
        raise Exception('Not a recursive function')
    if name[0] in recdefdict.keys():
        p = find_func_in_list(recdef)
        q = [*set(p)]               #removes duplicates
        r = []
        for i in q:
            if i!=name[0]:
                r.append(i)
    return r


#----------------------------------------------------------------------------------
#Below we club together everything so far to get a vc function.
#We assume input is given in the righ format. Need to handle issues better. Will do later.
init_recdef = dict()
def vc(list):
    transform = []
    code_line = [create_input(i) for i in list]
    #print(code_line)
    print('done creating input list')
    for i in code_line:
        tag = i[0]
        if tag =='Var' or tag == 'Const':
            var_parser(i)
        elif tag == 'Function' or tag == 'RecFunction':
            func_parser(i)
        elif tag == 'Pre':
            precond = interpret_ops(i[1])
        elif tag == 'Post':
            postcond = interpret_ops(i[1])
        elif tag == 'RecDef':
            name = i[1][0]
            if name in recdefdict.keys():
                z3_name, type, des, subfunc,counter = recdefdict[name]
                recdefdict[name] = (z3_name, type, i, sub_functions(i), counter)
                init_recdef[name] = (z3_name, type, i,name)
            else:
                raise Exception('Bad RecDef')
            interpret_ops(i)
        elif tag == ':=' and len(i[1])==3: #i.e add axiom
            interpret_ops(i)
        else:
            transform.append(interpret_ops(i))
    print('done preprocessing')
    #frame condition:#assume just 1 var for now
    mv = [*set(modified_vars)]
    set1 = fgsetsort.lattice_bottom
    for i in mv:
        set1 = SetAdd(set1,i)
    for i in recdefdict.keys():
        if i[:2]=='SP':
            pass
        else:
            #print('..................',((free_var,), Implies(And(init_recdef[i][0](free_var),IsSubset(SetIntersect(set1,init_recdef['SP'+i][0](free_var)),fgsetsort.lattice_bottom)),recdefdict[i][0](free_var))))
            AddAxiom((free_var,), Implies(IsSubset(SetIntersect(set1,init_recdef['SP'+i][0](free_var)), fgsetsort.lattice_bottom),init_recdef[i][0](free_var) == recdefdict[i][0](free_var)))
            AddAxiom((free_var,), Implies(IsSubset(SetIntersect(set1,init_recdef['SP'+i][0](free_var)), fgsetsort.lattice_bottom),init_recdef['SP'+i][0](free_var) == recdefdict['SP'+i][0](free_var)))

    goal =  Implies(And(precond,*[t for t in transform]),postcond)
    #cprint(goal)
    np_solver = NPSolver()
    np_solver.options.depth = 2
    solution = np_solver.solve(goal)
    if not solution.if_sat:
        print('goal (no lemmas) is valid')
    else:
        print('goal (no lemmas) is invalid')
    return goal




#####################################################################################

# t1 = ['(Const nil Loc)', '(Var x Loc)','(Var y Loc)','(Var var1 Loc)']
# t2 = ['(Function next Loc Loc)']
# t3 = ['(RecFunction list Loc Bool)', '(RecFunction SPlist Loc SetLoc)']
# t4 = ['(RecDef (SPlist var1) (ite (= var1 nil) EmptySet (SetAdd (SPlist (next var1)) var1)))']
# t5 = ['(RecDef (list var1) (ite (= var1 nil) True (and (not (IsSubset (SetAdd EmptySet var1) (SPlist (next var1)))) (list (next var1)))) )'] 
# t6 = ['(Pre (list x))']
# t7 = ['(assume (!= x nil))','(:= y (. x next))','(assume (!= y nil))']
# t8 = ['(:= (. x next) (. y next))', '(:= (. y next) x)']
# t9 = ['(:= x y)']
# t10 = ['(Post (list x))']
# t = t1+t2+t3+t4+t5+t6+t7+t8+t9+t10
# vc(t)