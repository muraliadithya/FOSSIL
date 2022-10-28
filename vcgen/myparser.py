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
#x = '(pre (and (list (next x)) (not (= x y))))'
# y = make_list(x)
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
        z3_var = Const(name, z3_type)
        vardict[name] = z3_var

def func_parser(funcinfo):
    if len(funcinfo)<4:
        raise Exception('Function input error: <=3 arguments given when expecting at least 4. (Function name type type ... )')
    else:
        tag, name, type = funcinfo[0], funcinfo[1], funcinfo[2:]
        z3_type = [type_parser(x) for x in type]
        z3_func = Function(name, *z3_type)
        if tag == 'Function':
            funcdict[name] = z3_func
        elif tag == 'RecFunction':
            recdefdict[name] = z3_func
        else:
            raise Exception('Wrong function/recfunction tag')


#func_parser(create_input('(Function next Loc Loc)'))
#need to add rec functions and recdef. For this, we need to interpret 'and', 'ite', etc from the input list
#The input list will be of the form ['operator', operand 1, operand 2,...] where each operand could be another list
# or a string (which just means it is a variable).
#What operators do we allow?
#x-> x
#(not x) -> Not(x)
#(= x y) -> x==y
#(imp x y) -> Implies(x,y)
#(ite x y z) -> If(x,y,z)
#(and x y z...) -> And(x,y,z,...)
#(or x y z...) -> Or(x,y,z,...)

def interpret_ops(list):
    if len(list)==1:
        if list[0]=='True':
            return True
        elif list[0]=='False':
            return False
        #variable. So, go to dict and get it.
        return vardict[list[0]]

    operator, operands = list[0], list[1:]
    #print('operator,operand--->',operator,'..',operands)

    if operator == 'not':
        if len(operands) != 1:
            raise Exception('not operator is unary. Either no argument or more than one argument was given')
        else:
            return Not(interpret_ops(operands[0]))
    elif operator == 'imp':
        if len(operands) != 2:
            raise Exception('implies takes two arguments')
        else:
            op1, op2 = operands
            return Implies(interpret_ops(op1),interpret_ops(2))
    elif operator == '=':
        if len(operands) != 2:
            raise Exception('Equality check(=) takes two arguments')
        else:
            op1, op2 = operands
            return (interpret_ops(op1)==interpret_ops(op2))
    elif operator == '!=':
        if len(operands) != 2:
            raise Exception ('!= takes two arguments')
        #shorthand for Not(x==y)
        else:
            op1, op2 = operands
            return Not((interpret_ops(op1)==interpret_ops(op2)))
    elif operator == 'ite':
        if len(operands) != 3:
            raise Exception ('If-Then-Else takes 3 arguments')
        else:
            op1, op2, op3 = operands
            return If(interpret_ops(op1),interpret_ops(op2),interpret_ops(op3))
    elif operator == 'and':
        return And(*[interpret_ops[op] for op in operands])
    elif operator == 'or':
        return Or(*[interpret_ops[op] for op in operands])
    #We will also define the assignment, mutation, and assume operators here->
    #(assume x)->x
    #(:= x y) -> x=y #assignment
    #(. x next) -> next(x) #application
    elif operator == 'assume':
        if len(operands)!=1:
            raise Exception('Assume takes only one argument: (assume (arg))')
        else:
            return interpret_ops(operands[0])
    # elif operator == ':=':
    #     if len(operands)!=2:
    #         raise Exception('Assignment takes two arguments: (:= x y)')
    #     else:
    #         op1, op2 = operands
    #         return (interpret_ops(op1)==interpret_ops(op2)) #?

    #Maybe split := to two cases, namely when LHS is just some variable, and when LHS has a mutation?
    #See below
    elif operator == '.':
        if len(operands)!=2:
            raise Exception('Application takes two arguments: (. x function)')
        else:
            op1, op2 = operands
            print('myr',op1,'velya myr', op2)
            if op2[0] in funcdict.keys():
                return funcdict[op2[0]](vardict[op1[0]])
            else:
                raise Exception('function not defined')
    elif operator == ':=':
        if len(operands)!=2:
            raise Exception('Assignment takes two arguments: (:= x y)')
        else:
            op1, op2 = operands
            if len(op1) == 1: #LHS is a variable
                return (interpret_ops(op1)==interpret_ops(op2))
            elif len(op1) == 2 and len(op2) == 4:
                func, var = op1
                #itetag, o1, o2, o3 = op2
                if func in funcdict.keys():

                    if var in vardict.keys():
                        return AddAxiom((vardict[var],),interpret_ops(op1)==interpret_ops(op2))


            #In SSA form, assume stuff like x.func = y will be given as ((func@c var) := (ite var==x, y, func@c-1))
            #both func@c and func@c-1 will be in funcdict(). So, need to add this to axioms.
            #choose var here carefully?
            #recdef functions also defined like this?

    elif operator == 'RecDef':
        if len(operands)== 1:
            print('operaands:',operands)
            tag, op1, op2 = operands[0]
            print('op1',op1)
            if tag == ':=':
                if len(op1)>=2:
                     if op1[0] in recdefdict.keys():
                        func, vars = op1[0], op1[1:]
                        return AddRecDefinition(recdefdict[func],*[vardict[v[0]] for v in vars],interpret_ops(op2))
    else:
        if operator in funcdict.keys():#i.e the function has been defined.
            return funcdict[operator](*[interpret_ops(op) for op in operands])   
        elif operator in recdefdict.keys():
            print('operands', operands)
            return recdefdict[operator](*[interpret_ops(op) for op in operands])        
    
    
#assume supports are given (will deal with this later)
def vc(list):
    transform = []
    code_line = [create_input(i) for i in list]
    for i in code_line:
        #print('i...................',i)
        tag = i[0]
        if tag =='Var' or tag == 'Const':
            var_parser(i)
        elif tag == 'Function' or tag == 'RecFunction':
            func_parser(i)
        elif tag == 'pre':
            precond = interpret_ops(i[1])
        elif tag == 'post':
            postcond = interpret_ops(i[1])
        elif tag == 'RecDef':
            interpret_ops(i[1])
        else:
            transform.append(interpret_ops(i))
    goal = Implies(And(precond,*[t for t in transform]),postcond)
    np_solver = NPSolver()
    solution = np_solver.solve(goal)
    print(goal)
    if not solution.if_sat:
        print('goal (no lemmas) is valid')
    else:
        print('goal (no lemmas) is invalid')


#Test:

t1 = ['(Var y0 Loc)','(Var z Loc)','(Var y1 Loc)','(Var x0 Loc)','(Const nil Loc)','(Function next Loc Loc)']
t2 = ['(RecFunction list Loc Bool)']
t3 = ['(RecDef (:= (list (z)) (ite (= (z) (nil)) (True) (list (next (z))))))']
t4 = ['(assume (!= (x0) (nil)))','(= (y1) (. (x0) (next)))']
t5 = ['(pre (list (x0)))','(post (list (y1)))']
var_test = t1+t2+t3+t4+t5
vc(var_test)