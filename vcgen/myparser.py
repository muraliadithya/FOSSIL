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
            z3_var = Var(name, z3_type)
            vardict[name] = z3_var
        elif tag == 'Const':
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


# func_parser(create_input('(Function next Loc Loc)'))
# The input list will be of the form ['operator', operand 1, operand 2,...] where each operand could be another list
# or a string (which just means it is a variable).
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
# (13) (func x..)                        -> func(x ..)   #function application v2


def interpret_ops(list):
    
    #-------------(1)-------------
    if type(list) == str or len(list)==1: #the two cases are when the input variable is given without brackets
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
            return vardict[x]

    operator, operands = list[0], list[1:]


    #-------------(2)-------------
    if operator == 'not':
        if len(operands) != 1:
            raise Exception('not operator is unary. Either no argument or more than one argument was given')
        else:
            return Not(interpret_ops(operands[0]))

    #-------------(3)-------------
    elif operator == 'imp':
        if len(operands) != 2:
            raise Exception('implies takes two arguments')
        else:
            op1, op2 = operands
            return Implies(interpret_ops(op1),interpret_ops(2))

    #-------------(4)-------------
    elif operator == '=':
        if len(operands) != 2:
            raise Exception('Equality check(=) takes two arguments')
        else:
            op1, op2 = operands
            return (interpret_ops(op1)==interpret_ops(op2))

    #-------------(5)-------------
    elif operator == '!=':
        if len(operands) != 2:
            raise Exception ('!= takes two arguments')
        #shorthand for Not(x==y)
        else:
            op1, op2 = operands
            return Not((interpret_ops(op1)==interpret_ops(op2)))

    #-------------(6)-------------
    elif operator == 'ite':
        if len(operands) != 3:
            raise Exception ('If-Then-Else takes 3 arguments')
        else:
            op1, op2, op3 = operands
            return If(interpret_ops(op1),interpret_ops(op2),interpret_ops(op3))

    #-------------(7)-------------
    elif operator == 'and':
        return And(*[interpret_ops(op) for op in operands])

    #-------------(8)-------------
    elif operator == 'or':
        return Or(*[interpret_ops(op) for op in operands])
    
    
    #We will also define the assignment, mutation, and assume operators here->

    #-------------(9)------------- 
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

    #-------------(10)-------------
    elif operator == '.':
        if len(operands)!=2:
            raise Exception('Application takes two arguments: (. x function)')
        else:
            op1, op2 = operands
            if op2 in funcdict.keys():
                return funcdict[op2](vardict[op1])
            else:
                raise Exception('function not defined')

    #-------------(11)-------------
    elif operator == ':=':
        if len(operands)!=2:
            raise Exception('Assignment takes two arguments: (:= x y)')
        else:
            op1, op2 = operands
            if len(op1) == 1 or type(op1)==str: #LHS is a variable
                return (interpret_ops(op1)==interpret_ops(op2))
                
            elif len(op1) == 2 and len(op2) == 4:
                func, var = op1
                #itetag, o1, o2, o3 = op2
                if func in funcdict.keys():

                    if var in vardict.keys():
                        print(type(vardict[var]),interpret_ops(op1)==interpret_ops(op2))
                        return AddAxiom((vardict[var],),interpret_ops(op1)==interpret_ops(op2))


            #In SSA form, assume stuff like x.func = y will be given as ((func@c var) := (ite var==x, y, func@c-1))
            #both func@c and func@c-1 will be in funcdict(). So, need to add this to axioms.
            #choose var here carefully?
            #recdef functions also defined like this?

    #-------------(12)-------------
    elif operator == 'RecDef':
        #check this again:
        #format is (RecDef (function (x) (y)...) (recursive definition))
        op1, op2 = operands
        if op1[0] in recdefdict.keys():
            func, vars = op1[0], op1[1:]
            print('?????', interpret_ops(op2))
            return AddRecDefinition(recdefdict[func],*[interpret_ops(v) for v in vars],interpret_ops(op2))

    #-------------(13)-------------
    elif operator in funcdict.keys(): #i.e the function has been defined.
        return funcdict[operator](*[interpret_ops(op) for op in operands])   
    elif operator in recdefdict.keys():
        return recdefdict[operator](*[interpret_ops(op) for op in operands])        
    

# For now, let us assume that support defenitions are given in the input.
# The support will be from a sort to its setsort. The 'RecFunction' tag
# and 'RecDef' tag will be used in defining these. The only issue then is
# defining interpret_ops on sets.

    #-------------(14)-------------
    elif operator == 'SetAdd':
        #(SetAdd set x y ...) -> setU{x,y}
        if len(operands)<2:
            raise Exception('Format is (SetAdd set elt1 elt2...)')
        else:
            set = interpret_ops(operands[0])
            for i in range(1,len(operands)):
                SetAdd(set,interpret_ops(operands[i]))
            return set

    elif operator == 'Union':
        #(Union set set) -> setUset
        return Union(*[interpret_ops(op) for op in operands])
    
    elif operator == 'SetIntersect':
        return SetIntersect(*[interpret_ops(op) for op in operands])
    
    elif operator == 'IsSubset':
        # Check if a is a subset of b
        if len(operands)==2:
            return IsSubset(interpret_ops(operands[0]), interpret_ops(operands[1]))
        else:
            raise Exception('(IsSubset X Y) checks if X is a subset of Y')

    elif operator == 'IsEmpty':
        return IsSubset(interpret_ops(operands[0]),fgsetsort.lattice_bottom)    #?



    #IsSubset, Union, SetIntersect, SetComplement, EmptySet, SetUnion, SetAdd
    #note-> distinguish b/w Consts and Const? eq thing for var?   

#--------------------------------------Track Modified variables----------------------
# def is_mutate(list):
#     #The list must be [:= (func x) (mod_defn)]
#     operator, operands = list
#     if operator == ':=':
#         op1, op2 = operands
#         if len(op1)==2:
#             return True, 
#     else:
#         return False

#change the above. 
def vc(list):
    transform = []
    code_line = [create_input(i) for i in list]
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
            interpret_ops(i)
        elif tag == ':=' and len(i[1])==2 and len(i[2])==4: #i.e add axiom
            interpret_ops(i)
        else:
            transform.append(interpret_ops(i))
    print('done preprocessing')
    return Implies(And(precond,*[t for t in transform]),postcond)
    # print(goal)
    # np_solver = NPSolver()
    # solution = np_solver.solve(goal)
    # if not solution.if_sat:
    #     print('goal (no lemmas) is valid')
    # else:
    #     print('goal (no lemmas) is invalid')



# To add supports, we need set operations.

#eg:
t1 = ['(Const nil Loc)', '(Var x0 Loc)','(Var y0 Loc)','(Var x1 Loc)','(Var y1 Loc)','(Var var1 Loc)']
t2 = ['(Function next0 Loc Loc)','(Function next1 Loc Loc)','(Function next2 Loc Loc)']
t3 = ['(RecFunction list0 Loc Bool)','(RecFunction list2 Loc Bool)', '(RecFunction SPlist0 Loc SetLoc)','(RecFunction SPlist2 Loc SetLoc)']
t4 = ['(RecDef (SPlist2 var1) (ite (= var1 nil) EmptySet (SetAdd (SPlist2 (next2 var1)) var1)))']
t5 = ['(RecDef (SPlist0 var1) (ite (= var1 nil) EmptySet (SetAdd (SPlist0 (next0 var1)) var1)))']
t6 = ['(RecDef (list0 var1) (ite (= var1 nil) True (and (not (IsSubset (SetAdd EmptySet var1) (SPlist0 (next0 var1)))) (list0 (next0 var1)))) )'] 
t66= ['(RecDef (list2 var1) (ite (= var1 nil) True (and (not (IsSubset (SetAdd EmptySet var1) (SPlist2 (next2 var1)))) (list2 (next2 var1)))) )'] 

t7 = ['(Pre (list0 x0))']
t8 = ['(assume (!= x0 nil))','(:= y1 (. x0 next0))','(assume (!= y1 nil))']
t9 = ['(:= (next1 var1) (ite (= var1 x0) (. y1 next0) (next0 var1)))', '(:= (next2 var1) (ite (= var1 y1) (x0) (next1 var1)))']
t10 = ['(:= x1 y1)']
t11 = ['(Post (list2 x1))']
t = t1+t2+t3+t4+t5+t6+t66+t7+t8+t9+t10+t11
x = vc(t)
x0 = vardict['x0']
y1 = vardict['y1']
list0 = recdefdict['list0']
list2 = recdefdict['list2']
SPlist0 = recdefdict['SPlist0']
SPlist2 = recdefdict['SPlist2']
next0 = funcdict['next0']
next2 = funcdict['next2']
next1 = funcdict['next1']
nil = vardict['nil']
set1 = SetAdd(fgsetsort.lattice_bottom,x0)
set2 = SetAdd(fgsetsort.lattice_bottom,y1)
fp1 = And(list0(next0(y1)), Not(Or(IsSubset(set1,SPlist0(next0(y1))),IsSubset(set2,SPlist0(next0(y1))))))
AddAxiom((y1,), Implies(fp1,list2(next0(y1))))
np_solver = NPSolver()
print(x)
solution = np_solver.solve(x)
if not solution.if_sat:
    print('goal (no lemmas) is valid')
else:
    print('goal (no lemmas) is invalid')

# t1 = ['(Const nil Loc)', '(Var x0 Loc)','(Var y0 Loc)','(Var x1 Loc)','(Var y1 Loc)','(Var var1 Loc)']
# t2 = ['(Function next0 Loc Loc)','(Function next1 Loc Loc)','(Function next2 Loc Loc)']
# t3 = ['(Pre True)']
# t4 = ['(:= (next1 var1) (ite (= var1 x0) (. y1 next0) (next0 var1)))']
# t5 = ['(Post True)']
# t = t1+t2+t3+t4+t5
# vc(t)