import logging


from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, IsMember, SetIntersect, SetUnion, SetAdd

from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Var, Function, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver



#Set verbose to 1 in order for print statements to be executed
verbose = 1 
def printf(*a):
    if verbose != 0:
        print(*a)
#---------------------------------------------------------------
#Add logs into vcgen.txt, which will be in the path the code is run on
logging.basicConfig(filename='vcgen.txt', level=logging.INFO)
with open('vcgen.txt', 'w'):
    pass
#---------------------------------------------------------------

#The following is to convert the user input to the input for the vc functions. 
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
    return make_list(listify(string))[0]

#Note about the input: Spacing is important. create_input will see =xy as a single word, but will see = x y as 3.
#-----------------------------------------------------------------
#Dictionary to store variables:
vardict = dict()
#Dictionary to store functions:
funcdict = dict()
#Dictionary for the recusive definitions:
recdefdict = dict()
#Adding a variable to use in mutations
free_var = Var('free_var', fgsort) ##might need to change this when extending to other sorts; multiple input mutates?
#List to store the Modified variables: 
modified_vars = []
#------------------------------------------------

#The use input will be converted into a list of strings.
# Going from strings to types:
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
        raise Exception('Allowed types are: Loc SetLoc Int SetInt Bool. Given: %s' %string)




# Adding to var_dict: Input of the form ['Var', 'x', 'type']
def var_parser(varinfo):
    if len(varinfo)!=3:
        raise Exception('Variable/Constant input error: Should be of the form (Var name type) or (Const name type). Given: %s' %varinfo)
    else:
        tag, name, type = varinfo
        z3_type = type_parser(type)
        if tag == 'Var':
            z3_var = Var(name+'0', z3_type)
            vardict[name] = (z3_var, z3_type, 0)
        elif tag == 'Const':
            z3_var = Const(name, z3_type)
            vardict[name] = (z3_var, z3_type,None)      #might want to make a seperate dict for constants and say things in constdict can't be derefd. Or could just 
                                                        #check if vardict[name][3] is None
#Adding to func_dict:
def func_parser(funcinfo):
    if len(funcinfo)<4:
        raise Exception('Function input error: <=3 arguments given when expecting at least 4. (Function name type type ... ). Given: %s' %funcinfo)
    else:
        tag, name, type = funcinfo[0], funcinfo[1], funcinfo[2:]
        z3_type = [type_parser(x) for x in type]
        
        if tag == 'Function':
            z3_func = Function(name+'0', *z3_type)
            funcdict[name] = (z3_func, z3_type, 0)
        elif tag == 'RecFunction':
            z3_func = Function(name+'0', *z3_type)
            recdefdict[name] = (z3_func, z3_type, [], [],0) #(function name, function type, description, sub-functions, counter)
            #...............
            if name[:2]!= 'SP':
                z3_sptype = [type_parser(funcinfo[2]),type_parser('Set'+funcinfo[2])]       #Only really makes sense in (F name type1 type2)
                z3_spfunc = Function('SP'+name+'0',*z3_sptype)
                recdefdict['SP'+name] = (z3_spfunc,z3_sptype,[],[],0)
            #..............
        else:
            raise Exception('Allowed function/recfunction tags are: Function RecFunction. Given: %s in %s' %(tag, funcinfo))    #don't actually need this
#Update variables and counters:
def var_update(name):
    if name in vardict.keys():
        var_name, z3_type, counter = vardict[name]
        c_new = counter+1
        var_new = Var(name+str(c_new), z3_type)
        vardict[name] = (var_new, z3_type, c_new)
    else:
        raise Exception(' %s is not a declared variable' %name )

def func_update(name):
    if name in funcdict.keys():
        func_name, z3_type, counter = funcdict[name]
        c_new = counter+1
        func_new = Function(name+str(c_new), *z3_type)
        funcdict[name] = (func_new, z3_type, c_new)
    elif name in recdefdict.keys():
        func_name, z3_type, description, subfns, counter = recdefdict[name]
        c_new = counter+1
        func_new = Function(name+str(c_new), *z3_type)
        recdefdict[name] = (func_new, z3_type, description, subfns,c_new)
    else:
        raise Exception('%s is not a declared function' %name)


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
# (20) (IsMember x set)                  -> Checkk if x is in set
#The interpret_ops function goes through strings like above and finds how to interpret it.
#There are individual interpret functions for each kind of operator. See below.
def interpret_ops(list):
    if type(list) == str or len(list)==1:
        return interpret_basics(list)
    operator = list[0]
    if operator == 'not' or operator == 'Not':
        return interpret_not(list)
    elif operator == 'imp' or operator == 'Imp' or operator == 'implies' or operator == 'Implies':
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
    elif operator == ':=' or operator == 'Assign' or operator == 'assign':
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
    elif operator == 'IsMember':
        return interpret_ismember(list)

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
    else:
        raise Exception('%s is not a constant/variable' %list)



#---------(2)---------------
def interpret_not(list):

    operator, operands = list[0], list[1:]
    if len(operands) != 1:
        raise Exception('not operator is unary. Either no argument or more than one argument was given: %s' %list)
    else:
        return Not(interpret_ops(operands[0]))

#----------(3)-----------------
def interpret_imp(list):
    operator, operands = list[0], list[1:]
    if len(operands) != 2:
        raise Exception('implies takes two arguments. Given: %s' %list)
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
        raise Exception('Equality check(=) takes two arguments. Given %s' %list)


#----------------(5)------------------------
def interpret_neq(list):
    #shorthand for Not(x==y)
    operator, operands = list[0], list[1:]
    if len(operands) == 2:
        op1, op2 = operands
        return Not((interpret_ops(op1)==interpret_ops(op2)))
    else:
        raise Exception ('!= takes two arguments. Given %s' %list)

#-------------------(6)-------------------------
def interpret_ite(list):
    operator, operands = list[0], list[1:]
    if len(operands) == 3:
        op1, op2, op3 = operands
        return If(interpret_ops(op1),interpret_ops(op2),interpret_ops(op3))
    else:
        raise Exception ('If-Then-Else takes 3 arguments. Given: %s' %list)

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
        raise Exception('Assume takes only one argument: (assume (arg)). Given: %s' %list)

#---------------------(10)----------------------------
def interpret_dot(list):
    operator, operands = list[0], list[1:]
    if len(operands)==2:
        op1, op2 = operands
        if op2 in funcdict.keys():
            if op1 in vardict.keys():
                return funcdict[op2][0](vardict[op1][0])
            else:
                raise Exception('Given %s. Variable %s not defined' %(list,op1))
        else:
            raise Exception('Given %s. Function %s not defined' %(list,op2))
    else:
        raise Exception('Application takes two arguments: (. x function). Given: %s' %list)

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
            
        elif op1[0] == '.' or (op1[0] in funcdict.keys()):
            if op1[0] == '.':
                dot , var, func = op1
            else:
                func, var = op1
            if func in funcdict.keys():
                if var in vardict.keys():           #generalize
                    modified_vars.append(vardict[var][0])
                    # x.func = Y -> func'(var) = if var==x then Y else func(var)
                    y = If(free_var==vardict[var][0],interpret_ops(op2), funcdict[func][0](free_var))
                    func_update(func)
                    x = funcdict[func][0](free_var)
                    logging.info('Mutation: %s = %s' %(x,y))
                    AddAxiom((free_var,),x == y)
                    for i in recdefdict.keys():
                        func_update(i)
                    for i in recdefdict.keys():
                        if i[:2] != 'SP':
                            interpret_recdef(recdefdict[i][2])          #interpret_recdef will make a defn for our recfunction, as well as its support



    else:
        raise Exception('Assignment/mutation takes two arguments: (:= x y). Given: %s' %list)


#-------------------------(12)-------------------------------------------
def interpret_recdef(list):
    #Specifically for RecDef, not calls to recursive functions (see interpret_recfunc (14) for this).
    #In a program, for each RecFunction, there should only be one of these.
    operator, operands = list[0], list[1:] 
    #format is (RecDef (function (x) (y)...) (recursive definition))
    op1, op2 = operands
    if op1[0] in recdefdict.keys():
        #......................................................
        if op1[0][:2]!= 'SP':
            func, spfunc, vars = op1[0], 'SP'+op1[0], op1[1:]
            s1 = recdefdict[spfunc][0]
            s2 = [interpret_ops(v) for v in vars]
            s3 = support(op2)
            logging.info('Adding support of recdef: (%s, %s, ,%s )' %(s1,s2,s3))
            AddRecDefinition(s1,*s2,s3)
        #..........................................................

        
        #func, vars = op1[0], op1[1:]
        #printf('AddRecDefn~~>',recdefdict[func][0],*[interpret_ops(v) for v in vars],interpret_ops(op2))
        a1 =recdefdict[func][0]
        a2 = [interpret_ops(v) for v in vars]
        a3 = interpret_ops(op2)
        logging.info('Adding recdef: (%s, %s, ,%s )' %(a1,a2,a3))
        #printf('recdef'-)
        AddRecDefinition(a1,*a2,a3)
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
    return SetUnion(*[interpret_ops(op) for op in operands])

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

#---------------------------------(20)------------------------------------------
def interpret_ismember(list):                                                                                   #new
    operator, operands = list[0], list[1:]
    if len(operands) == 2:
        return IsMember(interpret_ops(operands[0]),interpret_ops(operands[1]))
    else:
        raise Exception('(IsMember x Y) checks is x is a member of set Y.')


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


#--------------------Find Support--------------------------------------------------
def support(list):
    #print('list for supoport----->',list)
    if type(list) == str or len(list)==1:
        return support_basics(list)
    operator = list[0]
    if operator == '=' or operator == 'IsMember' or operator =='IsSubset' or operator == '!=':
        return support_binrel(list)
    elif operator == 'not' or operator == 'Not':
        return support_not(list)
    elif operator == 'ite':
        return support_ite(list)
    elif operator == 'and' or operator == 'And' or operator == 'not' or operator == 'Not':
        return support_and(list)
    #elif operator == 'RecDef':
    #    return support_recdef(list)
    elif operator in funcdict.keys() or operator in recdefdict.keys():
        return support_func(list)

def support_basics(list):   #Support of var/const is the empty set
    if type(list) == str:             
        x = list                      
    else:
        x = list[0]
    if x == 'True' or 'False' or 'EmptySet' or (x in vardict.keys()):
        return fgsetsort.lattice_bottom
    else:
        raise Exception('support basics failure')

def support_func(list):     #say func dict is just mutable functions.
    operator, operands = list[0], list[1:]

    terms = fgsetsort.lattice_bottom
    iterm = [interpret_ops(t) for t in operands]
    for i in iterm:
        terms = SetAdd(terms, i)

    sp_terms = SetUnion(*[support(t) for t in operands])

    if list[0] in funcdict.keys():
        return SetUnion(terms,sp_terms)
    elif list[0] in recdefdict.keys():
        if list[0][:2] == 'SP':
            pp = [list[0]]+operands
        else:
           pp = ['SP'+list[0]]+operands
        return SetUnion(sp_terms, interpret_ops(pp))
        

def support_binrel(list):
    operator, operands = list[0], list[1:]
    if len(operands) == 2:
        term1, term2 = operands
        return SetUnion(support(term1),support(term2))

def support_not(list):
    operator, operands = list[0], list[1:]
    if operator == 'Not' or 'not':
        if len(operands)==1:
            return support(operands[0])

def support_and(list):                                  #also or
    operator, operands = list[0], list[1:]

    if operator == 'And' or 'and' or 'Or' or 'or':
        return SetUnion(*[support(t) for t in operands])

# def support_or(list):
#     return support_and(list)

def support_ite(list):
    operator, operands = list[0], list[1:]
    if operator == 'ite':
        if len(operands) == 3:
            op1, op2, op3 = operands
            x = If(interpret_ops(op1), SetUnion(support(op1),support(op2)), SetUnion(support(op1),support(op3)))    #...
            return x      #?!


#----------------------------------------------------------------------------------
#Below we club together everything so far to get a vc function.
#We assume input is given in the righ format. Need to handle issues better. Will do later.
init_recdef = dict()
def vc(list):
    transform = []
    code_line = [create_input(i) for i in list]
    #printf(code_line)
    printf('done creating input list')
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
            spname = 'SP'+i[1][0]
            if name in recdefdict.keys():
                z3_name, type, des, subfunc,counter = recdefdict[name]
                recdefdict[name] = (z3_name, type, i, sub_functions(i), counter)
                init_recdef[name] = (z3_name, type, i,name)
                init_recdef[spname] = recdefdict[spname]
            else:
                raise Exception('Bad RecDef')
            interpret_ops(i)
        elif tag == ':=' and len(i[1])==3: #i.e add axiom
            interpret_ops(i)
        else:
            intops = interpret_ops(i)
            logging.info('Line of code: %s' %intops)
            transform.append(interpret_ops(i))
    print('done preprocessing')
    #frame condition:#assume just 1 var for now
    mv = [*set(modified_vars)]
    mod_set = fgsetsort.lattice_bottom
    for i in mv:
        modif_set = SetAdd(mod_set,i)
    for i in recdefdict.keys():
        if i[:2]=='SP':
            pass
        else:
            logging.info('Frame assumptions:')
            #printf('..................',((free_var,), Implies(And(init_recdef[i][0](free_var),IsSubset(SetIntersect(set1,init_recdef['SP'+i][0](free_var)),fgsetsort.lattice_bottom)),recdefdict[i][0](free_var))))
            a = Implies(IsSubset(SetIntersect(mod_set,init_recdef['SP'+i][0](free_var)), fgsetsort.lattice_bottom),init_recdef[i][0](free_var) == recdefdict[i][0](free_var))
            logging.info(a)
            AddAxiom((free_var,), a)
            b = Implies(IsSubset(SetIntersect(mod_set,init_recdef['SP'+i][0](free_var)), fgsetsort.lattice_bottom),init_recdef['SP'+i][0](free_var) == recdefdict['SP'+i][0](free_var))
            logging.info(b)
            AddAxiom((free_var,), b)

    goal =  Implies(And(precond,*[t for t in transform]),postcond)
    printf(goal)
    logging.info('Pre: %s' % precond)
    logging.info('Tranform: %s' % transform)
    logging.info('Post: %s' % postcond)
    np_solver = NPSolver()
    np_solver.options.depth = 2
    solution = np_solver.solve(goal)
    if not solution.if_sat:
        logging.info('goal is valid')
        print('goal is valid')
    else:
        logging.info('goal is invalid')
        print('goal is invalid')
    return goal




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