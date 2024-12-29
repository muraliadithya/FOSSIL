from z3 import And, Or, Not, Implies, If
from z3 import IsSubset, IsMember, SetIntersect, SetUnion, SetAdd, EmptySet, IntSort, SetDifference, SetDel
from naturalproofs.uct import fgsort, fgsetsort, intsort, intsetsort, boolsort
from naturalproofs.decl_api import Const, Var, Function, AddRecDefinition, AddAxiom
from naturalproofs.prover import NPSolver, get_foreground_terms
from naturalproofs.pfp import make_pfp_formula
import naturalproofs.proveroptions as proveroptions
from naturalproofs.AnnotatedContext import default_annctx
from naturalproofs.prover_utils import instantiate, make_recdef_unfoldings
from preprocessing import ml_to_sl, remove_comments, create_input, sl_to_fl_commands
from z3 import simplify
import time

immutables = ['=', 'not', 'or', 'and', '=>', 'IsMember', 'IsSubset', 'SetAdd', 'SetDel','SetIntersect', 'SetUnion', '<', '>', '>=', '<=', '+', '-']

# --------------------GLOBAL-------------------------------
vardict = {'nil' : {'z3name': Const('nil', fgsort),'z3type': fgsort,'type': 'Loc', 'counter': None, 'is_free_var': False}}                                                        # Dictionary to store variables
funcdict = {}                                                       # Dictionary to store functions
recdefdict = {}                                                     # Dictionary for the recusive definitions
freevardict = {'Loc': 0,'SetLoc': 0,'Int': 0,'SetInt': 0,'Bool': 0} # Will add free vars based on max arity of fn. Tracks number so far
alloc_set = fgsetsort.lattice_bottom                                #
has_mutated = 0                                                     # If == 1, need to update recfns
in_call = 0
number_of_function_calls = 0                                        #
lemma_set = set()                                                   # lemmas to be instantiated
lemma_description = []                                              #
defaultdict = {'Loc': vardict['nil']['z3name'],'Int': -1 , 'Bool': False  ,'SetLoc': fgsetsort.lattice_bottom,'SetInt': intsetsort.lattice_bottom}
statesdict = {}
latest_state = 'initial'
tracked_vars = set()
tracked_vars.add('nil')
is_nil = vardict['nil']['z3name']
modified_vars = fgsetsort.lattice_bottom
transform = []
check_side_conditions = 1                                           # default: check all obligations 
inputvarset = set()                                                 # set of input variables to the program. Given as a set of strings.
                                                                    # the user is not allowed to assign to this
inputs_of_call = {}                                                   
outputs_of_call = {}
in_old = 0
old_ref = 'initial'                                                 
lemmalist = []
framelist = []
instantiation_pairs = {}
dereferencedlist = []
boundarylist = []
trace = [ vardict['nil']['z3name']]
pointerdict = {}
all_locs = []
final_vc = []
on_the_fly = False
np_solver = NPSolver()
depth = 2
np_solver.options.depth = depth
typevardict = {'Loc': set(), 'SetLoc': set(), 'Int': set(), 'SetInt': set(), 'Bool': set() }   # stores the variables/consts of each type
pointerlist = []
frame_rules = []
support_map = {}
# MODES
footprint = {}
extended_footprint = {}
fo_abstractions = set()
frame_abstractions = set()
all_instantiations = []
pre_tag = 0
testing_mode = 0
depth1_mode = 1
depth2_mode = 2
mode = 0
number_of_vcs = 0
instantiation_pairs_support = {}

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
        vardict[name] = {'z3name': z3_var,'z3type': z3_type, 'type': input_type,'counter': 0, 'is_free_var': False}
        typevardict[input_type].add(name)

    elif tag == 'Const':
        z3_var = Const(name, z3_type)
        vardict[name] = {'z3name': z3_var,'z3type': z3_type, 'type': input_type, 'counter': None, 'is_free_var': False}
        typevardict[input_type].add(name)
    else:
        raise Exception(f'Invalid Var/Const tag {varinfo}')


def func_parser(funcinfo):
    '''Adding to func_dict. Input of the form [TAG, NAME, type, type....., output_type]
    All input types are the same.
    
    '''
    tag  = funcinfo[0]
    if tag == 'RecFunction':
        name, type_info =  funcinfo[1], funcinfo[2:]
    elif tag == 'Function':
        name, type_info=  funcinfo[1], funcinfo[2:]

    # The following looks at a function's input types and creates free variables if necessary.
    # If the max no. of Loc in a fn is k, there will be k free_Loc variables created.
    type_of_inputs = type_info[0]
    type_of_output = type_info[-1]
    for input_type in type_info[:-1]:
        if not(input_type == type_of_inputs):
            raise Exception('A function input types must be the same')
        
    no_of_inputs = len(type_info) - 1
    no_of_freevars_sofar = freevardict[type_of_inputs]
    if no_of_inputs > no_of_freevars_sofar:
        for i in range(no_of_freevars_sofar,no_of_inputs):
            vardict['free_'+type_of_inputs+str(i)] = {'z3name': (Var('free_'+type_of_inputs+str(i), type_parser(type_of_inputs))),
                                                      'z3type': type_parser(type_of_inputs), 'type': type_of_inputs,'counter': 0, 
                                                      'is_free_var': True}
        freevardict[type_of_inputs] = no_of_inputs
    # assuming only one input type per function.


    z3_type = [type_parser(x) for x in type_info]
    if tag == 'Function':
        z3_func = Function(name+'0', *z3_type)
        funcdict[name] = {'macro': lambda free_var, z3_func = z3_func: z3_func(free_var), 'z3type': z3_type, 'counter': 0, 'input_type': type_of_inputs, 'output_type': type_of_output, 'no_inputs': no_of_inputs}

        if type_of_output == 'Loc':
            pointerdict[name] = funcdict[name]['macro']


        global pointerlist
        if type_of_inputs == type_of_output:
            if type_of_output == 'Loc':
                pointerlist.append(name)

    elif tag == 'RecFunction':
        # The following creates function (to be 'defined' later)
        z3_func = Function(name+'0', *z3_type)
        recdefdict[name] = {'z3name': z3_func, 'z3type': z3_type, 'description': [],
                                'counter': 0, 'input_type': type_of_inputs, 'output_type': type_of_output, 'no_inputs': no_of_inputs,
                                'id': None} 
        
        # The following defines the support of the recursive function.
        if name[:2]== 'SP':
            raise Exception('Recursive functions must not start with SP')
        else:
            # support_map is of the form { 'SPRecfunc1s': 'SPA', 'SPRecfunc2': 'SPA', 'SPRecfunc3': 'SPB' ...}
            # For recfunction A, if SPA is either in support_map.values() or not in support_map.keys(), define SPA.
            # else map SPA to its value in support_map
            spname = 'SP'+ name
            if spname in support_map2.keys():
                recdefdict[spname] = recdefdict[support_map2[spname]]
            else:
                typelist = [type_parser(i) for i in type_info[:-1]]
                z3_sptype = [*typelist,fgsetsort]     
                z3_spfunc = Function(spname+'0',*z3_sptype)
                recdefdict[spname] = {'z3name': z3_spfunc, 'z3type': z3_sptype, 'description': [],
                                            'counter': 0,'input_type': type_of_inputs,'output_type': 'SetLoc','no_inputs': no_of_inputs,
                                            'id': None}

    else:
        raise Exception(f'Tag error. Given: {tag} in {funcinfo}')


def var_update(name):
    '''Update variables and counters'''
    if (name in vardict):
        if (name in inputvarset):
            raise Exception(f' Input variable to the program is assigned to / allocd to ')
        counter, z3_type = vardict[name]['counter'], vardict[name]['z3type']
        counter_new = counter+1
        var_new = Var(name+str(counter_new), z3_type)
        vardict[name]['z3name'], vardict[name]['counter'] = var_new, counter_new

        if vardict[name]['type'] == 'Loc':
            all_locs.append(var_new)
            
    else:
        raise Exception(f' Undeclared variable {name}')

def func_update(name):
    '''Update functions(and rec functions) and counters'''
    if name in funcdict:
        counter =  funcdict[name]['counter']
        counter_new = counter+1
        funcdict[name]['counter'] =  counter_new
    else:
        raise Exception(f' Undeclared function {name}')

def recfunc_update():
    """
    Creates new recursive Function names. Then defines them.
    """
    for name in recdefdict:
        if name in support_map2.keys():
            pass
        else:
            z3_type, counter = recdefdict[name]['z3type'], recdefdict[name]['counter']
            counter_new = counter+1
            func_new = Function(name+str(counter_new), *z3_type)
            recdefdict[name]['z3name'], recdefdict[name]['counter'] = func_new, counter_new

    for name in support_map2.keys():
        recdefdict[name] = recdefdict[support_map2[name]]

    global has_mutated
    has_mutated = 0

    for name in recdefdict:
        if name in support_map2.keys():
            pass
        else:
            interpret_recdef(recdefdict[name]['description'])

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
    if operator == 'antiSp':
        return interpret_antisp(iplist)


    raise Exception(f'Invalid Tag {operator} in {iplist}')

#---------(1)--------------
def interpret_basics(iplist):
    '''Interpret basic inputs'''

    global in_call

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
        if in_call == 1:    # By construction, all variables in the call must be in one of the two ifs; 
            if x in inputs_of_call.keys():
                        return inputs_of_call[x]
            elif x in outputs_of_call.keys():
                        return outputs_of_call[x]       
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
    elif len(operands) > 2:
        x= []
        for i in range(len(operands)-1):
            x.append(interpret_ops(operands[i]) == interpret_ops(operands[i+1]))
        return (And(*x))
    raise Exception(f'Equality check(=) takes >=two arguments. Given {iplist}')

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

def interpret_assign(iplist, check_obligations = 1):
    '''(assign X Y) where X can either be a variable or a mutation
        x:= Y will update x (increment counter to make an updated variable) to be Y
        (func x) := Y will update the function func' to say -> 
                        if arg is x then Y else (func arg) '''
    global number_of_function_calls
    global np_solver
    global lemma_set
    global transform
    global alloc_set

    global tracked_vars
    global boundarylist
    # MODES
    # global mode

    operands = iplist[1:]
    if len(operands)==2:
        lhs, rhs = operands

        if isinstance(lhs,str) and isinstance(rhs,str):    
            pass
        else:                                                   # => lhs or rhs is y.f
            if mode == testing_mode:
                global dereferencedlist
                global boundarylist
                global latest_state
                if not(isinstance(lhs,str)):
                        dereferencedlist.append(interpret_ops(lhs[1]))
                if not(isinstance(rhs,str)):
                    if rhs[1] in vardict.keys():
                        if vardict[rhs[1]]['type'] == 'Loc':
                            dereferencedlist.append(interpret_ops(rhs[1]))
        
            obligation = IsSubset(SetUnion(support(lhs),support(rhs)),alloc_set)    # change to the form in testing_mode above?
            if (check_obligations == 1) and not(cl_check(np_solver,lemma_set,transform,obligation)):
                print(f'Obligation not proven. Assuming obligations: {iplist}')

        if (isinstance(lhs,str) and (lhs in vardict)) or (len(lhs)==1 and (lhs[0] in vardict)): # LHS is a variable
            interpreted_rhs = interpret_ops(rhs)
            var_update(lhs)    
            interpreted_lhs = interpret_ops(lhs)

            if mode == testing_mode:
                    if vardict[lhs]['type'] == 'Loc':
                        boundarylist.append(interpreted_lhs)
                        tracked_vars.add(lhs)
                        add_instantiation_pairs_support(latest_state, [interpreted_lhs])

            return interpreted_lhs==interpreted_rhs
        if lhs[0] in funcdict:  # if mutation
            global modified_vars
            func = lhs[0]
            for i in range(1,len(lhs)):
                argument = interpret_ops(lhs[i])
                if number_of_function_calls == 0:
                    state = 'initial'
                else:
                    state = 'after_call_'+str(number_of_function_calls)
                modified_vars = SetAdd(modified_vars, argument)

            x = funcdict[func]['macro']
            y = interpret_ops(rhs)
            new_macro = lambda free_var, argument = argument, y = y, x = x: If(free_var == argument, y, x(free_var))
            func_update(func)
            funcdict[func]['macro'] = new_macro

            if funcdict[func]['output_type'] == 'Loc':
                pointerdict[func] = funcdict[func]['macro']

            global has_mutated
            has_mutated = 1 # indicates recdefs need to be updated. Will do when necessary.
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
        func, args = func_info[0], func_info[1:]

        if func_info[0] in support_map.keys():
            pass
        else:
            a1 =recdefdict[func]['z3name']
            a2 = [interpret_ops(v) for v in args]
            a3 = interpret_ops(func_definition)

            return_id = AddRecDefinition(a1,tuple(a2),simplify(a3))
            recdefdict[func_info[0]]['id'] = return_id

def interpret_func(iplist):
    '''(func args) -> func(args)
        Used for non recursive functions'''
    global in_old
    global old_ref

    if len(iplist) != 2:
        raise Exception('Invalid number of arguments on function')
    operator, operands = iplist[0], iplist[1]

    if in_old == 0:
        return funcdict[operator]['macro'](interpret_ops(operands))
    else:
        return statesdict[old_ref]['funcs'][operator](interpret_ops(operands))

def interpret_recfunc(iplist):
    '''(recfunc args) -> recfunc(args)
        Specifically for calling a fn, not recursive definitions. When a recfunc is called,
        need to check if it has been updated in accordance with mutations'''
    operator, operands = iplist[0], iplist[1:]
    global has_mutated
    global lemma_description
    if has_mutated == 1:        # if a function has been changed and we see a recfunc called, we update the defn, then apply the recfn.
        recfunc_update()
        instantiate_lemma()

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

    return emptyless_union([interpret_ops(op) for op in operands])

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
    global in_call
    global number_of_function_calls
    global in_old   
    global old_ref    
    
    in_old = 1

    operands = iplist[1:]
    if len(operands) == 1:
        func, arguments = operands[0][0], operands[0][1:]
        if func in recdefdict:
            if in_call == 1:
                old_ref = 'before_call_'+str(number_of_function_calls)
                to_return =  statesdict[old_ref]['recdefs'][func](*[interpret_ops(op) for op in arguments])      
            
                old_ref = 'initial'
            else:
                to_return = statesdict['initial']['recdefs'][func](*[interpret_ops(op) for op in arguments])
            
            in_old = 0

            return to_return
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

def function_call(iplist, check_obligations = 1):  # add a var update somewhere here in case someone uses an allocated var in return?
    '''
    iplist = ['call', actual_input_vars, actual_output_vars, formal_input_vars, formal_output_vars, pre_call, post_call]
    '''
    global in_call
    in_call = 1
    operands = iplist[1:]
    if len(operands) == 6:
        # frame_rules
        global frame_rules
        global alloc_set
        global number_of_function_calls
        global has_mutated
        global lemma_description
        global np_solver
        global check_side_conditions
        global transform
        # MODES
        global fo_abstractions

        number_of_function_calls = number_of_function_calls + 1

        actual_ip, actual_op, formal_ip, formal_op, pre_call, post_call = operands

        if not(len(actual_ip) == len(formal_ip)) or not(len(actual_op) == len(formal_op)):
            raise Exception ('Bad function call')           # expand

        global inputvarset

        for elt in actual_op:   # enforce that input variables to the program are not in this as we do not allow assignments to those
            if isinstance(elt, str):            # if inputvarset elt is in actual_ip - heap
                if elt in inputvarset:
                    raise Exception(f' Bad function call {iplist}.  Input variable {elt} of program is assigned to.')
            elif len(elt) == 1:
                if elt[0] in inputvarset:                        
                    raise Exception(f' Bad function call {iplist}.  Input variable {elt} of program is assigned to.')
            else:
                raise Exception( f'Bad input {elt} in {iplist}')


        global inputs_of_call
        inputs_of_call = {}
        global outputs_of_call
        outputs_of_call = {}

        for i in range(len(actual_ip)):
            ac_elt = actual_ip[i]
            fm_elt = formal_ip[i]

            z3_ac_elt = vardict[ac_elt]['z3name']

            inputs_of_call[fm_elt] = z3_ac_elt
        
        for i in range(len(actual_op)):
            ac_elt = actual_op[i]
            fm_elt = formal_op[i]

            var_update(ac_elt)
            z3_ac_elt = vardict[ac_elt]['z3name']

            # MODES
            if mode == testing_mode:
                if vardict[ac_elt]['type'] =='Loc':
                    tracked_vars.add(ac_elt)

            outputs_of_call[fm_elt] = z3_ac_elt


        if has_mutated == 1:
            recfunc_update()
            instantiate_lemma()
            snapshot('before_call_'+str(number_of_function_calls))
            sp_pre = support(pre_call)
            pre = interpret_ops(pre_call)
            
            if number_of_function_calls == 1:
                before = 'initial'
                now = 'before_call_'+str(number_of_function_calls)
            else:
                before = 'after_call_'+str(number_of_function_calls-1)
                now = 'before_call_'+str(number_of_function_calls)

            global modified_vars
            frame_rule(before, now)                     # frame rules between the previous call and the beginning of the new one. incorportates the modified set between
            modified_vars = fgsetsort.lattice_bottom    # reset modified locations to start tracking for the next call to call frame rules.

        else:
            snapshot('before_call_'+str(number_of_function_calls))
            add_instantiation_pairs('before_call_'+str(number_of_function_calls), False)
            sp_pre = support(pre_call)
            pre = interpret_ops(pre_call)            

        # obligation checking
        obligation = And(pre, IsSubset(sp_pre,alloc_set))

        if (check_obligations == 1) and not(cl_check(np_solver,lemma_set,transform, obligation)):
            print(f'Could not prove the preconditions for the function call: {iplist}')
        old_alloc_rem = SetDifference(alloc_set,sp_pre)

        for i,elt in funcdict.items():
            new_unint_fn = Function(i+'_unint_'+str(number_of_function_calls),*elt['z3type'])
            x = elt['macro']

            new_macro = lambda free_var, sp_pre = sp_pre, x = x, new_unint_fn = new_unint_fn : If(IsMember(free_var,sp_pre), new_unint_fn(free_var), x(free_var))
            func_update(i)
            elt['macro'] = new_macro

            # MODES
            if mode == testing_mode:
                if elt['output_type'] == 'Loc':
                    pointerdict[i] = elt['macro']

        recfunc_update()
        instantiate_lemma()
        snapshot('after_call_'+str(number_of_function_calls))
        before = 'before_call_'+str(number_of_function_calls)
        now = 'after_call_'+str(number_of_function_calls)
        frame_rule(before, now, 1, sp_pre)  # modified set is the retained heap
        sp_post = support(post_call)                    
        alloc_set = SetUnion(old_alloc_rem,sp_post)
        to_assume = interpret_ops(post_call) 
        in_call = 0 
        return And(pre, to_assume, SetIntersect(old_alloc_rem,sp_post) == fgsetsort.lattice_bottom)
    raise Exception('Bad function call')
    
def interpret_alloc(iplist):
    operands = iplist[1:]
    if len(operands) == 1:
        x = operands[0]
        if isinstance(x,str):
            pass
        elif isinstance(x[0],str):
            x = x[0]
        else:
            raise Exception(f'Bad alloc {iplist}. Alloc should be of the form (alloc x)')
    global alloc_set
    var_update(x)
    global mode
    if mode == testing_mode:
        global dereferencedlist
        global tracked_vars
        dereferencedlist.append(vardict[x]['z3name'])
        if vardict[x]['type'] =='Loc':
            tracked_vars.add(x)

    alloc_var = vardict[x]['z3name']
    to_return = []
    to_return.append(Not(IsMember(alloc_var, alloc_set)))
    for i, elt in funcdict.items():
        to_return.append(elt['macro'](alloc_var) == defaultdict[elt['output_type']])

    alloc_set = SetAdd(alloc_set, alloc_var)

    return And(*[to_return])

def interpret_free(iplist, check_obligations = 1):
    operands = iplist[1:]

    global np_solver
    global lemma_set
    global transform
    global alloc_set

    obligation =  IsMember(interpret_ops(operands), alloc_set) 

    if (check_obligations == 1) and not(cl_check(np_solver,lemma_set,transform,obligation)):
        print(f'Obligation not proven. Assuming obligations: {iplist}')
    if len(operands) == 1:
        x = operands[0]
        if isinstance(x,str):
            pass
        else:
            x = x[0]
    alloc_set = SetDel(alloc_set, vardict[x]['z3name'])

def interpret_antisp(iplist):
    '''(antiSp X) -> X '''
    operands = iplist[1:]
    if len(operands) != 1:
        raise Exception(f'not operator is unary. Given {iplist}')
    return interpret_ops(operands[0])

def instantiate_lemma(prove = False):        #this 'instantiates' a lemma
    
    global lemma_set                    # (lemma (args) (body) )
    global lemma_description
    global lemmalist

    lemmalist = []

    if prove:
        already_proven_lemmas = []

    global np_solver

    for operands in lemma_description:
        if len(operands)==2:
            argop, bodyop   = operands
            arglist = []
            for i in argop:
                arglist.append(interpret_basics(i))

            argtuple = tuple(arglist)
            body = interpret_ops(bodyop)
            
            # MODES
            if mode == testing_mode:
                lemma_id = AddAxiom(argtuple, simplify(body))
                lemmalist.append(lemma_id)
            
            if prove:
                isproven, already_proven_lemmas =  prove_lemma(np_solver, bodyop,lemma_set, already_proven_lemmas)
                if isproven:
                    print('Lemma is valid')
                else:
                    print('Lemma not proven')
            lemma_set.add((argtuple,body))

        else:
            raise Exception(f'lemma format (args) (body). Given {operands}')

def side_conditions_update(iplist):
        if len(iplist) == 2:
            if iplist[1] == 'False' or iplist[1] == 'false':
                return 0
            elif iplist[1] == 'True' or iplist[1] == 'true':
                return 1
            else:
                raise Exception(f':side-condition should be followed only by True or False. Error in: {iplist}')
        else:
            raise Exception(f' Wrong number of operands in {iplist}')

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
    if operator == 'Sp':
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

    list_of_sets = [support(t) for t in operands]
    sp_terms = emptyless_union(list_of_sets)

    if iplist[0] in funcdict:
        terms = fgsetsort.lattice_bottom
        term_list = [interpret_ops(t) for t in operands]
        for i in term_list:
            terms = SetAdd(terms, i)
        
        return emptyless_union([terms,sp_terms])
    if iplist[0] in recdefdict:
        if iplist[0][:2] == 'SP':
            ipp = interpret_ops(iplist)
        else:
            pp = ['SP'+iplist[0]]+operands
            ipp = interpret_ops(pp)
        return emptyless_union([sp_terms, ipp])
    raise Exception(f'Invalid support on functions in {iplist}')


def support_immut(iplist):
    '''Support of immutables (see beginning of the file to see the immutables)'''
    operands = iplist[1:]
    return emptyless_union([support(t) for t in operands ])

def support_ite(iplist):
    '''Support of if then else'''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'ite' and len(operands) == 3:
        op1, op2, op3 = operands
        x = If(interpret_ops(op1), emptyless_union([support(op1),support(op2)]), emptyless_union([support(op1),support(op3)]))
        return x      #?!
    raise Exception(f'Invalid if-then-else support given in {iplist}')

def support_support(iplist):
    '''Support of support -> support'''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'Sp' and len(operands)==1:
        return support(operands[0])
    raise Exception(f'Support is a unary operator. Invalid support {iplist}')

def support_old(iplist):
    '''
    # (Sp (Old (recfunc X))) -> (Old (Sp (recfunc X)))
    (Sp (Old (recfunc X))) -> empty
    '''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'Old' and len(operands)==1:
        recfn, args = operands[0][0], operands[0][1:]
        if recfn in recdefdict:
            return fgsetsort.lattice_bottom                     # assumed antisp brackets around old.

        raise Exception(f'Invalid rec def in support old operation {iplist}')
    raise Exception(f'Invalid tag in support old {iplist}')

def support_antisp(iplist):
    '''(Sp (antiSp X)) -> EmptySetLoc'''
    operator, operands = iplist[0], iplist[1:]
    if operator == 'antiSp' and len(operands)==1:
        return fgsetsort.lattice_bottom
    raise Exception(f'Invalid tag in support old {iplist}')


def snapshot(state):
    '''Store the current recursive definitions and functions under state'''

    global lemmalist
    global latest_state
    global tracked_vars
    
    if state in statesdict.keys():
        raise Exception(f'{state} already a snapshot state')
    
    funcs = {}
    for name, elt in funcdict.items():
        funcs[name] = elt['macro']

    recdefs = {}
    recdef_ids = []
    support_ids = []
    for name, elt in recdefdict.items():
        recdefs[name] = elt['z3name']
        
        if name in support_map2.keys():
            pass
        else:
            if name[:2] == 'SP':
                support_ids.append(elt['id'])
            recdef_ids.append(elt['id'])
    for name in support_map2.keys():
        recdefs[name] = (recdefdict[support_map2[name]])['z3name']

    vars = {}                               # vars also stored for use in 'Old'
    locs = []
    for name, elt in vardict.items():
        vars[name] = elt['z3name']
        if elt['type'] == 'Loc' and (not (elt['is_free_var'])):
            if name in tracked_vars:
                locs.append(elt['z3name'])

    lemma_id_list = []
    for i in lemmalist:
        lemma_id_list.append(i)

    statesdict[state] = {'funcs': funcs, 'recdefs': recdefs, 'vars': vars,
                          'recdef_ids': recdef_ids ,  'lemma_ids': lemma_id_list, 'loc_vars': locs, 'support_ids': support_ids}   
    latest_state = state


def cl_check(solver,lemmas,assumptions, obligation, is_final = False):
    '''Return true if the solver can prove the obligation with the set of assumptions and lemmas'''
    global number_of_vcs
    global trace
    number_of_vcs = number_of_vcs +1
    global frame_rules
    global on_the_fly
    support_only = False

    # MODES
    if mode == testing_mode:
        global instantiation_pairs
        if on_the_fly:
            np_solver.options.terms_to_instantiate = instantiation_pairs.items()
    
    if len(frame_rules) == 0:
        vc_formula = Implies(And(*assumptions), obligation)
    else: 
        vc_formula =  Implies(And(*frame_rules,*assumptions), obligation)

    if on_the_fly:
        solution = solver.solve(simplify(vc_formula), lemmas)
        if not solution.if_sat:
            return True
        return False
    else:
        global final_vc
        final_vc.append(simplify(vc_formula))
        if is_final:
            np_solver.options.terms_to_instantiate = instantiation_pairs.items()
            if mode == testing_mode:
                lemmas = set()
            solution = solver.solve(simplify(And(*final_vc)), lemmas)

            if not solution.if_sat:
                return True
            return False
        return True


def prove_lemma( solver, lemma_body, lemmas, already_proven_lemmas = []):
    '''Prove lemma
    body:   [=>, A, B]  A=>B
    '''
    global depth
    global lemmalist
    lem = interpret_ops(lemma_body)
    print('this is the lemma:', lem)

    locs_in_lemma = get_foreground_terms(lem, default_annctx)
    locs_in_lemma.add(vardict['nil']['z3name'])
    locs_in_lemma_pointers = set()
    for f in pointerdict.values():
        for i in locs_in_lemma:
            if not(i == is_nil):
                locs_in_lemma_pointers.add(f(i))
    locs_in_lemma = locs_in_lemma.union(locs_in_lemma_pointers)
    # print('These are the terms instantiated upon to prove lemmas:', locs_in_lemma)
    # print('Number of lemmas proven already:', len(already_proven_lemmas))
    pfp_formula = make_pfp_formula(lem)
    # print('This is the pfp formula', pfp_formula)

    terms_to_instantaite_lemma = [(i, locs_in_lemma) for i in statesdict['for_lemmas']['recdef_ids']]
    solver.options.terms_to_instantiate = terms_to_instantaite_lemma + already_proven_lemmas

    solution = solver.solve(pfp_formula, lemmas)
    if not solution.if_sat:
        solver.options.depth = depth
        already_proven_lemmas = already_proven_lemmas + [(i, locs_in_lemma) for i in lemmalist]
        return True, already_proven_lemmas
    
    # print('lemma not proven')
    solver.options.depth = depth
    return False, already_proven_lemmas

def frame_rule(state1, state2, use_alt = 0, alt_mod_set = fgsetsort.lattice_bottom, use_local = 0):
    '''
    Adds frame rules between state1 and state2 (assumed to be consecutive)
    For each recursive function F: If x not in modified_set Intersection Support_of_F1(x), then F1(x) = F2(x).
    '''
    s1 = statesdict[state1]['recdefs']
    s2 = statesdict[state2]['recdefs']
    if use_alt == 0:
        global modified_vars
        modified_set = modified_vars
    else:
        modified_set = alt_mod_set

    # MODES
    if mode == testing_mode:
        global framelist
        framelist = []
    for name in s1.keys():
        if name[:2] == 'SP':
            pass
        else:
            fv_used = []
            for j in range(recdefdict[name]['no_inputs']):
                fv_used.append(vardict['free_' + recdefdict[name]['input_type'] + str(j)]['z3name'])

            recdef_frame = Implies(SetIntersect(modified_set,s1['SP'+name](*fv_used)) ==  fgsetsort.lattice_bottom
                        ,s1[name](*fv_used) == s2[name](*fv_used))
                            
            recdef_ax = AddAxiom((*fv_used,), simplify(recdef_frame))
            if mode == testing_mode:    
                framelist.append(recdef_ax)

            if ('SP' + name) in support_map2.keys():
                pass
            else: 
                support_frame = Implies(SetIntersect(modified_set,s1['SP'+name](*fv_used)) == fgsetsort.lattice_bottom
                            ,s1['SP'+name](*fv_used) == s2['SP'+name](*fv_used))              
                support_ax = AddAxiom((*fv_used,), simplify(support_frame))
                if mode == testing_mode:    
                    framelist.append(support_ax)

    if mode == testing_mode:
        global instantiation_pairs
        add_instantiation_pairs(state2)
        framelist = []


def replace_var(the_map, iplist ):
    '''
    the_map -> {'x': 'm_x','y': 'm_y'...}
    return iplist[x<-m_x, y<-m_y, ...]
    '''
    new_list = []
    map_keys = the_map.keys()
    for elt in iplist:
        if isinstance(elt, str):
            if elt in map_keys:
                new_list.append(the_map[elt])
            else:
                new_list.append(elt)
        else:
            new_list.append(replace_var(the_map, elt))
    return new_list

def store_inputvars(iplist):
    '''
    iplist = [Program, [inputvars], [outputvars]]

    '''    
    if len(iplist) == 3:
        for i in iplist[1]:
            inputvarset.add(i)


def emptyless_union(list_of_sets):
    '''
    Return the union of the sets
    '''
    ret = []
    for i in list_of_sets:
        if i ==  fgsetsort.lattice_bottom:
            pass
        else:
            ret.append(i)
    if len(ret) == 0:
        return fgsetsort.lattice_bottom
    elif len(ret) == 1:
        return ret[0]
    return SetUnion(*ret)

#---------------------------------
def make_support_map(iplist):
    '''
    iplist = [EqSp, [A, [A1, A2...]] [B, [B1,...]] ... ]  
    Update the support_map dictionary with key:values SPAi:SPA, SPBi:SPB, ...
    '''
    ops = iplist[1:]
    
    for elt in ops:
        base_fn, related_fns = elt
        for fn in related_fns:
            support_map2['SP' + fn] = 'SP' + base_fn

def add_instantiation_pairs(state, mutated = True):
    """
    'state' is a key of statesdict. This contains a list of location variables,
    recdefs, and lemmas.
    """
    global framelist
    global instantiation_pairs
    global dereferencedlist

    id_list = []
    for i in statesdict[state]['recdef_ids']:
        id_list.append(i)
    for i in statesdict[state]['lemma_ids']:
        id_list.append(i)

    loc_set = set(statesdict[state]['loc_vars'])    # Current vars
    extended_loc = set()
    for f in pointerdict.values():
        for i in loc_set:
            if not(i == is_nil):
                extended_loc.add(f(i))
    extended_loc = loc_set.union(extended_loc)  # current vars + pointers
    loc_and_deref = loc_set.union(set(dereferencedlist))
    if mutated:
        for i in id_list:
            instantiation_pairs[i] =  loc_and_deref
        for i in framelist:
            instantiation_pairs[i] = extended_loc
    else:
        for i in id_list:
            if i in instantiation_pairs.keys():
                instantiation_pairs[i] = (instantiation_pairs[i]).union(loc_and_deref)     

def add_instantiation_pairs_init(state):
    """
    'state' is a key of statesdict. This contains a list of location variables,
    recdefs, and lemmas.
    """
    global framelist
    global instantiation_pairs
    global dereferencedlist

    id_list = []
    # for i in framelist:
    #     id_list.append(i)
    for i in statesdict[state]['recdef_ids']:
        id_list.append(i)
    for i in statesdict[state]['lemma_ids']:
        id_list.append(i)

    loc_set = set(statesdict[state]['loc_vars'])    # Current vars
    extended_loc = set()
    for f in pointerdict.values():
        for i in loc_set:
            if not(i == is_nil):
                extended_loc.add(f(i))
    extended_loc = loc_set.union(extended_loc)  # current vars + pointers
    for i in id_list:
        instantiation_pairs[i] = extended_loc

def add_instantiation_pairs_support(state, vars):
    global instantiation_pairs
    support_ids = statesdict[state]['support_ids']
    for i in support_ids:
        if i in instantiation_pairs.keys():
            instantiation_pairs[i] = (instantiation_pairs[i]).union(set(vars))




def get_loc_vars_in_formula(ip):
    """
    Given a parsed input as a list (eg: ['next' ['x']]). Return the variable names. (eg: set('x')).
    """
    vars_in_formula = set()
    if isinstance(ip, str):
        if (ip in vardict.keys()) and (vardict[ip]['type'] == 'Loc'):
            vars_in_formula.add(ip)
    else:
        for i in ip:
            vars_in_formula = vars_in_formula.union(get_loc_vars_in_formula(i))
    return vars_in_formula



def vc(user_input, aux_mode=testing_mode, logic='sl', onthefly=False, weaken_alloc_check = 0):
    '''VC generation'''
    # MODE Use variable 'mode' to switch between the modes
    global mode
    mode = aux_mode
    global frame_rules
    global on_the_fly
    global np_solver

    on_the_fly = onthefly

    if mode == testing_mode:
        np_solver.options.instantiation_mode = proveroptions.manual_instantiation_finegrained
    elif mode == depth1_mode:
        np_solver.options.depth = 1
    elif mode == depth2_mode:
        np_solver.options.depth = 2
    else:
        raise Exception('Bad mode')


    start = time.time()
    if logic == 'sl':
        nc_uip = sl_to_fl_commands(ml_to_sl(remove_comments(user_input)))
    else:
        nc_uip = ml_to_sl(remove_comments(user_input))
    code_line = [create_input(i) for i in nc_uip]
    # return 'done parse'
    print('done creating input list')
    global alloc_set
    global lemma_set
    global check_side_conditions
    global modified_vars
    global transform
    global number_of_function_calls
    global has_mutated
    global support_map
    global support_map2
    global tracked_vars
    global instantiation_pairs

    support_map2 = {}
    global trace

    for i in code_line:
        tag = i[0]
        if tag =='Var' or tag == 'Const':
            var_parser(i)

        elif tag == 'Function': 
            func_parser(i)

        elif tag == 'RecFunction':
            func_parser(i)

        # AUTO
        elif tag == 'EqSp':
            make_support_map(i)
            # support_map = {'SPMin': 'SPKeys', 'SPMax': 'SPKeys','SPBST': 'SPKeys'}
        elif tag == 'Program':
            # AUTO create recrsive definitions for the first time at this point
            # as well as instantiate lemmas for the first time
            # recfunc_update -
            for name in recdefdict:
                if name in support_map2.keys():
                    pass
                else:
                    interpret_recdef(recdefdict[name]['description'])
            snapshot('for_lemmas')
            instantiate_lemma(prove =True)

            store_inputvars(i)
            
        elif tag == 'Pre':

            # MODES
            if mode == testing_mode:
                tracked_vars = tracked_vars.union(get_loc_vars_in_formula(i[1]))

            precond = interpret_ops(i[1])
            alloc_set = support(i[1])
            transform.append(precond)
            snapshot('initial')

            if mode == testing_mode:
                add_instantiation_pairs_init('initial')

        elif tag[-4:] == 'Post':
            if len(tag[:-4]) == 0:
                rp = 0
            elif tag[:-4] == 'Relaxed':
                rp = 1
            elif tag[:-4] == 'Supportless':
                rp = 2
            else:
                raise Exception ('Bad Post condition Tag')
            
            # MODES
            final_frame = has_mutated
            if final_frame == 1:
                recfunc_update()
                instantiate_lemma()
                has_mutated = 0
            postcond = interpret_ops(i[1])
            sp_postcond = support(i[1])
            snapshot('final')
            if final_frame == 0:
                add_instantiation_pairs('final', False) 

        elif tag == 'RecDef':
            if not(len(i) == 3): 
                raise Exception('Invalid number of arguments to RecDef')
            name = i[1][0]
            if name in recdefdict:
                type_of_inputs = recdefdict[name]['input_type']
                no_of_inputs = recdefdict[name]['no_inputs']
                the_map = {}

                for j in range(1, len(i[1])):   # i[1] = [name, arg1, arg2, ...]
                    if isinstance(i[1][j],str):
                        x = i[1][j]
                    else:
                        x = i[1][j][0]
                    the_map[x] = 'free_'+type_of_inputs+str(j-1)
                recdefdict[name]['description']  = replace_var(the_map, i)

                new_i = recdefdict[name]['description']
                spname = 'SP'+new_i[1][0]
                if spname in support_map2.keys():
                    pass                        
                else:
                    inputs = new_i[1][1:]
                    spbody = ['Sp', new_i[2]]
                    sp_description = [tag, [spname]+inputs, spbody]
                    recdefdict[spname]['description'] = sp_description          
            else:
                raise Exception('Bad RecDef %s' %name)
            
            
        elif tag == 'lemma':
            operands = i[1:]
            if len(operands) == 2:
                lemma_description.append(operands)

            else:
                raise Exception(f' Wrong number of arguments for lemma {i}')


        elif tag == 'assume':
            transform.append(interpret_assume(i))  # remove tags inside interpretops TODO???

        elif tag == 'assign':
            to_append = interpret_assign(i, check_side_conditions)
            if to_append == None:   #?!
                pass
            else:
                transform.append(to_append)
        elif tag == 'free':
            interpret_free(i, check_side_conditions)
        elif tag == 'alloc':
            transform.append(interpret_alloc(i))
        elif tag == 'call':
            transform.append(function_call(i, check_side_conditions))
        elif tag == ':side-conditions':
            check_side_conditions = side_conditions_update(i) 

        else:        
            raise Exception (f'Invalid tag in code {i}')

    if  final_frame == 1:
        if number_of_function_calls == 0:   # frame_rules are added when a call is seen
            frame_rule('initial','final')
        else:

            frame_rule('after_call_'+str(number_of_function_calls),'final')

    print('done preprocessing and checking side-conditions')
    end = time.time()
    print('Time elapsed:', end-start)
    print('checking validity...')
    # print(instantiation_pairs)


    if weaken_alloc_check != 0:
        rp = weaken_alloc_check
 
    if rp == 0:
        ret = cl_check(np_solver,lemma_set,transform,And(postcond,sp_postcond == alloc_set), True)
    elif rp == 1:
        ret = cl_check(np_solver,lemma_set,transform, And(postcond, IsSubset(sp_postcond,alloc_set)), True)
    elif rp == 2:
        ret = cl_check(np_solver,lemma_set,transform,postcond, True)
    else:
        raise Exception ('No postcondition given')
    global number_of_vcs
    print('---------------')
    print('Number of VCs generated for BB:', number_of_vcs)
    print('---------------')

    if ret == True:
        print('goal is valid')
    else:
        print('goal not proven')
    end = time.time()
    print('Time elapsed:', end-start)


