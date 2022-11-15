"""
myparser.py in the vcgen folder contains a vc generator. The input is to be given as a list of strings, each string roughly corresponds to a line in the program to be
verified. It is possible to just write the program as in a text file and read it. Then apply the method 'vc' (import it from myparser.py) onto the result. 
The file should look like this:

(Const nil Loc)
(Var x Loc)
(Var var1 Loc)
(Function next Loc Loc)
(RecFunction list Loc Bool)
(RecFunction SPlist Loc SetLoc)
(RecDef (SPlist var1) (ite (= var1 nil) EmptySet (SetAdd (SPlist (next var1)) var1)))
(RecDef (list var1) (ite (= var1 nil) True (and (not (IsSubset (SetAdd EmptySet var1) (SPlist (next var1)))) (list (next var1)))) )
(Pre (list x))
(assume (!= x nil))
(assign x (. x next))
(Post True)

The ordering here is important. Variables and functions should be declared before they are used, and functions (and recursive functions) should be declared before defining/calling
them. 'Pre' gives the precondition. The lines that follow is the body of the program, which allows for assume and assign satements. It is possible to use multiple
operations when making assumes (see the list below for what all is allowed). 'Post' gives the post condition. 

Constants, Variables are declared in the form

(Const name type)                                                   # type can be Loc, SetLoc, Int, SetInt, Bool
(Var name type)



Functions/Recursive functions are declared in the form

(Function name type type    ....)                                                               #At least 2 types must be given
(RecFunction name type type ....)

NOTE: For any recursive function, the corresponding support must also be defined in the form SPname. Creating supports is not automated yet.


Recursive definitions are defined in the form

(RecDef (name variable1 variable2 ...) = function_definition_using_variable1_vairable2...._ )   #The definition has the format given in the list below

The general form ('operator' operand 1 operand 2 ... ). The following list has what all is allowed, followed by what it does.
See the following list as a grammar.
 x,y,z are variables or constants.

X,Y,Z = 
(1)      x ->    x                      ,                True -> True               ,           False -> False   
(2)  (func x..)                         -> func(x ..) 
(2)  (not X)                           -> Not(X)
(3)  (imp X Y)                         -> Implies(X,Y)
(4)  (= X Y)                           -> X==Y
(5)  (!= X Y)                          -> Not(X==Y)
(6)  (ite X Y Z)                       -> If X then Y else Z
(7)  (and X Y X...)                    -> And(X,Y,Z,...)
(8)  (or X Y Z...)                     -> Or(X,Y,Z,...)
(9) (IsSubset set1 set2)              -> Check if set1 is a subset of set2
(10) (IsEmpty set1)                     -> Check if set1 is empty


set1,set2 = 
(11) (SetAdd set1 x y ...)              -> set1 U {x,y,...}
(12) (Union set1 set2)                 -> set1 U set2
(13) (Intersect set1 set2)             -> set1 intersection set2

(14)  (assume X)                        -> X


(15) (. x func)                        -> func(x)      #application
(16) (assign p q)                      -> p:=q         #assignment, where p is a variable or (15), and q is a variable/constant or (15)

(17) (RecDef (func x..) (def_of_func)) -> AddRecDef(func, x..., def_of_func(x..)) #define recursive function, where def_of_func is using X.


Once the text file with the program to be verified is created(see swaptwo.txt), just read the file. Store this in, say lines_of_code. Then do vc(lines_of_code). (see textvc.py).
"""
