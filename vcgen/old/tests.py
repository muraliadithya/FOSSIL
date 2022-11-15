import pyparsing as pp

from vcgen.parser import Program
from vcgen.parser import vardict, funcdict, recdefdict


ProgramText = pp.original_text_for(Program)

# Use this command to read the input from a file
filename = 'tests/example.fsl'
for parse_elem in ProgramText.parse_file(filename):
    print(parse_elem)

print('\nParsing Successful!\n')


# You can also make a string within python and use parse_string instead of parse_file
# pgm = """
# // General format of the input: Declarations, followed by recursive definitions, followed by pre, program, and post.
# // This is how you write single line comments
# /* This is how you write
#  multiline comments */
#
# Var x Loc
# Var y Loc
# // This is how you declare constants. Be sure to distinguish them during declaration by using 'Const'.
# Const nil Loc
#
# // You should distinguish normal functions and recursive functions in the syntax
# Function next Loc Loc
# Function prev Loc Loc
# RecFunction list Loc Bool
# RecFunction SPlist Loc SetLoc
# RecFunction dlist Loc Bool
# RecFunction SPdlist Loc SetLoc
#
# /* Recursive definitions must always be defined with supports.
# The support of a recursive function <name> is of the form SP<name>.
# The creation of these support functions is not automatic yet. */
#
# Def list(x) := (If (x == nil) Then True Else list(next(x)))
# Def SPlist(x) := (If (x == nil) Then empSetLoc Else (x | SPlist(next(x))))
#
# Def dlist(x) := (If (x == nil) Then True Else ((next(prev(x)) == x) & dlist(next(x))))
# Def SPdlist(x) := (If (x == nil) Then empSetLoc Else (x | SPdlist(next(x))))
#
# // Only one precondition or postcondition can be defined at the moment.
# @pre: dlist(x)
#
# // There are only two kinds of statements: assume statements and assignment statements
# assume (x != nil)
# assume (x.next != nil)
# x.next.next := x.next
#
# @post: list(x)
# """
#
# for parse_elem in ProgramText.parse_string(pgm):
#     print(parse_elem)
#
# # These represent states of the program at the end of parsing. Not correct yet since
# # actions have not been implemented for program statements
# print(vardict)
# print(funcdict)
# print(recdefdict)
